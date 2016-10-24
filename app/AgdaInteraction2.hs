{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module AgdaInteraction2 where

import qualified Agda.Interaction.BasicOps                  as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.InteractionTop
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses            as Lens
import           Agda.Main
import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Abstract.Pretty
import           Agda.Syntax.Common
import           Agda.Syntax.Info
import           Agda.Syntax.Concrete
import           Agda.Syntax.Fixity
import           Agda.Syntax.Literal
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Translation.AbstractToConcrete
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TheTypeChecker
import           Agda.TypeChecking.Monad
import           Agda.TypeChecking.Errors
import           Agda.Utils.FileName
import           Agda.Utils.FileName
import           Agda.Utils.Hash
import           Agda.Utils.IO.Binary
import           Agda.Utils.Lens
import           Agda.Utils.Monad
import           Agda.Utils.Null
import           Agda.Utils.Pretty
import           Agda.Utils.Time
import qualified Agda.Utils.Trie                            as Trie

import           ProofSearch

import           Control.DeepSeq
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import Control.Monad.Reader
import qualified Data.List                                  as List
import           System.FilePath                            ((</>))
import Text.Printf

-- | An exercise is just an Agda file, represented by the declarations inside it.
-- INVARIANT: this state needs to be kept in sync with the TCM state.
-- To prevent headaches, only modify the list of declarations (aka the user program)
-- when the changes have been type checked and the TCM state has been populated with
-- the declarations.
data ExerciseState = ExerciseState
  { exerciseDecls :: [A.Declaration]
  }

-- | Environment for exercise computation.
data ExerciseEnv = ExerciseEnv
  { exerciseFile :: AbsolutePath
  , exerciseVerbosity :: Int
  , exerciseInitialAgdaState :: TCState
  }

-- | I'm sorry for another Monad stack, but somewhere we need to keep track of
-- information related to the exercise session.
type ExerciseM = ReaderT ExerciseEnv (StateT ExerciseState TCM)

-- * Interfacing with User

-- | Runs an interactive user session, loading the given exercise
-- This should be the main entry point for everything having to do with Agda.
runInteractiveSession :: Int -> FilePath -> IO ()
runInteractiveSession verbosity agdaFile = do
  -- load the Agda file
  absPath <- absolute agdaFile
  (pragmas, concreteDecls) <- parseFile' moduleParser absPath
  -- TODO: inject pragmas
  ret <- runTCMPrettyNoExit $ local (\e -> e { envCurrentPath = Just absPath }) $ do
    -- load Level primitives and setup TCM state
    initialState <- initAgda verbosity -- the number is the verbosity level, useful for debugging
    -- REMARK: initialState should now contain a snapshot of an initialized Agda session and can be used to quickly
    -- revert when we need to recheck the exercise code.
    
    -- convert exercise to abstract syntax
    abstractDecls <- toAbstract concreteDecls

    -- check that the exercise is valid to begin with
    checkDecls abstractDecls
    unfreezeMetas -- IMPORTANT: if metas are not unfrozen, we cannot refine etc.
    
    -- setup initial state and the environment
    let exState = ExerciseState
          { exerciseDecls = abstractDecls }
        exEnv = ExerciseEnv
          { exerciseFile = absPath
          , exerciseVerbosity = verbosity
          , exerciseInitialAgdaState = initialState
          }
    -- run user session
    st <- execStateT (runReaderT exerciseSession exEnv) exState
    -- if all went well, st contains the solved exercise
    -- TODO: pretty print and send to teacher ;)
    return ()
  -- print errors 
  case ret of
    Left err -> printf "Exercise session failed with\n%s\n" err
    Right _ -> return ()

-- | This is where all the exercise solving should happen
exerciseSession :: ExerciseM ()
exerciseSession = do
  -- REMARK: How a session should be structured:
  -- 1. given the current state of the program, invoke proof search to generate strategy (See module Strategy)
  --    (if it is not possible to solve, tell the user so, in order for him to backtrack)
  -- 2. let the user do stuff
  --    * if the user follows the strategy, just refine or split and return to 2
  --    * if the user diverts from the strategy, go to 1, or undo step
  -- 3. no holes left -> user happy

  -- THIS IS JUST AN INTERACTIVE LOOP ALLOWING TO EITHER REFINE OR SPLIT HOLES, TO SEE WHETHER IT'S ACTUALLY WORKING
  forever $ do
    showProgramToUser
    liftIO $ putStrLn "InteractionID:"
    ii <- InteractionId <$> liftIO readLn
    liftIO $ putStrLn "Action:"
    act <- liftIO $ getLine
    case act of
      ('r':' ':ref) -> do
        -- parse the user input in the given context
        given <- tcmToEx $ B.parseExprIn ii noRange ref
        liftIO $ print given
        -- try to refine the hole with the user expression
        expr <- tcmToEx $ fmap Just (B.refine ii Nothing given) `catchError` \err -> do
          str <- prettyError err
          liftIO $ putStrLn str
          return Nothing
        liftIO $ printf "done refining\n"
        -- if successful, actually replace that part of the AST
        case expr of
          Just repl -> do
            -- replace hole in AST
            curprog <- gets exerciseDecls
            let newprog = flip A.mapExpr curprog $ \e -> case e of
                  A.QuestionMark _ iiq
                    | iiq == ii -> repl
                  other -> other
            -- save current state to be able to recover if it turns out not to type check
            prev <- saveTCState
            resetTCState
            -- rebuild interaction points (normally only created when going from concrete -> abstract)
            newprog' <- rebuildInteractionPoints newprog
            -- check updated AST (should actually always succeed)
            liftIO $ printf "checking AST\n"
            tryIt (tcmToEx $ checkDecls newprog' >> unfreezeMetas)
              (\_ -> do -- success
                  liftIO $ printf "success\n"
                  modify $ \s -> s { exerciseDecls = newprog' }
                  )
              (\_ -> do -- failure
                  liftIO $ printf "failure\n"
                  restoreTCState prev
              )
          Nothing -> return ()
      ('c':' ':var) -> do
        -- TODO split
        return ()
      _ -> liftIO $ putStrLn "try again"

-- | Replaces all question marks with fresh interaction points and registers them with the type checker.
-- This step is necessary after resetting the type checker state.
rebuildInteractionPoints :: A.ExprLike e => e -> ExerciseM e
rebuildInteractionPoints = tcmToEx . A.traverseExpr
              (\e -> case e of
                       A.QuestionMark m ii -> A.QuestionMark m <$> registerInteractionPoint noRange Nothing
                       other -> pure other)


-- | Reverts to a fresh Agda TCM state, forgetting all user definitions and retaining only the primitives
resetTCState :: ExerciseM ()
resetTCState = do
  -- asks exerciseVerbosity >>= void . tcmToEx . initAgda
  asks exerciseInitialAgdaState >>= restoreTCState

tcmToEx :: TCM a -> ExerciseM a
tcmToEx = lift . lift

tryIt :: MonadError e m => m a -> (a -> m b) -> (e -> m b) -> m b
tryIt act success failure = do
  r <- fmap Right act `catchError` \e -> return $ Left e
  either failure success r

saveTCState :: ExerciseM TCState
saveTCState = tcmToEx get

restoreTCState :: TCState -> ExerciseM ()
restoreTCState = tcmToEx . put

-- | Displays the current state of the program to the user.
-- It also shows the numbers (InteractionId) of each hole. Based on that, the user can then
-- choose to perform an action on a given hole.
showProgramToUser :: ExerciseM ()
showProgramToUser = do
    prog <- setMetaNumbersToInteraction <$> gets exerciseDecls
    doc <- tcmToEx $ vcat <$> mapM prettyA prog  -- printDecls prog
    liftIO $ putStrLn $ render doc

refineWithProof :: InteractionId -> Proof -> ExerciseM ()
refineWithProof hole proof = return ()

-- * Interfacing with Agda

-- | In the abstract syntax, sets the 'metaNumber' of 'QuestionMark' to
-- the corresponding interaction ID to have it printed. Seems to be the suggested
-- way according to the documentation for 'QuestionMark'.
-- WARNING: This messes with the internal state of expressions which causes type checking to brake,
-- so only use before pretty printing.
setMetaNumbersToInteraction :: A.ExprLike e => e -> e
setMetaNumbersToInteraction = A.mapExpr go where
  go (A.QuestionMark meta ii) = A.QuestionMark meta { metaNumber = Just $ MetaId $ interactionId ii } ii
  go other = other

-- | Like 'runTCMPrettyErrors', but does not exit the application afterwards
runTCMPrettyNoExit :: TCM a -> IO (Either String a)
runTCMPrettyNoExit tcm = do
  ret <- runTCMTop $ (Right <$> tcm) `catchError` \err -> do
    str <- prettyError err
    return $ Left str
  case ret of
    Left _ -> return $ Left "impossible: this error should have been caught before"
    Right x -> return x

-- | This initializes the TCM state just enough to get everything started.
-- For now, it uses the default options and loads Agda's Level primitives.
initAgda :: Int -> TCM TCState
initAgda verbosity = do
  -- initialize interactive state
  resetAllState
  setCommandLineOptions defaultOptions
    { optPragmaOptions = (optPragmaOptions defaultOptions)
      { optVerbose = Trie.singleton [] verbosity }
    }

  -- ==================== BEGIN CODE FROM AGDA SOURCE
  libdir <- liftIO defaultLibDir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  iface <- bracket_ (gets Lens.getSafeMode) Lens.putSafeMode $ do
    Lens.putSafeMode False
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.
    bracket_ (gets Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0
      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $ do
        primitiveModule <- moduleName $ mkAbsolute $
            libdir </> "prim" </> "Agda" </> "Primitive.agda"
        getInterface_ primitiveModule
  -- ==================== END CODE FROM AGDA SOURCE
  -- return with state right after initialization, to be able to speed up things when we need to reset
  get


-- | Takes a proof and converts it to an abstract expression in the context of the given hole.
proofToAbstractExpr :: InteractionId -> Proof -> TCM A.Expr
proofToAbstractExpr ii proof = B.parseExprIn ii noRange (proofStr proof) where
  proofStr (Proof name args _)
    | List.null args = name
    | otherwise = "(" ++ List.unwords (name : map proofStr args) ++ ")"



-- * Some functions solely used for testing stuff

itest2 :: FilePath -> IO ()
itest2 agdaFile = do
  -- load agda file
  path <- absolute agdaFile
  (pragmas, concreteDecls) <- parseFile' moduleParser path
  -- run TCM computation (inside Agda's type checking monad)
  runTCMPrettyErrors $ do
    -- load primitives like Level etc.
    initialState <- initAgda 0
    -- convert to abstract syntax
    abstractDecls <- toAbstract concreteDecls
    checkDecls abstractDecls
    -- print all interaction metas (i.e. holes in the program)
    getInteractionIdsAndMetas >>= liftIO . print

    -- TEST CODE for map function
    [(inil,mnil), (icons,mcons)] <- getInteractionIdsAndMetas
    forM_ itWorks $ \prf -> do
      liftIO $ print prf
      given <- proofToAbstractExpr icons prf
      pp <- prettyA given
      liftIO $ print $ render pp
    -- END TEST CODE

    -- try restoring the state
    put initialState
    getInteractionIdsAndMetas >>= liftIO . print -- prints [], so restoring actually works

    return ()
