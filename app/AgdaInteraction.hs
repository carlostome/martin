module AgdaInteraction where

import qualified Agda.Interaction.Imports                   as Interaction
import qualified Agda.Interaction.MakeCase                  as Interaction
import qualified Agda.Interaction.Options                   as Interaction
import qualified Agda.Main                                  as Agda
import qualified Agda.Syntax.Abstract                       as A
import           Agda.Syntax.Abstract.Pretty
import qualified Agda.Syntax.Common                         as Agda
import qualified Agda.Syntax.Common                         as Agda
import qualified Agda.Syntax.Concrete                       as Agda
import qualified Agda.Syntax.Fixity                         as Agda
import qualified Agda.Syntax.Literal                        as Agda
import qualified Agda.Syntax.Parser                         as Agda
import qualified Agda.Syntax.Position                       as Agda
import qualified Agda.Syntax.Translation.ConcreteToAbstract as Agda
import qualified Agda.TheTypeChecker                        as Agda
import qualified Agda.TypeChecking.Errors                   as Agda
import qualified Agda.TypeChecking.Monad                    as TCMonad
import qualified Agda.Utils.FileName                        as Agda

import           Control.Monad.IO.Class
import           Data.Foldable
import qualified Data.HashMap.Strict                        as HMS
import qualified Data.List                                  as List
import qualified Data.Map.Strict                            as MS
import           Text.Printf

-- interaction test
itest :: FilePath -> IO ()
itest path = do
  printf "Starting tutor with %s\n" path
  absPath <- Agda.absolute path
  --  moduleSrc <- Agda.parseFile' Agda.moduleParser (Agda.mkAbsolute $ agdaFile opts)
  -- REMARK: the code below seems to be the "standard way" of performing type checking in an interactive setting
  Agda.runTCMPrettyErrors $ do
    -- initialize interactive state
    TCMonad.resetState
    TCMonad.setCommandLineOptions Interaction.defaultOptions
    -- type check file
    (iface, warnings) <- Interaction.typeCheckMain absPath
    case warnings of
      Interaction.NoWarnings     -> return ()
      -- TODO: print warnings (or not), most likely just stuff about unresolved meta variables
      Interaction.SomeWarnings w -> return ()

    liftIO $ do
      print iface
      printf "\n\n"
    
    -- print a list of declarations (the Interface seems to be abstract syntax)
    liftIO $ forM_ (HMS.toList $ TCMonad._sigDefinitions (TCMonad.iSignature iface)) $ \(k,v) ->
      printf "%s : %s\n\n" (show k) (show $ TCMonad.defType v)

    TCMonad.getInteractionIdsAndMetas >>= liftIO . print

    foo <- Interaction.makeCase (Agda.InteractionId 0) Agda.noRange "xs"
    liftIO $ printf "Split!\n\n"
--    Interaction.getInterface'
    liftIO $ print foo
    TCMonad.getInteractionMetas >>= liftIO . print
  printf "Done!"

