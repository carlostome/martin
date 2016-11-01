{-# LANGUAGE TemplateHaskell #-}
{-| This module contains the functionality required for initializing an Agda session.
-}
module Martin.Agda.Init
  ( parseAgdaFile
  , initAgda
  , importAllAbstract
  , AgdaOptions (..)
  , defaultAgdaOptions
  , agdaOptVerbosity
  , agdaOptIncludePaths
  ) where

import qualified Agda.Interaction.BasicOps                  as B
import           Agda.Interaction.FindFile
import           Agda.Interaction.Imports
import           Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses            as Lens
import qualified Agda.Syntax.Abstract                       as A
import qualified Agda.Syntax.Abstract.Views                 as A
import           Agda.Syntax.Common
import qualified Agda.Syntax.Concrete                       as C
import           Agda.Syntax.Info                           as I
import           Agda.Syntax.Parser
import           Agda.Syntax.Position
import           Agda.Syntax.Scope.Base
import           Agda.Syntax.Scope.Monad                    as Scope
import           Agda.Syntax.Translation.AbstractToConcrete
import           Agda.Syntax.Translation.ConcreteToAbstract
import           Agda.TypeChecking.Monad
import           Agda.Utils.FileName
import           Agda.Utils.Monad                           hiding (ifM)
import qualified Agda.Utils.Trie                            as Trie

import Control.Lens
import           Control.Arrow                              ((&&&))
import           Control.Monad.Except
import           Control.Monad.State.Strict
import           Control.Monad.Writer
import           Data.Generics.Geniplate
import qualified Data.Map.Strict                            as Map
import qualified Data.Set                                   as Set
import           System.FilePath                            ((</>))

-- | Some additional options that can be passed to Agda.
data AgdaOptions = AgdaOptions
  { _agdaOptVerbosity    :: Int
  , _agdaOptIncludePaths :: [FilePath]
  }

makeLenses ''AgdaOptions

defaultAgdaOptions :: AgdaOptions
defaultAgdaOptions = AgdaOptions 0 []

-- | This initializes the TCM state just enough to get everything started.
-- For now, it uses the default options and loads Agda's Level primitives.
initAgda :: AgdaOptions -> TCM TCState
initAgda opts = do
  -- initialize interactive state
  resetAllState
  setCommandLineOptions defaultOptions
    { optPragmaOptions = (optPragmaOptions defaultOptions)
      { optVerbose = Trie.singleton [] (view agdaOptVerbosity opts) }
    }
  -- set include path
  absIncl <- liftIO $ mapM absolute (view agdaOptIncludePaths opts)
  Lens.modifyAbsoluteIncludePaths (++ absIncl)
  -- ==================== BEGIN CODE FROM AGDA SOURCE
  libdir <- liftIO defaultLibDir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  _ <- bracket_ (gets Lens.getSafeMode) Lens.putSafeMode $ do
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

-- | Parse an Agda file to concrete syntax.
parseAgdaFile :: FilePath -> IO (AbsolutePath, [C.Declaration])
parseAgdaFile path = do
  absPath <- absolute path
  (_, module') <- parseFile' moduleParser absPath
  return (absPath, module')

-- | Imports a module from an abstract syntax tree.
importModuleAbstract :: I.ModuleInfo -> C.QName -> TCM ()
importModuleAbstract minfo x = setCurrentRange (getRange minfo) $ do
  let dir  = maybe defaultImportDir id $ minfoDirective minfo
      r    = getRange minfo
  -- First scope check the imported module and return its name and
  -- interface. This is done with that module as the top-level module.
  -- This is quite subtle. We rely on the fact that when setting the
  -- top-level module and generating a fresh module name, the generated
  -- name will be exactly the same as the name generated when checking
  -- the imported module.
  (m, i) <- Scope.withCurrentModule A.noModuleName $ withTopLevelModule x $ do
    m <- toAbstract $ NewModuleQName x
    (m, i) <- scopeCheckImport m
    -- We don't want the top scope of the imported module (things happening
    -- before the module declaration)
    return (m, Map.delete A.noModuleName i)

  -- Merge the imported scopes with the current scopes
  modifyScopes $ \ ms -> Map.unionWith mergeScope (Map.delete m ms) i

  -- Bind the desired module name to the right abstract name.
  bindQModule PrivateAccess x m

  void $ openModule_ x dir
  return ()

-- | Scans the abstract syntax for import statements and imports the referenced modules.
importAllAbstract :: [A.Declaration] -> TCM ()
importAllAbstract decls = forM_ (concatMap universeBi decls) go where
  go (A.Import minfo x _) = abstractToConcrete_ x >>= importModuleAbstract minfo
  go _ = pure ()
