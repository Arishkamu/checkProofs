{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

module Main where

import GHC
    ( Id,
      compileToCoreModule,
      runGhc,
      setSessionDynFlags,
      getSessionDynFlags,
      CoreModule(..),
      HscEnv,
      GeneralFlag(..),
      GhcMonad(..),
      NamedThing(..),
      Module, Name, guessTarget, setTargets, depanal, mgModSummaries, parseModule, typecheckModule, desugarModule, DesugaredModule (dm_core_module), LoadHowMuch (LoadAllTargets), load, coreModule, addTarget, setTargets)
import GHC.Paths (libdir)
import GHC.Core
import GHC.Core.Map.Type (DeBruijn(..), deBruijnize, extendCMEs)
import GHC.Core.Make (mkCoreApps) -- maybe mkApps
import GHC.Driver.DynFlags ( gopt_set )
import GHC.Driver.Env ( mainModIs, hsc_HUE, HscEnv(..) )
import GHC.Types.Literal (Literal(..))
import GHC.Types.Name.Occurrence (occNameString)
import GHC.Types.Basic (Activation(..))
-- Subst
import GHC.Core.Subst (extendSubst, mkEmptySubst, substExpr)
import GHC.Core.FVs (exprFreeVars, ruleRhsFreeVars)
import GHC.Types.Var.Env (mkInScopeSet, extendInScopeSetSet)
import GHC.Types.Var.Set (delVarSet, emptyDVarSet)
import GHC.Data.FastString (mkFastString)
import GHC.Types.Unique.Set (addListToUniqSet, unionUniqSets)

import Control.Monad.State.Lazy ( runStateT, liftIO, gets, modify )
import Control.Monad.Except ( runExceptT, MonadError(..) )
import Control.Applicative ((<|>))
import Data.Generics.Uniplate.Data (universe)
import qualified Data.ByteString.Char8 as BS8
import Data.Functor ( (<&>) )
import Data.List (isPrefixOf, partition, find)
import Data.Bifunctor (bimap)

-- Simplifier
import GHC.Unit.External (initExternalUnitCache, eucEPS, ExternalPackageState(..))
import GHC.Driver.Config.Core.Opt.Simplify (initSimplifyExprOpts)
import GHC.Core.FamInstEnv (extendFamInstEnvList, emptyFamInstEnv)
import GHC.Core.Opt.Simplify (SimplifyExprOpts(..))
import GHC.Core.Stats (exprSize)
import GHC.Core.Opt.Simplify.Monad (initSmpl)
import GHC.Core.Opt.Simplify.Iteration (simplExpr)

-- DEBUG
import GHC.Utils.Outputable ( ppr, showSDocUnsafe )
import GHC.Types.Id ( modifyIdInfo, idInfo, Var, idDetails, isDFunId, isClassOpId_maybe, idUnfolding)
import GHC.Types.Id.Info
import GHC.Core.Class
import GHC.Core.Rules ( addLocalRules, emptyRuleEnv, mkRule, updExternalPackageRules, lookupRule, roughTopNames, matchExprs )
import GHC.Core.Opt.Simplify.Env ( getInScope, mkSimplEnv, setInScopeSet, pprSimplEnv, seRuleOpts, SimplEnv (seMode) )
import GHC.Types.Id.Info ( RuleInfo(..), setRuleInfo, IdInfo (ruleInfo), ruleInfoRules )
import GHC.Core.InstEnv 

import AstInfo
import PrettyString
import ProofBase
import SortDecls ( sorteDeclConvrs )
import GHC.Core.Opt.Simplify.Utils
import GHC.Core.SimpleOpt ( defaultSimpleOpts, simpleOptExpr, SimpleOpts(..) )
import GHC.Core.Utils
import GHC.Types.Tickish
import GHC.Plugins hiding (L, getModule)
--  (ModGuts(..), getUnique)
import GHC.Core.Opt.OccurAnal


main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags' <- getSessionDynFlags
    let dflags = gopt_set dflags' Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags
    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/ExampleInst-fails.hs"
    let filePath_base = "/Users/arina/hse/nir/moskvinPrj/checkProofs/src/ProofBase.hs"
    -- coreMod <- compileToCoreModule filePath
    -- -- liftIO $ putStrLn $ (showSDocUnsafe (ppr coreMod))

    target1 <- guessTarget filePath Nothing Nothing
    target2 <- guessTarget filePath_base Nothing Nothing
    -- addTarget target2
    setTargets [target1, target2]
    _ <- load LoadAllTargets
    -- coreMod <- compileToCoreModule filePath

    modGraph <- depanal [] False
    let ms1 = mgModSummaries modGraph !! 0
    let ms2 = mgModSummaries modGraph !! 1

    desugared <- parseModule ms1 >>= typecheckModule >>= desugarModule
    let mg1 = dm_core_module desugared

    desugared2 <- parseModule ms2 >>= typecheckModule >>= desugarModule
    let mg2 = dm_core_module desugared2

    liftIO $ putStrLn "\n=== Imported Func ===\n"
    -- liftIO $ putStrLn (showSDocUnsafe $ ppr $ (mg_binds mg1))
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ [ nameModule (idName nam) | (x, y) <- flattenBinds (mg_binds mg1), (Var nam) <- universe y, "importThisFunc" <- [getStrById nam]]
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ [ nameModule (idName nam) | (x, y) <- flattenBinds (mg_binds mg1), (Var nam) <- universe y, "importThisFuncHiding" <- [getStrById nam]]

    liftIO $ putStrLn "\n===== The End: App/Main ====="

getStrById :: Id -> String
getStrById v = occNameString (getOccName v)