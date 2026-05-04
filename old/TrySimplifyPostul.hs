{-# LANGUAGE RecordWildCards, FlexibleContexts#-}

module Main where

import GHC
import GHC.Paths (libdir)
import GHC.Core
import GHC.Core.Subst (extendSubst, mkEmptySubst, substExpr)
import GHC.Core.FVs (exprFreeVars)
import GHC.Core.Map.Type (DeBruijn(..), deBruijnize)
import GHC.Types.Name.Occurrence (occNameString)
-- import GHC.Types.Name (getOccName)
import GHC.Types.Literal (Literal(..))
import GHC.Types.Var.Env (mkInScopeSet, extendInScopeSetSet)
import GHC.Types.Var.Set (delVarSet)
import GHC.Types.Id
import GHC.Unit.Module.ModGuts
import GHC.Core.Rules
import GHC.Data.FastString
import GHC.Types.Basic
import GHC.Data.EnumSet
import GHC.Driver.DynFlags

import Control.Monad.IO.Class (liftIO)
import Data.Generics.Uniplate.Data (universe)
import qualified Data.ByteString.Char8 as BS8

-- Simplifier
import GHC.Unit.External (initExternalUnitCache, eucEPS, ExternalPackageState(..))
import GHC.Driver.Config.Core.Opt.Simplify (initSimplifyExprOpts)
import GHC.Driver.Env (HscEnv(..))
import GHC.Core.FamInstEnv (extendFamInstEnvList, emptyFamInstEnv)
import GHC.Core.Opt.Simplify (SimplifyExprOpts(..))
import GHC.Core.Opt.Simplify.Env (mkSimplEnv, getInScope, setInScopeSet)
import GHC.Core.Rules (updExternalPackageRules, emptyRuleEnv)
import GHC.Core.Stats (exprSize)
import GHC.Core.Opt.Simplify.Monad (initSmpl)
import GHC.Core.Opt.Simplify.Iteration (simplExpr)

import GHC.Utils.Outputable
import Data.List (intercalate)


{-
  TWO STEPS
    match all variables from expr_o to expr_l (expr_l==expr_o)
    subst all variables into expr_r
-}

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags0 <- getSessionDynFlags
    let dflags = gopt_set dflags0 Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags

    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/TrySimplifyPostulExample.hs"
    coreMod <- compileToCoreModule filePath

    target <- guessTarget filePath Nothing Nothing
    setTargets [target]
    modGraph <- depanal [] False
    let ms = head $ mgModSummaries modGraph

    parsed <- parseModule ms
    typed <- typecheckModule parsed
    desugared <- desugarModule typed
    let mg = dm_core_module desugared

    let m1Rule = head $ drop 1 $ mg_rules mg ++ concatMap collectIdRules (cm_binds coreMod)
    liftIO $ putStrLn (showSDocUnsafe (ppr m1Rule))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_name m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_act m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_fn m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_rough m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_bndrs m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_args m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_rhs m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_auto m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_origin m1Rule)))

    liftIO $ putStrLn "-----------"


    let 
      coreBinds  = flattenBinds (cm_binds coreMod)
      postulates = [ (f_id, l_postl, r_postl) |
        (f_id, f_expr) <- coreBinds,
        (App (App (App (Var app_id) _) l_postl) r_postl) <- universe f_expr,
        "postulate" <- [getStrById app_id] ]
      postulM1@(postulM1_id, l_postl, r_postl) = head postulates
      postulM1FuncBody = (case lookup postulM1_id coreBinds of
        Just func_body -> func_body
        Nothing        -> error $ "Function definition not found for:\n" ++ (showSDocUnsafe (ppr postulM1_id)))
      (fn_rule, fn_args) = collectArgs l_postl
      fn_binds = (\(Lam x1 (Lam x2 (Lam x3 (Lam x4 (Lam x5 (Lam x6 _)))))) -> [x1, x2, x3, x4, x5, x6]) postulM1FuncBody 
      fn_name = (\(Var x) -> getName x) fn_rule
      fn_id = (\(Var x) -> x) fn_rule

    liftIO $ putStrLn (showSDocUnsafe (ppr fn_name))
    liftIO $ putStrLn (showSDocUnsafe (ppr fn_binds))
    liftIO $ putStrLn (showSDocUnsafe (ppr fn_args))
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1))
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1_id))
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1FuncBody))

    let new_rule = mkRule (mg_module mg) False True (mkFastString "my-new-rule") AlwaysActive fn_name fn_binds fn_args r_postl
      
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr m1Rule))
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr new_rule))

    let 
      (_, bindExpr0) = head $ filter (\(x, _) -> getStrById x == "myCoreExpr2") coreBinds
      bindExpr = (\(Lam _ (Lam _ (Lam _ (Lam _ (Lam _ (Lam _ x)))))) -> x) bindExpr0 
      

    liftIO $ putStrLn (showSDocUnsafe (ppr bindExpr0))
    liftIO $ putStrLn "============ WAS       ============"
    liftIO $ putStrLn (showSDocUnsafe (ppr bindExpr))
    liftIO $ putStrLn "============ Rule Auto ============"
    liftIO $ printMy session m1Rule [bindExpr]
    liftIO $ putStrLn "============ Rule My   ============"
    liftIO $ printMy session new_rule [bindExpr]

    let genFlags = toList $ generalFlags dflags
    liftIO $ print $ gopt Opt_EnableRewriteRules dflags
    -- let dflags2 = gopt_set dflags Opt_EnableRewriteRules

    -- let
    --   rule_opts =
    --   in_scope_set = mkInScopeSet $ exprFreeVars bindExpr 
    -- let ruleLookup = lookupRule opts (\_ -> True) fn_id fn_args [m1Rule]
    -- case ruleLookup of
    --   Just (_, new_expr) -> liftIO $ putStrLn (showSDocUnsafe (ppr new_expr))
    --   Nothing -> liftIO $ putStrLn "Nothing"

      -- rule = mkRule
      --   (mkFastString "my-left-identity")
      --   AlwaysActive
      --   [aVar, kVar]
      --   (idName bindId)
      --   [ App (Var returnId) (Var aVar)
      --   , Var kVar
      --   ]
      --   rhs

    -- TODO: collectModule no dif just yet
    -- liftIO $ putStrLn "\n=== Core cm_types ===\n"
    -- liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_types coreMod)
    -- let astInfo = collectModule coreMod
    -- liftIO $ putStrLn "\n===== Collected AstInfo =====\n"
    -- liftIO $ putStrLn $ prettyPrint astInfo
    -- liftIO $ putStrLn "\n===== End AstInfo =====\n"
    -- let result = analyzeConversions astInfo
    -- case result of
    --   Left err -> liftIO $ putStrLn $ "Error: " ++ err
    --   Right convrs -> do
    --     liftIO $ putStrLn "\n=== Simplify Analysis ===\n"
    --     liftIO $ printMy session convrs
        -- liftIO $ putStrLn "\n=== End ===\n"
        -- mapM_ (\(e1, e2) -> (liftIO (simplifyFunc session e1), e2)) convrs
        -- liftIO $ putStrLn $ map prettyPrintEqPairs $ map (\(e1, e2) -> (inlineLets e1, e2)) m


    liftIO $ putStrLn "\n===== The End: App/Main ====="

collectIdRules :: CoreBind -> [CoreRule]
collectIdRules bind =
  case bind of
    NonRec b _ -> idCoreRules b
    Rec pairs  -> concatMap (idCoreRules . fst) pairs

getStrById :: Id -> String
getStrById v = occNameString (getOccName v)



printMy :: HscEnv -> CoreRule -> [CoreExpr] -> IO ()
printMy ses rule exprs = 
  do
    res <- mapM (printMyPair ses rule) exprs
    putStrLn $ intercalate "\n" $ map (showSDocUnsafe . ppr) res

printMyPair :: HscEnv -> CoreRule -> CoreExpr -> IO CoreExpr
printMyPair ses rule x = 
  do
    x1 <- simplifyFunc ses rule x
    -- let x2 = inlineLets x1
    return x1

-- inlineLets :: CoreExpr -> CoreExpr
-- inlineLets expr =
--   case expr of
--     Let (NonRec b rhs) body ->
--       inlineLets (easySubstFunc body b rhs)

--     App f x ->
--       App (inlineLets f) (inlineLets x)

--     Lam b e ->
--       Lam b (inlineLets e)

--     _ -> expr



simplifyFunc :: HscEnv -> CoreRule -> CoreExpr -> IO CoreExpr
simplifyFunc hscEnv rule expr = do
  euc <- initExternalUnitCache
  let dflags = hsc_dflags hscEnv
  let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)
  let logger = hsc_logger hscEnv

  eps <- eucEPS euc
  let fam_envs =  ( eps_fam_inst_env eps
                  , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                  )

      simpl_env = mkSimplEnv (se_mode opts) fam_envs
      my_in_scope = (getInScope simpl_env) `extendInScopeSetSet` (exprFreeVars expr)
      my_env = setInScopeSet simpl_env my_in_scope
      -- my_env_two = GHC.Core.Opt.Simplify.Env.extendIdSubst my_env fnId (mkContEx my_env fnBody)
      -- delOneVSet = delOneFromUniqSet (exprFreeVars expr) fnId
      -- my_env_two = setInScopeSet my_env $ (getInScope my_env) `extendInScopeSetSet` delOneVSet
      
      top_env_cfg = se_top_env_cfg opts
      read_eps_rules = eps_rule_base <$> eucEPS euc
      read_ruleenv = updExternalPackageRules emptyRuleEnv <$> read_eps_rules
      my_rule_env  = (\a -> addLocalRules a [rule]) <$> read_ruleenv

  let sz = exprSize expr
  (expr', counts) <- initSmpl logger my_rule_env top_env_cfg sz $
                        simplExpr my_env expr
  return expr'
