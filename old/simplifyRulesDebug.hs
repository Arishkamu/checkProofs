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
import GHC.Core.Stats ( coreBindsSize, coreBindsStats, exprSize )
import GHC.Core.Opt.Simplify.Monad (initSmpl)
import GHC.Core.Opt.Simplify.Iteration (simplExpr)

import GHC.Utils.Outputable
import Data.List (intercalate)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)

import GHC.Core.Opt.Simplify
import GHC.Core.Opt.Simplify.Env
import GHC.Core.Opt.Simplify.Utils
import GHC.Core.Opt.Simplify.Inline
import GHC.Core.Opt.Simplify.Iteration
import GHC.Utils.Trace
import GHC.Core.Opt.Simplify.Monad
import GHC.Core.Opt.Simplify.Utils
import GHC.Types.Name.Ppr
import GHC.Driver.Config.Core.Opt.Simplify
import GHC.Core.Lint.Interactive
import GHC.Types.Name.Env
import GHC.Utils.Logger
import GHC.Core.Ppr
import GHC.Types.Unique.Set
import GHC.Builtin.Names

{-
  TWO STEPS
    match all variables from expr_o to expr_l (expr_l==expr_o)
    subst all variables into expr_r
-}

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags0 <- getSessionDynFlags
    let dflags = foldl gopt_set dflags0 [Opt_EnableRewriteRules]
    -- let dflags = foldl dopt_set dflags1 [Opt_D_dump_simpl_trace, Opt_D_dump_rule_firings, Opt_D_dump_simpl_iterations, Opt_D_dump_rules, Opt_D_dump_simpl, Opt_D_verbose_core2core, Opt_D_dump_simpl_stats, Opt_D_dump_occur_anal]
    _ <- setSessionDynFlags dflags

    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/TrySimplifyPostulExample.hs"
    coreMod <- compileToCoreModule filePath
    -- liftIO $ putStrLn $ (showSDocUnsafe (ppr coreMod))

    target <- guessTarget filePath Nothing Nothing
    setTargets [target]
    modGraph <- depanal [] False
    let ms = head $ mgModSummaries modGraph

    parsed <- parseModule ms
    typed <- typecheckModule parsed
    desugared <- desugarModule typed
    let mg = dm_core_module desugared

    liftIO $ putStrLn $ "================= MOD-GUT REC BINDS"
    let recBind = head [ re | re@(Rec _) <- (mg_binds mg)]
    liftIO $ putStrLn $ showSDocUnsafe (ppr recBind)
    let (Rec [(recBindB, recBindBody)]) = recBind
    liftIO $ putStrLn "----"
    liftIO $ putStrLn $ showSDocUnsafe (ppr recBindB)
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ idInfo recBindB
    liftIO $ putStrLn "----"
    liftIO $ putStrLn $ showSDocUnsafe (ppr recBindBody)
    liftIO $ putStrLn "----"
    -- liftIO $ putStrLn $ show $ map  recBindInner
    liftIO $ putStrLn "----"
    liftIO $ putStrLn $ showSDocUnsafe (ppr $ flattenBinds [recBind])
    let [(fb, _)] = flattenBinds [recBind]
    liftIO $ putStrLn "----"
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ idInfo fb
    liftIO $ putStrLn $ "================= MOD-GUT RULES"
    liftIO $ putStrLn $ showSDocUnsafe (ppr (mg_rules mg))
    liftIO $ putStrLn $ "========="
    let m1Rule = head $ mg_rules mg ++ concatMap collectIdRules (cm_binds coreMod)
    liftIO $ putStrLn (showSDocUnsafe (ppr m1Rule))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_name m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_act m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_fn m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_rough m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_bndrs m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_args m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_rhs m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_auto m1Rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_local m1Rule)))
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
      fn_binds = fst $ collectBinders postulM1FuncBody 
    liftIO $ putStrLn $ showSDocUnsafe (ppr l_postl)
    let
      fn_name = (\(Var x) -> getName x) fn_rule
      fn_id = (\(Var x) -> x) fn_rule
      fnBody = snd $ head $ (filter (\(x, _) -> x == fn_id) coreBinds) ++ [(fn_id, fn_rule)]
    liftIO $ putStrLn "----------- fnBody"
    liftIO $ putStrLn (showSDocUnsafe (ppr fnBody))

    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr fn_name))
    liftIO $ putStrLn (showSDocUnsafe (ppr fn_binds))
    liftIO $ putStrLn (showSDocUnsafe (ppr fn_args))
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1))
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1_id))
    liftIO $ putStrLn (showSDocUnsafe (ppr postulM1FuncBody))

    let new_rule = mkRule (cm_module coreMod) False True (mkFastString "my-new-rule") AlwaysActive fn_name fn_binds fn_args r_postl
    
    liftIO $ putStrLn "----------- new-rule"
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_rough new_rule)))
    liftIO $ putStrLn (showSDocUnsafe (ppr (ru_bndrs new_rule)))
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr m1Rule))
    liftIO $ putStrLn "-----------"
    liftIO $ putStrLn (showSDocUnsafe (ppr new_rule))

    let 
      (be_id, bindExpr0) = head $ filter (\(x, _) -> getStrById x == "myRuleCheck1") coreBinds
      bindExpr = snd $ collectBinders bindExpr0 
 
    liftIO $ putStrLn "----------- bindExpr0"
    liftIO $ putStrLn (showSDocUnsafe (ppr bindExpr0))
    liftIO $ putStrLn "============ WAS       ============"
    liftIO $ putStrLn (showSDocUnsafe (ppr bindExpr))
    -- liftIO $ putStrLn "============ occurAnalyseExpr       ============"
    -- liftIO $ putStrLn (showSDocUnsafe (ppr (occurAnalyseExpr bindExpr)))
    liftIO $ putStrLn "============ Rule Auto ============"
    liftIO $ printMy session [m1Rule] [bindExpr] fn_id fb
    let (Var beAppId) = fst $ collectArgs bindExpr
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ getUnique (getName beAppId)
    liftIO $ putStrLn "------"
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ idInfo fn_id
    liftIO $ putStrLn "------"
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ idInfo be_id
    liftIO $ putStrLn "------"
    liftIO $ putStrLn $ showSDocUnsafe $ ppr $ idInfo beAppId
    liftIO $ putStrLn "============ Rule My   ============"
    liftIO $ printMy session [new_rule] [bindExpr] fn_id fb 

    liftIO $ putStrLn ""
    ---- EEEEEEEE do only once!!!!!
    liftIO $ putStrLn "============ LOOKUP RULE   ============"
    (ropts, inEnv, actFun, simpl_env) <- liftIO $ simplifyFuncOpts session m1Rule bindExpr
    -- lookupRule  RuleOpts -> InScopeEnv -> (Activation -> Bool) -> Id -> [CoreExpr] -> [CoreRule] -> Maybe (CoreRule, CoreExpr)
    let (Var f_target, args_targetgs) = collectArgs bindExpr
    let (Just (_, lule)) = lookupRule ropts inEnv actFun f_target args_targetgs [m1Rule]
    liftIO $ putStrLn "============ LOOKUP RULE result ============"
    liftIO $ putStrLn (showSDocUnsafe (ppr lule))
    liftIO $ putStrLn "============ LOOKUP RULE after simplify ============"
    -- liftIO $ printMy session [] [lule]
    -- liftIO $ putStrLn ""
    liftIO $ putStrLn "============ DEBUG ============"
    liftIO $ putStrLn $ (showSDocUnsafe (ppr (seMode simpl_env)))
    let (ISE inScopeSet idUnfold) = inEnv
    liftIO $ putStrLn $ (showSDocUnsafe (ppr inScopeSet))
    liftIO $ putStrLn $ (showSDocUnsafe (ppr (idUnfolding f_target)))
    liftIO $ putStrLn $ (showSDocUnsafe (ppr (ruleActivation new_rule)))
    let phase = sm_phase (seMode simpl_env)
    let activation = idInlineActivation f_target
    case activation of
      AlwaysActive -> liftIO $ putStrLn "A"
      ActiveBefore _ _ -> liftIO $ putStrLn "B" 
      ActiveAfter _ _ -> liftIO $ putStrLn "C"
      FinalActive -> liftIO $ putStrLn "D"
      NeverActive -> liftIO $ putStrLn "E" 

    liftIO $ putStrLn $ (showSDocUnsafe (ppr (phase)))
    liftIO $ putStrLn $ (showSDocUnsafe (ppr (isActive phase activation)))
    liftIO $ putStrLn $ (showSDocUnsafe (ppr f_target))
    liftIO $ putStrLn $ (showSDocUnsafe (ppr fn_id))
  
    -- liftIO $ putStrLn "============ SIMPLIFY TOP BIND ============"
    -- let bind = NonRec be_id bindExpr0
    -- liftIO $ simplifyTopBind session [m1Rule] [bind]
    -- liftIO $ putStrLn "============ DEBUG PRG ============"
    -- mg' <- liftIO $ simplifyPrg session [new_rule] mg
    -- let (_, bindExprMG') = head $ filter (\(x, _) -> getStrById x == "myRuleCheck1") (flattenBinds (mg_binds mg'))
    -- liftIO $ putStrLn $ showSDocUnsafe $ ppr bindExprMG'

    -- liftIO $ putStrLn $ show $ maxSimplIterations dflags

    -- activeUnfolding :: SimplMode -> Id -> Bool
-- activeUnfolding mode id
--   | isCompulsoryUnfolding (realIdUnfolding id)
--   = True   -- Even sm_inline can't override compulsory unfoldings
--   | otherwise
--   = isActive (sm_phase mode) (idInlineActivation id)
--   && sm_inline mode
    -- (activeUnfolding (seMode simpl_env) f_target)

    -- let genFlags = toList $ generalFlags dflags
    -- liftIO $ print $ gopt Opt_EnableRewriteRules dflags
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



printMy :: HscEnv -> [CoreRule] -> [CoreExpr] -> Id -> Id -> IO ()
printMy ses rules exprs fnId fbId = 
  do
    res <- mapM (printMyPair ses rules fnId fbId) exprs
    putStrLn $ intercalate "\n" $ map (showSDocUnsafe . ppr) res

printMyPair :: HscEnv -> [CoreRule] -> Id -> Id -> CoreExpr -> IO CoreExpr
printMyPair ses rules fnId fbId x = 
  do
    x1 <- simplifyFunc ses rules x fnId fbId
    let x2 = inlineLets x1
    return x2

inlineLets :: CoreExpr -> CoreExpr
inlineLets expr =
  case expr of
    Let (NonRec b rhs) body ->
      inlineLets (easySubstFunc body b rhs)

    App f x ->
      App (inlineLets f) (inlineLets x)

    Lam b e ->
      Lam b (inlineLets e)

    _ -> expr

easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubstFunc expr fn_id fn_body = substExpr subst expr
  where
    delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id 
    subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body

simplifyPrg :: HscEnv -> [CoreRule] -> ModGuts -> IO ModGuts
simplifyPrg hscEnv rules guts = do
  -- let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)
  let 
    dflags = hsc_dflags hscEnv
    logger = hsc_logger hscEnv
    rdr_env = mg_rdr_env guts 
    name_ppr_ctx =
        mkNamePprCtx
          (initPromotionTickContext dflags)
          (hsc_unit_env hscEnv)
          rdr_env
    extra_vars     = interactiveInScope (hsc_IC hscEnv)
  let opts = initSimplifyOpts dflags extra_vars (2)
                             (initSimplMode dflags (Phase 0) "main") (mkRuleBase rules)


  (counts, guts') <- simplifyPgm logger (hsc_unit_env hscEnv) name_ppr_ctx opts guts
  -- initSmpl logger my_rule_env top_env_cfg sz $
                        -- simplExpr my_env expr
  -- when (logHasDumpFlag logger Opt_D_verbose_core2core && logHasDumpFlag logger Opt_D_dump_simpl_stats) $
  --     logDumpMsg logger "Simplifier statistics for following pass"
  --           (vcat [text "term-msg" <+> text "after" <+> ppr it_count
  --                                       <+> text "iterations",
  --                   blankLine,
  --                   pprSimplCount counts_out])

  return guts'


simplifyFunc :: HscEnv -> [CoreRule] -> CoreExpr -> Id -> Id -> IO CoreExpr
simplifyFunc hscEnv rules expr fnId fbId = do
  euc <- initExternalUnitCache
  let dflags = hsc_dflags hscEnv
  let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)
  let logger = hsc_logger hscEnv

  eps <- eucEPS euc
  let fam_envs =  ( eps_fam_inst_env eps
                  , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                  )

      simpl_env = mkSimplEnv (se_mode opts) fam_envs
      delAddOneVSet = addOneToUniqSet (delOneFromUniqSet (exprFreeVars expr) fnId) fbId
      my_in_scope_del_add_one = (getInScope simpl_env) `extendInScopeSetSet` delAddOneVSet 
      -- my_in_scope = (getInScope simpl_env) `extendInScopeSetSet` (exprFreeVars expr)
      my_env = setInScopeSet simpl_env my_in_scope_del_add_one
      -- my_env_two = GHC.Core.Opt.Simplify.Env.extendIdSubst my_env fnId (DoneId fbId)
      -- my_env_tree = setInScopeSet my_env $ (getInScope my_env) `extendInScopeSetSet` delOneVSet
      
      top_env_cfg = se_top_env_cfg opts
      read_eps_rules = eps_rule_base <$> eucEPS euc
      read_ruleenv = updExternalPackageRules emptyRuleEnv <$> read_eps_rules
      my_rule_env  = (\a -> addLocalRules a rules) <$> read_ruleenv
  putStrLn $ "------MY-ENV-------"
  putStrLn $ showSDocUnsafe $ pprSimplEnv my_env
  putStrLn $ "------MY-RULE-ENV-------"

  let sz = exprSize expr
  (expr', counts) <- initSmpl logger my_rule_env top_env_cfg sz $
                        simplExprGently my_env expr
  putDumpFileMaybe logger Opt_D_dump_simpl_stats "Simplifier statistics" FormatText (pprSimplCount counts)

  putDumpFileMaybe logger Opt_D_dump_simpl "Simplified expression" FormatCore (pprCoreExpr expr')
  -- putStrLn $ "------MY-ENV-------"
  -- putStrLn $ showSDocUnsafe $ pprSimplEnv my_env_two
  -- putStrLn $ "------MY-RULE-ENV-------"
  re <- my_rule_env
  putStrLn $ "Local: " ++ showSDocUnsafe (pprRuleBase $ re_local_rules re)
  putStrLn $ "Home: " ++ showSDocUnsafe (pprRuleBase $ re_home_rules re)
  putStrLn $ "EPS: " ++ showSDocUnsafe (pprRuleBase $ re_eps_rules re)
  putStrLn $ "------"
  putStrLn $ showSDocUnsafe $ ppr $ substId my_env fnId
  putStrLn $ "------"
  putStrLn $ showSDocUnsafe $ ppr $ substId my_env fnId
  putStrLn $ "------ ID-INFO"
  putStrLn $ showSDocUnsafe $ ppr $ getUnique (ru_fn (head rules))
  putStrLn $ showSDocUnsafe $ ppr $ getUnique (getName fnId)
  putStrLn $ showSDocUnsafe $ ppr $ idInfo fnId
  putStrLn $ showSDocUnsafe $ ppr $ idCoreRules fnId
  putStrLn $ "------MY-ENV-------"
  return expr'

simplExprGently env expr = do
    expr1 <- simplExpr env (occurAnalyseExpr expr)
    simplExpr env (occurAnalyseExpr expr1)


simplifyTopBind :: HscEnv -> [CoreRule] -> [CoreBind] -> IO ()
simplifyTopBind hscEnv rules binds = do
  euc <- initExternalUnitCache
  let dflags = hsc_dflags hscEnv
  let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)
  let logger = hsc_logger hscEnv

  eps <- eucEPS euc
  let fam_envs =  ( eps_fam_inst_env eps
                  , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                  )

      simpl_env = mkSimplEnv (se_mode opts) fam_envs
      (NonRec _ expr) = head $ binds
      my_in_scope = (getInScope simpl_env) `extendInScopeSetSet` (exprFreeVars expr)
      my_env = setInScopeSet simpl_env my_in_scope
      -- my_env_two = GHC.Core.Opt.Simplify.Env.extendIdSubst my_env fnId (mkContEx my_env fnBody)
      -- delOneVSet = delOneFromUniqSet (exprFreeVars expr) fnId
      -- my_env_two = setInScopeSet my_env $ (getInScope my_env) `extendInScopeSetSet` delOneVSet
      
      top_env_cfg = se_top_env_cfg opts
      read_eps_rules = eps_rule_base <$> eucEPS euc
      read_ruleenv = updExternalPackageRules emptyRuleEnv <$> read_eps_rules
      my_rule_env  = (\a -> addLocalRules a rules) <$> read_ruleenv

  let sz = coreBindsSize binds
  (expr', counts) <- initSmpl logger my_rule_env top_env_cfg sz $
      do { (floats, env1) <- simplTopBinds my_env binds

                      -- Apply the substitution to rules defined in this module
                      -- for imported Ids.  Eg  RULE map my_f = blah
                      -- If we have a substitution my_f :-> other_f, we'd better
                      -- apply it to the rule to, or it'll never match
                  ; rules1 <- simplImpRules env1 []

                  ; return (getTopFloatBinds floats, rules1) } 

  putDumpFileMaybe logger Opt_D_dump_simpl_stats "Simplifier statistics" FormatText (pprSimplCount counts)

  -- putDumpFileMaybe logger Opt_D_dump_simpl "Simplified expression" FormatCore (pprCoreExpr expr')
  putStrLn $ showSDocUnsafe $ ppr expr'
  -- putStrLn $ showSDocUnsafe $ ppr $ substId
  return ()


mySimplMSimplifier :: SimplEnv -> CoreExpr -> Id -> SimplM CoreExpr
mySimplMSimplifier my_env expr fun = do
  r <- simplExpr my_env expr
  rule_base <- getSimplRules
  let 
    rules_for_me = getRules rule_base fun
    -- out_args     = contOutArgs my_env cont :: [OutExpr]
  liftIO $ putStrLn $ showSDocUnsafe (ppr (re_local_rules rule_base))
  liftIO $ putStrLn $ showSDocUnsafe (ppr (re_home_rules rule_base))
  liftIO $ putStrLn $ showSDocUnsafe (ppr (re_eps_rules rule_base))
  liftIO $ putStrLn $ showSDocUnsafe (ppr (re_visible_orphs rule_base))
  liftIO $ putStrLn $ showSDocUnsafe (ppr rules_for_me)
  -- liftIO $ putStrLn $ showSDocUnsafe (ppr out_args)
  liftIO $ print (not (null rules_for_me) && (isClassOpId fun || activeUnfolding (seMode my_env) fun))
  return r

simplifyFuncOpts :: HscEnv -> CoreRule -> CoreExpr -> IO (RuleOpts, InScopeEnv, Activation -> Bool, SimplEnv)
simplifyFuncOpts hscEnv rule expr = do
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
  let
    ropts        = seRuleOpts my_env :: RuleOpts
    in_scope_env = getUnfoldingInRuleMatch my_env :: InScopeEnv
    act_fun      = activeRule (seMode my_env) :: Activation -> Bool

  return (ropts, in_scope_env, act_fun, my_env)
