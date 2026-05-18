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
import ProofBase ( ExprInfo(..), SideExprInfo(..) )
import SortDecls ( sorteDeclConvrs )
import GHC.Core.Opt.Simplify.Utils
import GHC.Core.SimpleOpt ( defaultSimpleOpts, simpleOptExpr, SimpleOpts(..) )
import GHC.Core.Utils
import GHC.Types.Tickish
import GHC.Plugins hiding (L, getModule)
--  (ModGuts(..), getUnique)
import GHC.Core.Opt.OccurAnal
import GHC.RTS.Flags (GiveGCStats)
import System.FilePath ( (</>) )
import Control.Monad.IO.Class (MonadIO)


logPath :: FilePath
logPath = "logs" </> "app.log"

proofbasePath :: FilePath
proofbasePath = "src" </> "ProofBase.hs"

filePath :: FilePath
filePath = "examples" </> "allExamples.hs"

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags' <- getSessionDynFlags
    let dflags = gopt_set dflags' Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags
    session <- getSession

    liftIO $ writeFile logPath ""
    (mg_main, mg_base) <- getModulesGuts

    -- logMsg "\n=== Core mg_binds ===\n"
    -- logMsg (showSDocUnsafe $ ppr $ mg_binds mg_main)

    -- create State
    let astState = getState session (mg_binds mg_main) (mg_binds mg_base)
    -- logMsg "\n===== Collected AstState =====\n"
    -- logMsg $ prettyString astState
    -- logMsg "\n===== End AstState =====\n"
    _ <- liftIO $ analyzeModuleSt astState

    logMsg            "\n===== The End: App/Main ====="
    liftIO $ putStrLn "\n===== The End: App/Main ====="



---- GET MOD GUTS
getModulesGuts :: GhcMonad m => m (ModGuts, ModGuts)
getModulesGuts =
  do
    targets <- mapM (\fp -> guessTarget fp Nothing Nothing) [filePath, proofbasePath]
    setTargets targets
    _ <- load LoadAllTargets

    modGraph <- depanal [] False
    mg_base  <-
      case find (\m -> "ProofBase" == showSDocUnsafe (ppr (moduleName (ms_mod m)))) $ mgModSummaries modGraph of
        Just ms -> getModGuts ms
        Nothing -> error $ "Error. Module `ProofBase` not found. All modules:\n" ++ showSDocUnsafe (ppr (map (moduleName . ms_mod) (mgModSummaries modGraph)))
    mg_main <-
      case filter (\m -> "ProofBase" /= showSDocUnsafe (ppr (moduleName (ms_mod m)))) $ mgModSummaries modGraph of
        [ms] -> getModGuts ms
        _    -> error "Error. Expected to find single NOT `ProofBase` Module"
    return (mg_main, mg_base)
  where
    getModGuts :: GhcMonad m => ModSummary -> m ModGuts
    getModGuts ms = parseModule ms >>= typecheckModule >>= desugarModule <&> dm_core_module


---- COLLECTING AST STATE
getState :: HscEnv -> CoreProgram -> CoreProgram -> CheckerST
getState hscEnv core_binds base_binds = CheckerST {
  st_declconvrs   = sortedDeclConvrs,
  st_funcdefs     = binds,
  st_postldefs    = [],
  st_hscenv       = hscEnv,
  st_base_defs    = flattenBinds base_binds,
  st_cnvrs_count  = 0,
  st_declconvr_id = Nothing
  -- TODO. maybe add st_counter = CheckerCounter{}
}
  where
  binds    = map (fmap inlineLetsIgnoreCast) $ flattenBinds core_binds
  sortedDeclConvrs = case sorteDeclConvrs $ concatMap collectConvrs binds of
    Left cyrcles -> error $ "Error. Cyrcle dependencies were found.\n" ++ showSDocUnsafe (ppr cyrcles)
    Right sdc    -> sdc


collectConvrs :: FuncDef -> [DeclConversions]
collectConvrs (f_id, f_body) = case map getConvrs pairs_skip_lhe_qed of
    []      -> []
    convrs  -> [(f_id, convrs)]
  where
  argAddInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe f_body,
    "--." <- [getStrById exprName] ]
  pairs  = zip argAddInfo (drop 1 argAddInfo)
  pairs_skip_lhe_qed = filter (\((_, v_cmnt), _) ->
    case v_cmnt of
      (Var cmnt) | getStrById cmnt == "QED" -> False
      _ -> True
    ) pairs
  getConvrs ((lhe, c1), (rhe, _)) = Conversion lhe rhe (toSideExprInfo c1)
---- END COLLECTING AST STATE


---- UTILS
createFail :: CheckerST -> String -> String
createFail CheckerST{..} reason =
  "Fail in decl: " ++ str_decl_id ++ " in conversion number: " ++ show st_cnvrs_count ++ "\n"
  ++ "  Reason: " ++ reason
  where
    str_decl_id = maybe "<No decl_id>" getStrById st_declconvr_id

getStrById :: Id -> String
getStrById v = occNameString (getOccName v)

toSideExprInfo :: CoreExpr -> SideExprInfo
toSideExprInfo (App (Var expr_side) expr_info) = toSideInfo (toExprInfo expr_info)
  where
  toSideInfo
    | getStrById expr_side == "L" = L
    | getStrById expr_side == "R" = R
    | otherwise = err "`L` or `R`" expr_side
  toExprInfo (Var v)
    | getStrById v == "Beta" = Beta
    | getStrById v == "Eta"  = Eta
  toExprInfo (App (Var v_id) (App _ (Lit (LitString pack_str))))
    | getStrById v_id == "Def"  = Def  $ BS8.unpack pack_str
    | getStrById v_id == "Prop" = Prop $ BS8.unpack pack_str
    | getStrById v_id == "Inst" = Inst $ BS8.unpack pack_str
  toExprInfo (App (App (Var v_id) (App _ (Lit (LitString pack_str)))) (App _ (Lit (LitNumber _ n))))
    | getStrById v_id == "DefRec" && n > 0 = DefRec (BS8.unpack pack_str) n
  toExprInfo _ = err "`Beta`, `Eta`, `Def  comment`, `Prop comment`, `Inst comment` or DefRec comment n > 0" expr_info
  err str_expect e = error $ "Unexpected expression structure for comment, expected " ++ str_expect ++ ".\nGot: " ++ prettyString e
toSideExprInfo (Var expr_side) | getStrById expr_side == "Postulate" = Postulate
toSideExprInfo e = error $ "Unexpected expression structure for comment, expected a function application with a string literal argument.\nGot: " ++ prettyString e

{-
 assume that any variable in convertion is OR
  * in (\x ->) this convertion
  * global func
  * parametr for this function

  alphaEq called for whole expr works correctly
  for subexpr need to remember Lam-binds (\x ->)
-}
alphaEq :: (Eq (DeBruijn a)) => a -> a -> Bool
alphaEq lhv rhv = deBruijnize lhv == deBruijnize rhv

-- Called in getFirstDiff
alphaEqWithEnv :: (Eq (DeBruijn a)) => ([Id], [Id]) -> a -> a -> Bool
alphaEqWithEnv (l_vars, r_vars) lhv rhv =
    deBrujinWithEnv lhv l_vars == deBrujinWithEnv rhv r_vars
  where
    deBrujinWithEnv e vars =
      case deBruijnize e of (D cm_env a) -> D (extendCMEs cm_env vars) a


mapPassStM :: (Monad m) => (a -> s -> m (b, s)) -> [a] -> s -> m [(b, s)]
mapPassStM _ [] _ = return []
mapPassStM f (a:as) s = do
  r@(_, s1) <- f a s
  (r :) <$> mapPassStM f as s1


mkRulePstl :: HscEnv -> Id -> [CoreBndr] -> CoreExpr -> CoreExpr -> Maybe PostlDef
mkRulePstl hscEnv pstl_id pstl_binds pstl_lhs pstl_rhs = 
  case lhs_func of
        Var fid -> Just $ mkRuleHelper (getName fid) fid
        _       -> Nothing
  where
    (lhs_func, lhs_args) = collectArgs pstl_lhs
    mkRuleHelper lhs_f_name f_id = PostlDef pstl_id f_infoId rule
      where
        rule = mkRule
          (getModule hscEnv)
          False
          True
          (mkFastString ("my-rule-" ++ getStrById pstl_id))
          AlwaysActive
          lhs_f_name
          pstl_binds
          lhs_args
          pstl_rhs
        f_infoId = modifyIdInfo (`setRuleInfo` RuleInfo [rule] emptyDVarSet) f_id
        getModule = mainModIs . hsc_HUE
---- UTILS


logMsg :: (MonadIO m) => String -> m ()
logMsg log_msg = liftIO $ appendFile logPath (log_msg ++ "\n")


incCnvrsCounter :: CheckerM ()
incCnvrsCounter = 
  do
    modify (\st -> st { st_cnvrs_count = st_cnvrs_count st + 1 })
    cnvrs_count <- gets st_cnvrs_count
    decl_id     <- gets st_declconvr_id
    logMsg $ "\n----------------\n" ++ 
      "Start analyzing: decl=`" ++ prettyString decl_id ++ "` conversion=" ++ show cnvrs_count ++ "\n"

newDeclCnvrs :: Id -> CheckerM ()
newDeclCnvrs decl_id = modify (\st -> st { st_cnvrs_count = 0, st_declconvr_id = Just decl_id })

madePostulate :: Id -> CheckerM ()
madePostulate fn_id =
  do
    (f_id, f_body)     <- getBodyByFuncId fn_id
    let (pstl_binds, _) = collectBinders f_body
    declConvrs <- gets st_declconvrs

    (convrs_fst, convrs_lst) <- case lookup f_id declConvrs of
      Just convrs@(cnvr:_) -> return (cnvr, last convrs)
      _                    -> throwError $ 
        "Unexpected state. Succesfully analized " ++ getStrById f_id ++ " but it doesn't have conversions."
    hscEnv     <- gets st_hscenv
    case mkRulePstl hscEnv f_id pstl_binds (cn_lhs convrs_fst) (cn_rhs convrs_lst) of
      Nothing -> logMsg $ "Can't make postulate from `" ++ prettyString f_id ++ 
        "`.\n  Pstl_lhs must be of form (f e1 .. en) where f is not forall'd.\n"
      Just new_postl -> do
        logMsg $ "Made new postulate from: " ++ prettyString f_id ++ "\n"
        modify (\st -> st { st_postldefs = new_postl : st_postldefs st})



------ Analyze
analyzeModuleSt :: CheckerST -> IO ()
analyzeModuleSt checkerST =

  do
    result <- mapPassStM runChecker (st_declconvrs checkerST) checkerST
    putStrLn $ prettyStringReport $ toReport result

  where
    runChecker x = runStateT (runExceptT (analyzeDeclCnvrs x))
    toReport     = foldr resToReport ([], [])
    resToReport (res, st) (succs, fails) = case res of
      Left reason  -> (succs         , createFail st reason : fails)
      Right res_id -> (res_id : succs,                        fails)

    analyzeDeclCnvrs :: DeclConversions -> CheckerM Id
    analyzeDeclCnvrs (decl_id, cnvrs) =
      do
        newDeclCnvrs decl_id
        logMsg $ "\n-----------------------------\n" ++ 
          "Start analyze declConversion: " ++ prettyString decl_id ++ "\n"
        mapM_ analyzeConvrs cnvrs
        madePostulate decl_id
        return decl_id


---- ANALYZE SINGLE CONVERSION
cmpCnvrs :: CoreExpr -> CoreExpr -> CheckerM ()
cmpCnvrs e_cntr e | alphaEq e_cntr e = logMsg "Compare result: True\n"
cmpCnvrs e_cntr e = 
  do
    logMsg $
      "EXPR: " ++ prettyString e ++ "\n" ++
      "==?==\n" ++
      "CNTR: " ++ prettyString e_cntr ++ "\n" ++
      "Compare result: False\n"
    throwError $ "Error. Not equal." ++ 
      "\n\nExpected: " ++ prettyString e_cntr ++ 
      "\n\n.    Got: " ++ prettyString e ++ "\n"


analyzeConvrs :: Conversion -> CheckerM ()
analyzeConvrs Conversion{..} =
  do
    incCnvrsCounter
    case cn_info of
      Postulate -> return ()
      L info    -> analyze cn_lhs cn_rhs info
      R info    -> analyze cn_rhs cn_lhs info
      info      -> throwError $ "Unexpected converseion_info. Expected useful information. Get:" ++ prettyString info

  where
    analyze expr control_expr expr_info =
      do
        let analyzeExpr = case expr_info of
              Def  comment   -> analyzeDefConv  comment 0
              Prop comment   -> analyzePropConv comment
              Inst comment   -> analyzeInstConv comment
              DefRec cmnt n  -> analyzeDefConv  cmnt n
              Eta            -> analyzeEtaConv
              Beta           -> analyzeBetaConv
        (ce, e) <- analyzeExpr control_expr expr
        cmpCnvrs ce e

---- just believe that this is enought
getFirstDiff :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr -> CoreExpr)
getFirstDiff contrl_expr expr = 
  do
    (d_expr, bldr, _) <- go ([], []) contrl_expr expr 
    logMsg $ "getFirstDiff result:" ++ 
      "\ncntr_expr:\n" ++ prettyString contrl_expr ++ 
      "\nexpr:\n" ++ prettyString d_expr ++ "\n"
    return (d_expr, bldr)

  where
    go cm_envs (Lam cntr_b cntr_body) (Lam b body) = do
      let new_cm_envs = bimap (cntr_b :) (b :) cm_envs
      res <- go new_cm_envs cntr_body body
      return $ updBuilder (Lam b .) res
    go cm_envs ce@(App _ (Type _)) e@(App _ (Type _)) = checkEq cm_envs ce e True
    go cm_envs (App cntr_f cntr_arg) (App f arg) =
      (go cm_envs cntr_f f <&>
        \case
          (diff, bldr, True)  -> (App diff arg, bldr, True)
          (diff, bldr, False) -> (diff, \x -> App (bldr x) arg, False))
        <|> (go cm_envs cntr_arg arg <&> updBuilder (App f .))
    go cm_envs ce e@(App _ _) = checkEq cm_envs ce e True
    go cm_envs ce e = checkEq cm_envs ce e False

    updBuilder updater (diff_expr, builder, _) = (diff_expr, updater builder, False)
    checkEq cm_envs ce e is_collect
      | alphaEqWithEnv cm_envs ce e = throwError $ "No difference." ++ 
        "\n  cntr_expr: " ++ prettyString ce ++ 
        "\n       expr: " ++ prettyString e ++ "\n"
      | otherwise    = do
        logMsg $ "Get diff:\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e ++ "\n"
        return (e, id, is_collect)

getNAppearance :: String -> Integer -> CoreExpr -> CheckerM (CoreExpr, CoreExpr -> CoreExpr)
getNAppearance comnt m expr = go m expr >>= (\(x, y, _) -> return (x, y))
  where
    go n (Lam b body) = go n body <&> updBuilder (Lam b .)
    go n (App f arg) = do
      (new_e, new_builder, new_n) <- go n f
      if new_n <= 0
        then return (new_e, \x -> App (new_builder x) arg, new_n)
        else go new_n arg <&> updBuilder (App f .)
    go n f@(Var f_id) | getStrById f_id == comnt = return (f, id, n - 1)
    go n e = return (e, id, n)

    updBuilder updater (diff_expr, builder, n) = (diff_expr, updater builder, n)

analyzeBetaConv :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeBetaConv control_expr expr = return (control_expr, expr) -- TODO: check alphaEq

analyzeEtaConv :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeEtaConv control_expr expr =
  do
    logMsg "Evaluate eta-reduction"
    (diff_expr, builder) <- getFirstDiff control_expr expr
    new_expr <- case diff_expr of
      (Lam v1 (App f (Var v2))) | v1 == v2 -> return f  -- TODO: check and fix
      _ -> throwError $ "Error in analyzeEtaConv:\n" ++ prettyString diff_expr
    return (control_expr, builder new_expr)

analyzeDefConv :: String -> Integer -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeDefConv comment n control_expr expr =
  do
    logMsg "Evaluate def-conversion"
    (diff_expr, builder) <-
      if n <= 0
        then getFirstDiff control_expr expr
        else getNAppearance comment n expr
    subst_expr      <- substitute diff_expr
    let restr_expr   = builder subst_expr
    simpl_expr      <- simplifyOptFunc restr_expr
    return (control_expr, simpl_expr)

  where
    substitute e =
      do
        let (func, args)      = collectArgs e
        fn_id                <- checkComment func
        (func_id, func_body) <- getBodyByFuncId fn_id
        logMsg $ "Substitute def for function: " ++ prettyString func_id ++ "\n"
        let subst_func        = easySubstFunc (Var func_id) func_id func_body
        return $ mkCoreApps subst_func args

    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | getStrById func_id == comment = return func_id
      | otherwise                     = throwError $ 
        "Applied function_id does not match comment:" ++ 
        "\n Expected: " ++ comment ++ 
        "\n Got     : " ++ prettyString func_id
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e

getBodyByFuncId :: Id -> CheckerM (Id, CoreExpr)
getBodyByFuncId func_id =
  do
    let (fl_id, stDefs) = case nameModule_maybe (idName func_id) of
          Just modl | showSDocUnsafe (ppr modl) == "ProofBase" -> (localiseId func_id, st_base_defs)
          _                                                    -> (func_id, st_funcdefs)
    func_defs <- gets stDefs
    case lookup func_id func_defs of
      Just func_body -> return (fl_id, func_body)
      Nothing        -> throwError $ "Function definition not found for:\n" ++ prettyString func_id


analyzePropConv :: String -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzePropConv comment control_expr expr =
  do
    logMsg "Evaluate prop-conversion"
    (diff_expr, builder) <- getFirstDiff control_expr expr
    postl_defs           <- gets st_postldefs
    let matchedPstls      = filter ((comment ==) . getStrById . pstl_id) postl_defs
    rule <- case matchedPstls of
      [pstl] -> return pstl
      (_:_)  -> throwError $ "Unexpected postulate. Found more than one matched with comment `" ++ comment ++ "`"
      []     -> throwError $ "Unexpected postulate. Not found match with comment `"             ++ comment ++ "`"

    lookup_expr        <- substRule [rule] diff_expr
    let lookup_restored = builder lookup_expr
    -- TODO
    simpl_expr         <- simplifyOptFunc lookup_restored
    return (control_expr, simpl_expr)


analyzeInstConv :: String -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeInstConv comment control_expr expr =
  do
    logMsg "Evaluate inst-conversion"
    (diff_expr, builder) <- getFirstDiff control_expr expr
    subst_inst      <- substituteInst diff_expr
    subst_simp      <- simplifyOptFunc subst_inst
    subst_expr      <- ordinar_subst subst_simp
    let restr_expr   = builder subst_expr
    simpl_expr      <- simplifyOptFunc restr_expr
    return (control_expr, simpl_expr)

  where
    substituteInst expr =
      do
        let (func, args) = collectArgs expr
        func_id         <- checkComment func
        let func_body    = unfoldingTemplate $ idUnfolding func_id

        {- TODO check why doesn't work
          logMsg $ "SUBS_INST" ++ 
            "\nsubst_func:\n" ++ prettyString subst_func ++ 
            "\n      func:\n" ++ prettyString func ++ 
            "\n   func_id:\n" ++ prettyString func_id ++ 
            "\n func_body:\n" ++ prettyString func_body
        -}
        let subst_selector = mkCoreApps func_body (take 2 args)
        selector_simpl    <- simplifyOptFunc subst_selector
        logMsg $ "Substitute selector for instance_method: " ++ prettyString func_id ++ "\n"
        -- logMsg $ "Selector implementation\n" ++ prettyString selector_simpl ++ "\n"


        let (Var instce_id, _) = collectArgs (args !! 1)
        (inst_id, inst_body)  <- getBodyByFuncId instce_id
        let subst_inst         = easySubstFunc selector_simpl inst_id inst_body
        selector_inst         <- simplifyOptFunc subst_inst
        logMsg $ "Substitute instance for instance_method: " ++ prettyString instce_id ++ "\n"
        -- logMsg $ "Selector instanced\n" ++ prettyString selector_inst
        return $ mkCoreApps selector_inst (drop 2 args)

    ordinar_subst expr =
      do
        let (func@(Var fn_id), args) = collectArgs expr
        (func_id, func_body)        <- getBodyByFuncId fn_id
        let subst_func = easySubstFunc func func_id func_body
        logMsg $ "Substitute instance method for inst: " ++ prettyString func_id ++ "\n"
        return $ mkCoreApps subst_func args

    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | getStrById func_id == comment = return func_id
      | otherwise  = throwError $ 
        "Applied function_id does not match comment:" ++ 
        "\n Expected: " ++ comment ++ 
        "\n Got     : " ++ prettyString func_id
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e




---- SIMPLIFIERS
inlineLetsIgnoreCast :: CoreExpr -> CoreExpr
inlineLetsIgnoreCast expr =
  case expr of
    Let (NonRec b rhs) body ->
      inlineLetsIgnoreCast (easySubstFunc body b rhs)
    App f x ->
      App (inlineLetsIgnoreCast f) (inlineLetsIgnoreCast x)
    Lam b e ->
      Lam b (inlineLetsIgnoreCast e)
    Cast e _ -> inlineLetsIgnoreCast e
    _ -> expr

easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubstFunc expr fn_id fn_body = substExpr subst expr
  where
    delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id
    subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body

simplifyOptFunc :: CoreExpr -> CheckerM CoreExpr
simplifyOptFunc expr = go 0 expr
  where
    go :: Int -> CoreExpr -> CheckerM CoreExpr
    go n _ | n >= 3 = throwError $ 
      "Unexpected expression. Expression needs to much beta-reductions. " ++ 
      "Default threshold = 3. Expr:\n" ++ prettyString expr ++ "\n"
    go n e = do
      logMsg $ "Try simplifyOptFunc n=" ++ show n ++ "\n"
      let no_lets_expr = inlineLetsIgnoreCast (simpleOptExpr defaultSimpleOpts e)
      case find isBetaRedex (universe no_lets_expr) of
        Just _  -> go (n + 1) no_lets_expr
        Nothing -> return no_lets_expr

    isBetaRedex (App (Lam _ _) _) = True
    isBetaRedex _                 = False


substRule :: [PostlDef] -> CoreExpr -> CheckerM CoreExpr
substRule pstls expr =
  do
    hscEnv <- gets st_hscenv
    let opts   = initSimplifyExprOpts (hsc_dflags hscEnv) (hsc_IC hscEnv)

    euc <- liftIO initExternalUnitCache
    eps <- liftIO (eucEPS euc)

    let fam_envs =  ( eps_fam_inst_env eps
                    , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                    )
        rules = map pstl_rule pstls
        simpl_env = mkSimplEnv (se_mode opts) fam_envs
        ru_rhs_fv = map ruleRhsFreeVars rules
        fv_set    = foldl unionUniqSets (exprFreeVars expr) ru_rhs_fv
        -- NOTE order is important. We want to preserve modified pstl_fid
        fv_idInfo_set = fv_set `addListToUniqSet` map pstl_fid pstls
        my_in_scope   = getInScope simpl_env `extendInScopeSetSet` fv_idInfo_set
        my_env        = setInScopeSet simpl_env my_in_scope

    let
      ru_opts         = seRuleOpts my_env           :: RuleOpts
      in_scope_env = getUnfoldingInRuleMatch my_env :: InScopeEnv
      act_fun      = activeRule (seMode my_env)     :: Activation -> Bool
      rules_id_str = show $ map (prettyString . pstl_id) pstls
      (Var f_target, args_targetgs) = collectArgs expr

    case lookupRule ru_opts in_scope_env act_fun f_target args_targetgs rules of
      Nothing -> do
        logMsg     $ "Rule `" ++ rules_id_str ++ "`not fired." ++ "\n"
        throwError $ "Rule `" ++ rules_id_str ++ "`not fired." ++ 
          "\nRule:\n" ++ prettyString pstls ++ 
          "\nExpr:\n" ++ prettyString expr ++ "\n"
      Just (applied_rule, new_expr) -> do
          logMsg $ "Rule fired:" ++ rules_id_str ++ "\n"
          return $ reapplyExtraArgs applied_rule new_expr

  where
    reapplyExtraArgs applied_rule new_expr = mkApps new_expr (leftoverArgs applied_rule)
    leftoverArgs ap_ru = drop (ruleArity ap_ru) $ snd (collectArgs expr)



-- {- TODO:
--     * collectModule no dif just yet
--     * analyze each conversion separatly
--         * Chcek comment. 
--         * if Func 
--             * take correct hand-side
--             * find first applied function: 
--                 * it could be inside lam 
--                 * compare that before that alphaEq
--             * Check that function coresponds with comment
--             * Find defenition for func
--             * subst and restore function 
--             * simplify ? (restored function) (whole expr) 
--             * letinlined 
--             * compare alphaEq
--         * if Beta
--             * compare alphaEq
--     * prettyStringBinds (cm_binds coreMod)
-- -}



-- {-
--   Context: 
--     variables with types or Types
--     free variables?

--   Variables at the moment:
--     global
--     params

--   wrap in monad
--     except
--     store context

--   TODO make meaningfull subst
--     a==b
--     k==(\x = expr expr expr)

--     k a ==> (\x = expr expr expr) b

--     expr_l ==> (\x y -> expr_l) == (\x y -> expr_r) <== expr_r
--     expr_o ==> (\x y -> expr_o) x_o y_o

--     expr_o ==> (\x y -> expr_o) x_o y_o ==> (\x y -> (\x y -> expr_l)) x_o y_o ==> 
--     (\x_o y_o -> expr_l) ==> (\x_o y_o -> expr_r) ==> expr_r

--   TWO STEPS
--     match all variables from expr_o to expr_l (expr_l==expr_o)
--     subst all variables into expr_r
-- -}
