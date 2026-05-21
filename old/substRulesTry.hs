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
      Module )
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
import GHC.Types.Id ( modifyIdInfo, idInfo )
import GHC.Core.Rules ( addLocalRules, emptyRuleEnv, mkRule, updExternalPackageRules, lookupRule, roughTopNames, matchExprs )
import GHC.Core.Opt.Simplify.Env ( getInScope, mkSimplEnv, setInScopeSet, pprSimplEnv, seRuleOpts, SimplEnv (seMode) )
import GHC.Types.Id.Info ( RuleInfo(..), setRuleInfo, IdInfo (ruleInfo), ruleInfoRules )

import AstInfo
import PrettyString
import SortDecls ( sorteDeclConvrs )
import GHC.Core.Opt.Simplify.Utils
import GHC.Core.SimpleOpt ( defaultSimpleOpts, simpleOptExpr, SimpleOpts(..) )


main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags' <- getSessionDynFlags
    let dflags = gopt_set dflags' Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags
    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example-5.5.hs"
    coreMod <- compileToCoreModule filePath

    -- print CoreModule
    -- liftIO $ putStrLn "\n=== Core cm_types ===\n"
    -- liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_types coreMod)
    liftIO $ putStrLn "\n=== Core cm_binds ===\n"
    liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_binds coreMod)

    -- create State
    let astState = getState session coreMod
    liftIO $ putStrLn "\n===== Collected AstState =====\n"
    liftIO $ putStrLn $ prettyString astState
    liftIO $ putStrLn "\n===== End AstState =====\n"
    liftIO $ analyzeModuleSt astState
    liftIO $ putStrLn "\n===== Sorted DeclConvers =====\n"
    liftIO $ putStrLn $ prettyString (map fst (st_declconvrs astState))
    liftIO $ putStrLn "\n===== End Sorted DeclConvers =====\n"
    -- liftIO $ putStrLn result
    -- let result = analyzeConversions astState
    -- case result of
    --   Left err -> liftIO $ putStrLn $ "Error: " ++ err
    --   Right convrs -> do
    --     liftIO $ putStrLn "\n=== Simplify Analysis ===\n"
    --     liftIO $ printMy session convrs
    --     liftIO $ putStrLn "\n=== End ===\n"
    --     mapM_ (\(e1, e2) -> (liftIO (simplifyFunc session e1), e2)) convrs
    --     liftIO $ putStrLn $ map prettyStringEqPairs $ map (\(e1, e2) -> (inlineLets e1, e2)) m


    liftIO $ putStrLn "\n===== The End: App/Main ====="

-- checkModule :: HscEnv -> CoreModule -> IO ()
-- checkModule hscEnv CoreModule{..} = 
--   do

--     putStrLn "\n===== End: checkModule ====="

---- COLLECTING AST STATE
getState :: HscEnv -> CoreModule -> CheckerST
getState hscEnv CoreModule{..} = CheckerST {
  st_declconvrs   = sortedDeclConvrs,
  st_funcdefs     = binds,
  st_postldefs    = concatMap (collectPostls hscEnv) binds,
  st_hscenv       = hscEnv,
  st_cnvrs_count  = 0,
  st_declconvr_id = Nothing
  -- TODO. maybe add st_counter = CheckerCounter{}
}
  where
  -- declConvrs = orderConvrs $ concatMap collectConvrs binds
  -- declConvrsOrdered = uncurry (++) $ partition (isPrefixOf "lemma" . getStrById . fst) declConvrs
  binds    = flattenBinds cm_binds
  sortedDeclConvrs = case sorteDeclConvrs $ concatMap collectConvrs binds of
    Left cyrcles -> error $ "Error. Cyrcle dependencies were found.\n" ++ showSDocUnsafe (ppr cyrcles)
    Right sdc    -> sdc
  -- (funcDefs, postlDefs, proofsDefs) = foldr splitFunc ([], [], []) binds
  -- splitFunc (fns, pstls, prfs) bind
  --   | isAppliedFn bind value_id = (fns, pstls, bind : prfs)
  --   | isAppliedFn bind postl_id = (fns, bind : pstls, prfs)
  --   | otherwise                 = (bind : fns, pstls, prfs)

  -- isAppliedFn (_, body) cmp_id = case getFirstApp body of
  --   Var app_id -> app_id == cmp_id
  --   _          -> False
  -- getFirstApp = collectFunSimple . snd . collectBinders

  -- value_id = head $ filterByStrName "value"
  -- postl_id = head $ filterByStrName "postulate"

  -- filterByStrName strName = filterNameEnv (\case
  --   AnId elt_id -> getStrById elt_id == strName
  --   _           -> False) cm_types

orderConvrs :: [DeclConversions] -> [DeclConversions]
orderConvrs = uncurry (++) . partition (isPrefixOf "lemma" . getStrById . fst)

collectPostls :: HscEnv -> FuncDef -> [PostlDef]
collectPostls hscEnv (f_id, f_body) = res
  -- case pstl_rest of
  -- App (App (App (Var app_id) _) pstl_lhs) pstl_rhs | getStrById app_id == "postulate"
  --   -> [mkRulePstl hscEnv f_id pstl_binds pstl_lhs pstl_rhs]
  -- _ -> []

  where
  res = [mkRulePstl hscEnv f_id pstl_binds pstl_lhs pstl_rhs |
    App (App (App (Var app_id) _) pstl_lhs) pstl_rhs <- universe pstl_rest,
    "postulate" <- [getStrById app_id] ]
  (pstl_binds, pstl_rest) = collectBinders f_body

collectConvrs :: FuncDef -> [DeclConversions]
collectConvrs (f_id, f_body) = case map getConvrs pairs of
    []      -> []
    convrs  -> [(f_id, convrs)]
  where
  argAddInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe f_body,
    "--." <- [getStrById exprName] ]
  pairs  = zip argAddInfo (drop 1 argAddInfo)
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
-- (L (FuncRec
--                       (unpackCString# "myFoldl"#)
--                       (fromInteger @Natural $fNumNatural (IS 1#))))
-- (L (Func (unpackCString# "myConst"#)))
  where
  toSideInfo
    | getStrById expr_side == "L" = L
    | getStrById expr_side == "R" = R
    | otherwise = err "`L` or `R`" expr_side
  toExprInfo (Var v)
    | getStrById v == "Beta" = Beta
    | getStrById v == "Eta"  = Eta
  toExprInfo (App (Var v_id) (App _ (Lit (LitString pack_str))))
    | getStrById v_id == "Func"  = Func $ BS8.unpack pack_str
    | getStrById v_id == "Postl" = Postl $ BS8.unpack pack_str
  toExprInfo (App (App (Var v_id) (App _ (Lit (LitString pack_str)))) (App _ (Lit (LitNumber _ n))))
    | getStrById v_id == "FuncRec" && n > 0 = FuncRec (BS8.unpack pack_str) n
  toExprInfo _ = err "`Beta`, `Eta`, `Func comment`, `Postl comment` or FuncRec comment n > 0" expr_info
  err str_expect e = error $ "Unexpected expression structure for comment, expected " ++ str_expect ++ ".\nGot: " ++ prettyString e
toSideExprInfo e = error $ "Unexpected expression structure for comment, expected a function application with a string literal argument.\nGot: " ++ prettyString e

getModule :: HscEnv -> Module
getModule = mainModIs . hsc_HUE

-- assume that any variable in convertion is OR
-- in (\x ->) this convertion
-- global func
-- parametr for this function
-- Called for whole expr and works as needs 
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

mkRulePstl :: HscEnv -> Id -> [CoreBndr] -> CoreExpr -> CoreExpr -> PostlDef
mkRulePstl hscEnv pstl_id pstl_binds pstl_lhs pstl_rhs = PostlDef pstl_id f_infoId rule
  where
    (lhs_func, lhs_args) = collectArgs pstl_lhs
    (lhs_f_name, f_id) = case lhs_func of
        Var fid -> (getName fid, fid)
        _       -> error $ "Unexpected postulate. Pstl_lhs must be of form (f e1 .. en) where f is not forall'd." ++ "\n  Found: " ++ prettyString pstl_lhs
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


collectValArgs :: Expr b -> (Expr b, [Arg b])
collectValArgs expr = go expr [] 
  where
    go app@(App f a) as 
      | isValArg a  = go f (a:as)
      | otherwise   = (app, as)
    go e         as = (e, as)
---- UTILS



logMsg :: String -> CheckerM ()
logMsg msg = liftIO $ putStrLn $ "LOG\n" ++ msg

incCnvrsCounter :: CheckerM ()
incCnvrsCounter = modify (\st -> st { st_cnvrs_count = st_cnvrs_count st + 1 })

newDeclCnvrs :: Id -> CheckerM ()
newDeclCnvrs decl_id = modify (\st -> st { st_cnvrs_count = 0, st_declconvr_id = Just decl_id })

madePostulate :: Id -> CheckerM ()
madePostulate f_id =
  do
    f_body     <- getBodyByFuncId f_id
    let (pstl_binds, _) = collectBinders f_body
    declConvrs <- gets st_declconvrs

    (convrs_fst, convrs_lst) <- case lookup f_id declConvrs of
      Just convrs -> return (head convrs, last convrs)
      Nothing     -> throwError $ "Unexpected state. Succesfully analized " ++ getStrById f_id ++ " but it doesn't have conversions."
    hscEnv     <- gets st_hscenv
    let new_postl = mkRulePstl hscEnv f_id pstl_binds (cn_lhs convrs_fst) (cn_rhs convrs_lst)

    logMsg $ "Made new postulate:\n  " ++ prettyString new_postl
    modify (\st -> st { st_postldefs = new_postl : st_postldefs st})


-- fff :: CheckerM ()
-- fff = return ()

-- checkModule :: HscEnv -> CoreModule -> IO ()
-- checkModule hscEnv coreModule = 
--   do
--     (r, st) <- runStateT (runExceptT fff) emptyCheckerST
--     fillCheckerSt hscEnv coreModule <|> 
--     return ()


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
        mapM_ analyzeConvrs cnvrs
        madePostulate decl_id
        return decl_id
        --- TODO 
        -- replace throwError with createError and create in in place
        -- return decl_id


---- ANALYZE SINGLE CONVERSION
cmpCnvrs :: CoreExpr -> CoreExpr -> CheckerM ()
cmpCnvrs e_cntr e = do
  logMsg $
    "EXPR: " ++ prettyString e ++ "\n" ++
    "==?==\n" ++
    "CNTR: " ++ prettyString e_cntr ++ "\n" ++
    "Result: " ++ show (alphaEq e e_cntr)  ++ "\n"
  if alphaEq e e_cntr
    then return ()
    else throwError $ "Error. Not equal.\n  Expected: " ++ prettyString e_cntr ++ "\n  Got: " ++ prettyString e


analyzeConvrs :: Conversion -> CheckerM ()
analyzeConvrs Conversion{..} =
  do
    incCnvrsCounter
    (expr, control_expr, expr_info) <- case cn_info of
      L info -> return (cn_lhs, cn_rhs, info)
      R info -> return (cn_rhs, cn_lhs, info)
      QED    -> throwError "Unexpected converseion_info. Expected useful information. Get: QED"

    let analyzeExpr = case expr_info of
          Func  comment  -> analyzeFuncConv  comment 0
          Postl comment  -> analyzePostlConv comment
          FuncRec cmnt n -> analyzeFuncConv cmnt n
          Eta            -> analyzeEtaConv
          Beta           -> analyzeBetaConv
    (ce, e) <- analyzeExpr control_expr expr
    cmpCnvrs ce e
    -- return (new_expr, control_expr)
-- TODO no simplify subs or postulate. raw substing

---- just believe that this is enought
getFirstDiff :: CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr -> CoreExpr)
getFirstDiff = go ([], [])-- (suc, _) (suc, err) (err, _)
  where
    go cm_envs (Lam cntr_b cntr_body) (Lam b body) = do
      let new_cm_envs = bimap (cntr_b :) (b :) cm_envs
      res <- go new_cm_envs cntr_body body
      return $ updBuilder (Lam b .) res
    go cm_envs ce@(App _ _) e@(App _ _) = do
      let (cntr_f_typed, cntr_val_args) = collectValArgs ce
      let (f_typed, val_args) = collectValArgs e
      (checkEq cm_envs cntr_f_typed f_typed <&> (\(x, y) -> (mkCoreApps x val_args, y)))
        <|> goThroArgs cm_envs (App f_typed) cntr_val_args val_args
    --     <|> foldl (\(new_e, new_b) (ca, a) -> (go cm_envs ca a <&> (\(ee, bb) -> (ee, App (new_b . bb)))) <|> return (new_e, App (new_b a))) (e, App f) (zip cntr_val_args val_args)
    -- go cm_envs ce@(App _ (Type _)) e@(App _ (Type _)) = checkEq cm_envs ce e
    -- go cm_envs (App cntr_f cntr_arg) (App f arg) =
    --   (go cm_envs cntr_f f <&> updBuilder id . (\(nf, y) -> (App nf arg, y)))
    --     <|> (go cm_envs cntr_arg arg <&> updBuilder (App f .))
    go cm_envs ce e = checkEq cm_envs ce e

    goThroArgs :: ([Id], [Id]) -> (CoreExpr -> CoreExpr) -> [CoreExpr] -> [CoreExpr] -> CheckerM (CoreExpr, CoreExpr -> CoreExpr)
    goThroArgs cm_envs old_f (ca:cas) (a:as) =
      (go cm_envs ca a <&> \(new_a, new_a_bl) -> (new_a, (\new_arg -> mkCoreApps (old_f (new_a_bl new_arg)) as))) <|> goThroArgs cm_envs (App (old_f a)) cas as
    goThroArgs _ _ _ _ = throwError $ "No difference AAAAA"

    updBuilder updater (diff_expr, builder) = (diff_expr, updater builder)
    checkEq cm_envs ce e
      | alphaEqWithEnv cm_envs ce e = do
        logMsg $     "No difference.\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e
        throwError $ "No difference.\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e
      | otherwise    = do
        logMsg $ "Get diff:\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e ++ "\n"
        return (e, id)

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
    (diff_expr, builder) <- getFirstDiff control_expr expr
    logMsg $ "Evaluate Eta for expr:\n  " ++ prettyString diff_expr
    new_expr <- case diff_expr of
      (Lam v1 (App f (Var v2))) | v1 == v2 -> return f  -- TODO: check and fix
      _ -> throwError $ "Error in analyzeEtaConv:\n" ++ prettyString diff_expr
    return (control_expr, builder new_expr)

analyzeFuncConv :: String -> Integer -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzeFuncConv comment n control_expr expr =
  do
    decl_id <- gets st_declconvr_id
    logMsg $ "analyzeFuncConv for:" ++ prettyString decl_id
    (diff_expr, builder) <-
      if n <= 0
        then getFirstDiff control_expr expr
        else getNAppearance comment n expr
    logMsg $ "Evaluate func substitution for expr:\n  " ++ prettyString diff_expr
    subst_expr      <- substitute diff_expr
    let restr_expr   = builder subst_expr
    simpl_expr      <- simplifyBetaRed restr_expr
    return (control_expr, simpl_expr)

  where
    substitute e =
      do
        let (func, args) = collectArgs e
        func_id   <- checkComment func
        func_body <- getBodyByFuncId func_id

        let subst_func = easySubstFunc func func_id func_body
        return $ mkCoreApps subst_func args -- maybe mkApps

    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | getStrById func_id == comment = return func_id
      | otherwise  = throwError $ "Applied function_id does not match comment:\n" ++ prettyString func_id ++ "\nExpected: " ++ comment
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e

getBodyByFuncId :: Id -> CheckerM CoreExpr
getBodyByFuncId func_id =
  do
    func_defs <- gets st_funcdefs
    case lookup func_id func_defs of
      Just func_body -> return func_body
      Nothing        -> throwError $ "Function definition not found for:\n" ++ prettyString func_id

{- 
  when to do simplify and subst
  problem
    (m >>= return) `postulate` m
    expr = (m >>= return) >>= return

    (return a >>= k) `postulate` (k a)
    (return a >>= (\a1 -> (return a1 >>= k)))
    (\a1 -> (return a1 >>= k)) a              (return a >>= (\a1 -> k a1))
-}
analyzePostlConv :: String -> CoreExpr -> CoreExpr -> CheckerM (CoreExpr, CoreExpr)
analyzePostlConv comment control_expr expr =
  do
    (diff_expr, _) <- getFirstDiff control_expr expr
    d_id <- gets st_declconvr_id
    logMsg $ "POSTL_DIFF: " ++ prettyString d_id ++ "\n" ++ prettyString diff_expr
    postl_defs    <- gets st_postldefs
    declconv_defs <- gets st_declconvrs
    let matchedPstls = filter ((comment ==) . getStrById . pstl_id) postl_defs
    rule <- case matchedPstls of
      [pstl] -> return pstl
      (_:_)  -> throwError $ "Unexpected postulate. Found more than one matched with comment `" ++ comment ++ "`"
      []     -> throwError $ "Unexpected postulate. Not found match with comment `" ++ comment ++ "`" ++ "\nALL postuls:\n" ++ prettyString (map pstl_id postl_defs) ++ "\nOrder:\n" ++ prettyString (map fst declconv_defs)
    
    lookup_expr <- substRule [rule] expr
    logMsg $ "SUBST_RULE\n" ++ prettyString lookup_expr
    
    new_expr        <- simplifyFunc [rule] expr
    new_contrl_expr <- simplifyFunc [rule] control_expr
    let no_lets_expr = inlineLets new_expr
    return (new_contrl_expr, no_lets_expr)


---- SIMPLIFIERS
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

simplifyBetaRed :: CoreExpr -> CheckerM CoreExpr
simplifyBetaRed expr = go 0 expr
  where
    go n _ | n >= 3 = throwError $ "Unexpected expression. Expression needs to much beta-reductions. Default threshold = 3. Expr:\n" ++ prettyString expr
    go n e = do
      logMsg $ "TRY simplifyBetaRed n=" ++ show n
      let no_lets_expr = inlineLets $ simpleOptExpr defaultSimpleOpts e
      case find isBetaRedex (universe no_lets_expr) of
        Just _  -> go (n + 1) no_lets_expr
        Nothing -> return no_lets_expr

    isBetaRedex (App (Lam _ _) _) = True
    isBetaRedex _                 = False


simplifyFunc :: [PostlDef] -> CoreExpr -> CheckerM CoreExpr
simplifyFunc pstls expr = go 0 expr
  where
    go n _ | n >= 3 = throwError $ "Unexpected expression. Expression needs to much beta-reductions. Default threshold = 3. Expr:\n" ++ prettyString expr
    go n e = do
      hscEnv     <- gets st_hscenv
      logMsg $ "TRY simplify n=" ++ show n
      simplified <- liftIO $ simplifyFuncIO hscEnv pstls e
      let no_lets_expr = inlineLets simplified
      case find isBetaRedex (universe no_lets_expr) of
        Just _  -> go (n + 1) no_lets_expr
        Nothing -> return no_lets_expr

    isBetaRedex (App (Lam _ _) _) = True
    isBetaRedex _                 = False

simplifyFuncIO :: HscEnv -> [PostlDef] -> CoreExpr -> IO CoreExpr
simplifyFuncIO hscEnv pstls expr =
  do
    let opts   = initSimplifyExprOpts (hsc_dflags hscEnv) (hsc_IC hscEnv)
        logger = hsc_logger hscEnv

    euc <- initExternalUnitCache
    eps <- eucEPS euc

    let fam_envs =  ( eps_fam_inst_env eps
                    , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                    )

        -- simpl_env = mkSimplEnv (se_mode opts) fam_envs
        -- my_in_scope = getInScope simpl_env `extendInScopeSetSet` exprFreeVars expr
        -- my_env = setInScopeSet simpl_env my_in_scope
        rules = map pstl_rule pstls
        simpl_env = mkSimplEnv (se_mode opts) fam_envs
        ru_rhs_fv = map ruleRhsFreeVars rules
        fv_set    = foldl unionUniqSets (exprFreeVars expr) ru_rhs_fv
          -- TODO order IS IMPORTANT. WANT TO SAVE MODIFied
        fv_idInfo_set = fv_set `addListToUniqSet` map pstl_fid pstls
        my_in_scope   = getInScope simpl_env `extendInScopeSetSet` fv_idInfo_set
        my_env        = setInScopeSet simpl_env my_in_scope

        top_env_cfg = se_top_env_cfg opts
        read_eps_rules = eps_rule_base <$> eucEPS euc
        my_rule_env = (`addLocalRules` rules) . updExternalPackageRules emptyRuleEnv <$> read_eps_rules

    -- putStrLn $ "------MY-ENV-------"
    -- putStrLn $ showSDocUnsafe $ pprSimplEnv my_env
    -- putStrLn $ "------MY-ENV-------"
    let sz = exprSize expr
    (expr', _) <- initSmpl logger my_rule_env top_env_cfg sz $
                          simplExpr my_env expr

    if not (null rules)
      then
        if alphaEq expr' expr
          then putStrLn $ "NOT FIRED: " ++ show (map (prettyString . pstl_id) pstls)
          else putStrLn $ "RULE `" ++ show (map (prettyString . pstl_id) pstls) ++ "` FIRED"
      else putStrLn "NO rules"
    return expr'

substRule :: [PostlDef] -> CoreExpr -> CheckerM CoreExpr
substRule pstls expr = 
  do
    hscEnv <- gets st_hscenv
    let opts   = initSimplifyExprOpts (hsc_dflags hscEnv) (hsc_IC hscEnv)
        logger = hsc_logger hscEnv

    euc <- liftIO $ initExternalUnitCache
    eps <- liftIO $ eucEPS euc

    let fam_envs =  ( eps_fam_inst_env eps
                    , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                    )

        -- simpl_env = mkSimplEnv (se_mode opts) fam_envs
        -- my_in_scope = getInScope simpl_env `extendInScopeSetSet` exprFreeVars expr
        -- my_env = setInScopeSet simpl_env my_in_scope
        rules = map pstl_rule pstls
        simpl_env = mkSimplEnv (se_mode opts) fam_envs
        ru_rhs_fv = map ruleRhsFreeVars rules
        fv_set    = foldl unionUniqSets (exprFreeVars expr) ru_rhs_fv
          -- TODO order IS IMPORTANT. WANT TO SAVE MODIFied
        fv_idInfo_set = fv_set `addListToUniqSet` map pstl_fid pstls
        my_in_scope   = getInScope simpl_env `extendInScopeSetSet` fv_idInfo_set
        my_env        = setInScopeSet simpl_env my_in_scope

        top_env_cfg = se_top_env_cfg opts
        read_eps_rules = eps_rule_base <$> eucEPS euc
        my_rule_env = (`addLocalRules` rules) . updExternalPackageRules emptyRuleEnv <$> read_eps_rules

    let
      opts        = seRuleOpts my_env :: RuleOpts
      in_scope_env = getUnfoldingInRuleMatch my_env :: InScopeEnv
      act_fun      = activeRule (seMode my_env) :: Activation -> Bool
      rules_id_str = show $ map (prettyString . pstl_id) pstls
      rules = map pstl_rule pstls
      (Var f_target, args_targetgs) = collectArgs expr

    case lookupRule opts in_scope_env act_fun f_target args_targetgs rules of
      Nothing -> throwError $ "Rule `" ++ rules_id_str ++ "`not fired." ++ "\nRule:\n" ++ prettyString pstls ++ "\nExpr:\n" ++ prettyString expr
      Just (_, new_expr) -> do
          logMsg $ "Rule fired:" ++ rules_id_str
          return new_expr

-- simplExprGently env expr = do
--     expr1 <- simplExpr env (occurAnalyseExpr expr)
--     simplExpr env (occurAnalyseExpr expr1)

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

-- -- myM1
-- -- \ (@(m_aIR :: Type -> Type))
-- --   (@a_aIS)
-- --   (@b_aIT)
-- --   ($dMonad_aIU :: Monad m_aIR)
-- --   (a_azv :: a_aIS)
-- --   (k_azw :: a_aIS -> m_aIR b_aIT)

-- -- FREE VARS l_postl: App :: >>=
-- --   @m_aIR
-- --   $dMonad_aIU
-- --   @a_aIS
-- --   @b_aIT
-- --   (return @m_aIR $dMonad_aIU @a_aIS a_azv)
-- --   k_azw
-- -- FREE VARS        : {a_azv, k_azw, m_aIR, a_aIS, b_aIT, $dMonad_aIU}

-- -- FREE VARS expr.  : App :: >>=
-- --   @m_aMV
-- --   $dMonad_aMY
-- --   @(a_aMW -> b_aMX)
-- --   @b_aMX
-- --   (return @m_aMV $dMonad_aMY @(a_aMW -> b_aMX) g_azQ)
-- --   (\ (f_azS :: a_aMW -> b_aMX) ->
-- --      myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR)
-- -- FREE VARS        : {g_azQ, xs_azR, m_aMV, a_aMW, b_aMX, $dMonad_aMY, myLiftM}

-- -- m_aIR       == m_aMV
-- -- $dMonad_aIU == $dMonad_aMY
-- -- a_aIS       == (a_aMW -> b_aMX)
-- -- b_aIT.      == b_aMX
-- -- a_azv       == g_azQ
-- -- k_azw       == (\ (f_azS :: a_aMW -> b_aMX) -> myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR)

-- -- k_azw a_azv ==
-- --   (\ (f_azS :: a_aMW -> b_aMX) -> myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR) g_azQ
-- --   myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY g_azQ xs_azR