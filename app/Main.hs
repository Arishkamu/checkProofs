{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

module Main where

import GHC
import GHC.Paths (libdir)
import GHC.Core
import GHC.Driver.DynFlags ( gopt_set )
import GHC.Types.Literal (Literal(..))
import GHC.Types.Name.Occurrence (occNameString)

import Control.Monad.IO.Class (liftIO)
import Data.Generics.Uniplate.Data (universe)
import qualified Data.ByteString.Char8 as BS8
import Data.Functor

-- DEBUG
import GHC.Utils.Outputable

import AstInfo
import PrettyString


main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags' <- getSessionDynFlags
    let dflags = gopt_set dflags' Opt_EnableRewriteRules
    _ <- setSessionDynFlags dflags
    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example3.hs"
    coreMod <- compileToCoreModule filePath

    -- print CoreModule
    -- liftIO $ putStrLn "\n=== Core cm_types ===\n"
    -- liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_types coreMod)
    -- liftIO $ putStrLn "\n=== Core cm_binds ===\n"
    -- liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_binds coreMod)

    -- create State
    let astState = getState coreMod
    liftIO $ putStrLn "\n===== Collected AstState =====\n"
    liftIO $ putStrLn $ prettyString astState
    liftIO $ putStrLn "\n===== End AstState =====\n"
    let result = analyzeModule astState
    -- let result = analyzeConversions astState
    -- case result of
    --   Left err -> liftIO $ putStrLn $ "Error: " ++ err
    --   Right convrs -> do
    --     liftIO $ putStrLn "\n=== Simplify Analysis ===\n"
    --     liftIO $ printMy session convrs
    --     liftIO $ putStrLn "\n=== End ===\n"
    --     mapM_ (\(e1, e2) -> (liftIO (simplifyFunc session e1), e2)) convrs
    --     liftIO $ putStrLn $ map prettyPrintEqPairs $ map (\(e1, e2) -> (inlineLets e1, e2)) m


    liftIO $ putStrLn "\n===== The End: App/Main ====="


---- COLLECTING AST STATE
getState :: CoreModule -> CheckerST
getState CoreModule{..} = CheckerST {
  st_declconvrs = concatMap collectConvrs binds,
  st_funcdefs   = binds,
  st_postldefs  = concatMap collectPostls binds
}
  where
  binds    = flattenBinds cm_binds
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

collectPostls :: FuncDef -> [PostlDef]
collectPostls (f_id, f_body) = case pstl_rest of
  App (App (App (Var app_id) _) pstl_lhs) pstl_rhs | getStrById app_id == "postulate"
    -> [PostlDef f_id pstl_binds pstl_lhs pstl_rhs]
  _ -> []

  where
  (pstl_binds, pstl_rest) = collectBinders f_body

collectConvrs :: FuncDef -> [DeclConversions]
collectConvrs (f_id, f_body) = case map getConvrs pairs of
    []      -> []
    convrs  -> [(f_id, convrs)]
  where
  convrs = map getConvrs pairs
  argAddInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe f_body,
    "addInfo" <- [getStrById exprName] ]
  pairs  = zip argAddInfo (drop 1 argAddInfo)
  getConvrs ((lhe, c1), (rhe, _)) = Conversion lhe rhe (toSideExprInfo c1)
---- END COLLECTING AST STATE

---- UTILS
getStrById :: Id -> String
getStrById v = occNameString (getOccName v)

toSideExprInfo :: CoreExpr -> SideExprInfo
toSideExprInfo (App (App (App (Var expr_side) _) _) expr_info) = toSideInfo (toExprInfo expr_info)
  where
  toSideInfo
    | getStrById expr_side == "Left"  = Left
    | getStrById expr_side == "Right" = Right
  toExprInfo (Var v)
    | getStrById v == "Beta" = Beta
    | getStrById v == "Eta" = Eta
  toExprInfo (App (Var v_id) (App _ (Lit (LitString pack_str))))
    | getStrById v_id == "Func"  = Func $ BS8.unpack pack_str
    | getStrById v_id == "Postl" = Postl $ BS8.unpack pack_str
toSideExprInfo e = error $ "Unexpected expression structure for comment, expected a function application with a string literal argument.\nGot: " ++ prettyString e


-- onSnd :: (b -> c) -> (a, b) -> (a, c)
-- onSnd f (x, y) = (x, f y)

-- -- alphaEqExpr :: CoreExpr -> CoreExpr -> Bool
-- -- alphaEqExpr lhs rhs = (deBruijnize lhs) == (deBruijnize rhs)

-- assume that any variable in convertion is OR
-- in (\x ->) this convertion
-- global func
-- parametr for this function
alphaEq :: (Eq (DeBruijn a)) => a -> a -> Bool
alphaEq lhv rhv = deBruijnize lhv == deBruijnize rhv

-- checkArgTypes :: CoreExpr -> CoreExpr -> Bool
-- checkArgTypes (Type tl) (Type tr) = (deBruijnize tl) == (deBruijnize tr)
-- checkArgTypes _ _ = True
-- ---- END UTILS




logMsg :: String -> CheckerM ()
logMsg msg = liftIO $ putStrLn msg

-- incCounter :: CheckerM ()
-- incCounter = modify (\st -> st { counter = counter st + 1 })

analyzeModule :: HscEnv -> Module -> CheckerST -> Report
analyzeModule session mod checkerST =
  do
    map () (st_declconvrs checkerST)

analyzeConvrs :: HscEnv -> Module -> Conversion -> CheckerM (CoreExpr, CoreExpr)
analyzeConvrs session mod Conversion{..} =
  do
    let analyzeFirstDiff = case expr_info of
          Func  comment -> getFirstDiff (analyzeFuncConv  comment)
          Postl comment -> getFirstDiff (analyzePostlConv comment)
          Eta           -> getFirstDiff  analyzeEtaConv
          Beta          -> analyzeBetaConv
    new_expr <- analyzeFirstDiff control_expr expr
    return (new_expr, control_expr)

  where
    (expr, control_expr, expr_info) = case cn_info of
      Left  info -> (cn_lhe, cn_rhe, info)
      Right info -> (cn_rhe, cn_lhe, info)

getFirstDiff :: (CoreExpr -> CheckerM CoreExpr) -> CoreExpr -> CoreExpr -> CheckerM CoreExpr
getFirstDiff analyzer cntr_expr expr =
  case (cntr_expr, expr) of
    (Lam cntr_b cntr_body, Lam b body) -> do
      new_body <- getFirstDiff analyzer cntr_body body
      return $ Lam b new_body
    (App cntr_f cntr_arg,  App f arg)  ->
      getFirstDiff cntr_f f <|>
      (getFirstDiff cntr_arg arg <&> App f)
    (ec, c) 
      | alphaEq ec c -> throwError $ "No difference.\n  cntr_expr: " ++ prettyString ec ++ "\n       expr: " ++ prettyString e
      | otherwise    -> do
        logMsg $ "Get diff:\n  cntr_expr: " ++ prettyString ec ++ "\n       expr: " ++ prettyString e ++ "\n"
        analyzer ec c 


analyzeBetaConv :: CoreExpr -> CoreExpr -> Either String CoreExpr
analyzeBetaConv control_expr expr
  | alphaEq control_expr expr = Right expr -- TODO: check alphaEq
  | otherwise = Left "Not Beta equivalent"

analyzeEtaConv :: CoreExpr -> Either String CoreExpr
analyzeEtaConv expr = case expr of
  (Lam v1 (App f (Var v2))) | v1 == v2
    -> do
      logMsg $ "Evaluate Eta for expr:\n  " ++ prettyString expr 
      return f  -- TODO: check and fix
  _ -> throwError $ "Error in analyzeEtaConv:\n" ++ prettyPrint expr

analyzeFuncConv :: CoreExpr -> CheckerM CoreExpr
analyzeFuncConv 

-- analyzeFuncConv funcdefs comment expr = do
--   args <- getFuncArgs expr
--   checked <- checkComment comment args
--   substAndRestoreFunc funcdefs checked

-- printMy :: HscEnv -> [(CoreExpr, CoreExpr)] -> IO ()
-- printMy ses exprs = 
--   do
--     res <- mapM (printMyPair ses) exprs
--     putStrLn $ intercalate "\n" $ map prettyPrintEqPairs res
--     let onlyFalse = filter (\(e1, e2) -> not (alphaEq e1 e2)) res
--     putStrLn "---- Print only false:----\n"
--     putStrLn $ intercalate "\n" $ map prettyPrintEqPairs onlyFalse
--     putStrLn $ "Number of false: " ++ show (length onlyFalse) ++ "\n"

-- printMyPair :: HscEnv -> (CoreExpr, CoreExpr) -> IO (CoreExpr, CoreExpr)
-- printMyPair ses (x, y) = 
--   do
--     x1 <- simplifyFunc ses x
--     let x2 = inlineLets x1
--     return (x2, y)

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



-- ---- DEBUG
-- prettyPrintEqPairs :: (CoreExpr, CoreExpr) -> String
-- prettyPrintEqPairs (e1, e2) = 
--   "LHS: " ++ prettyPrint e1 ++ "\n" ++
--   "==?==\n" ++
--   "RHS: " ++ prettyPrint e2 ++ "\n" ++
--   "Result: " ++ show (alphaEq e1 e2)  ++ "\n"
-- ---- END DEBUG

-- ---- analyze
-- analyzeConversions :: AstInfo -> Either String [(CoreExpr, CoreExpr)]
-- analyzeConversions AstInfo{..} = analyze $ concatMap snd ast_declconvrs
--   where
--     analyze :: [Conversion] -> Either String [(CoreExpr, CoreExpr)]
--     analyze [] = Right []
--     analyze (x:xs) = analyzeConvr ast_funcdefs ast_postldefs x >>= 
--       \res -> analyze xs  >>= 
--         \rest -> Right (res : rest)

-- analyzeConvr :: [FuncDef] -> [PostlDef] -> Conversion -> Either String (CoreExpr, CoreExpr)
-- analyzeConvr funcdefs postldefs Conversion{..} = (
--   case expr_info of
--     Func comment  -> getFirstDiff    control_expr expr (analyzeFuncConv  funcdefs comment)
--     Postl comment -> getFirstDiff    control_expr expr (analyzePostlConv postldefs comment)
--     Eta           -> getFirstDiff    control_expr expr analyzeEtaConv
--     Beta          -> analyzeBetaConv control_expr expr)
--   >>= (\new_expr -> Right (new_expr, control_expr))
--   where
--     (expr, control_expr, expr_info) = case cn_info of
--       Left  info -> (cn_lhe, cn_rhe, info)
--       Right info -> (cn_rhe, cn_lhe, info)

-- getFirstDiff :: CoreExpr -> CoreExpr -> (CoreExpr -> Either String CoreExpr) -> Either String CoreExpr
-- getFirstDiff (Lam b_contr body_contr) (Lam b body) checker
--   = getFirstDiff body_contr body checker >>= \new_body -> Right (Lam b new_body)
--   -- TODO: check wisely. They can not be the same, but all others should
--   -- | alphaEq b_contr b = getFirstDiff body_contr body >>= \new_body -> Right (Lam b new_body) 
--   -- | otherwise = Left $ "Lambda:\n" ++ prettyPrint b ++ "\ndoes not match control lambda binder:\n" ++ prettyPrint b_contr 
-- getFirstDiff e1@(App f_contr arg_contr) e2@(App f arg) checker
--   | alphaEq f_contr f && checkArgTypes arg_contr arg     = getFirstDiff arg_contr arg checker >>= \new_arg -> Right (App f new_arg) 
--   | otherwise = trace ("GET DIFF :\ncontrol: " ++ prettyPrint e1 ++ "\nexprexp: " ++ prettyPrint e1 ++ "\n") $ checker e2
--   -- | otherwise = getFirstDiff f_contr f >>= \new_f -> Right (App new_f arg)
--   -- | otherwise = Left $ "Application:\n" ++ prettyPrint e1 ++ "\ndoes not match control lambda binder:\n" ++ prettyPrint e2 
-- getFirstDiff ec app@(App _ _) checker = trace ("GET DIFF :\ncontrol: " ++ prettyPrint ec ++ "\nexprexp: " ++ prettyPrint app  ++ "\n") $ checker app
-- getFirstDiff ec e checker = trace ("GET DIFF :\ncontrol: " ++ prettyPrint ec ++ "\nexprexp: " ++ prettyPrint e ++ "\n") $ checker e


-- analyzeEtaConv :: CoreExpr -> Either String CoreExpr
-- analyzeEtaConv (Lam v1 (App f (Var v2))) | v1 == v2 = Right f  -- TODO: check and fix
-- analyzeEtaConv expr = Left $ "analyzeEtaConv:\n" ++ prettyPrint expr

-- analyzeBetaConv :: CoreExpr -> CoreExpr -> Either String CoreExpr
-- analyzeBetaConv control_expr expr 
--   | alphaEq control_expr expr = Right expr -- TODO: check alphaEq
--   | otherwise = Left "Not Beta equivalent"

-- analyzeFuncConv :: [FuncDef] -> String -> CoreExpr -> Either String CoreExpr
-- analyzeFuncConv funcdefs comment expr = getFuncArgs expr 
--   >>= checkComment 
--   >>= substAndRestoreFunc funcdefs
--   where
--     -- checker :: CoreExpr -> CoreExpr -> Either String CoreExpr
--     -- checker = checkUntilRegex control_expr expr
--     --   >>= getFuncArgs 
--     --   >>= checkComment 
--     --   >>= substAndRestoreFunc funcdefs
--       -- >>= \new_expr -> Right [(new_expr, control_expr)]

--     -- checkRegex :: CoreExpr -> Either String CoreExpr
--     -- checkRegex app = getFuncArgs app 
--     --   >>= checkComment 
--     --   >>= substAndRestoreFunc funcdefs 
--     --   >>= \new_expr -> Right [(new_expr, control_expr)]
--       -- >>= simplifyFunc

--     getFuncArgs :: CoreExpr -> Either String [CoreExpr]
--     getFuncArgs expr = Right $ reverse $ getFunc expr
--       where
--         getFunc (App f a) = a : getFunc f
--         getFunc f = [f]

--     checkComment :: [CoreExpr] -> Either String [CoreExpr]
--     checkComment e@((Var func_id) : _) 
--       | getStrById func_id == comment = Right e
--       | otherwise = Left $ "First applied function_id does not match comment:\n" ++ prettyPrint func_id ++ "\nExpected: " ++ comment
--     checkComment (e:_) = Left $ "First applied not a function!\nGot: " ++ prettyPrint e
--     checkComment [] = Left $ "No function found in application!"

--     substAndRestoreFunc :: [FuncDef] -> [CoreExpr] -> Either String CoreExpr
--     substAndRestoreFunc funcdefs (func_var@(Var func_id) : args) = 
--       (case lookup func_id funcdefs of
--         Just func_body -> Right $ easySubstFunc func_var func_id func_body
--         Nothing        -> Left $ "Function definition not found for:\n" ++ prettyPrint func_id)
--       >>= \subst_f -> Right $ foldl App subst_f args
--     substAndRestoreFunc _ app = Left $ "Unexpected expression structure, expected a function application:\n" ++ prettyPrint app

--     -- simplifyFunc :: CoreExpr -> Either String CoreExpr
--     -- simplifyFunc = Right

-- analyzePostlConv :: [PostlDef] -> String -> CoreExpr -> Either String CoreExpr
-- analyzePostlConv postldefs comment expr = getPostl >>= substIfAlphaEq
--   where
--   matchedFuncs = filter (\(postl_id, _, _) -> getStrById postl_id == comment) postldefs
--   getPostl = case matchedFuncs of
--     [(_, l_postl, r_postl)] -> Right (l_postl, r_postl)
--     (_:_) -> Left $ "Unexpected postulate. Found more than one matched with comment `" ++ comment ++ "`"
--     []    -> Left $ "Unexpected postulate. Not found match with comment `" ++ comment ++ "`"

--   substIfAlphaEq (l_postl, r_postl) = trace (
--     "\nFREE VARS l_postl: " ++ prettyPrint l_postl ++ "\nFREE VARS        : " ++ showSDocUnsafe (ppr (exprFreeVars l_postl)) ++
--     "\nFREE VARS expr.  : " ++ prettyPrint expr ++ "\nFREE VARS        : " ++ showSDocUnsafe (ppr (exprFreeVars expr))) $ Right r_postl
--   -- TODO make meaningfull subst
--   -- TODO fix alpha_eq
--     -- | alphaEq l_postl expr = Right r_postl TODO fix alpha_eq
--     -- | otherwise = Left $ "Left side of postulate: " ++ prettyPrint l_postl ++ "\n don't match expr: " ++ prettyPrint expr


-- simplifyFunc :: HscEnv -> CoreExpr -> IO CoreExpr
-- simplifyFunc hscEnv expr = do
--   euc <- initExternalUnitCache
--   let dflags = hsc_dflags hscEnv
--   let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)
--   let logger = hsc_logger hscEnv

--   eps <- eucEPS euc
--   let fam_envs =  ( eps_fam_inst_env eps
--                   , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
--                   )

--       simpl_env = mkSimplEnv (se_mode opts) fam_envs
--       my_in_scope = (getInScope simpl_env) `extendInScopeSetSet` (exprFreeVars expr)
--       my_env = setInScopeSet simpl_env my_in_scope
--       -- my_env_two = GHC.Core.Opt.Simplify.Env.extendIdSubst my_env fnId (mkContEx my_env fnBody)
--       -- delOneVSet = delOneFromUniqSet (exprFreeVars expr) fnId
--       -- my_env_two = setInScopeSet my_env $ (getInScope my_env) `extendInScopeSetSet` delOneVSet

--       top_env_cfg = se_top_env_cfg opts
--       read_eps_rules = eps_rule_base <$> eucEPS euc
--       read_ruleenv = updExternalPackageRules emptyRuleEnv <$> read_eps_rules

--   let sz = exprSize expr
--   (expr', counts) <- initSmpl logger read_ruleenv top_env_cfg sz $
--                         simplExpr my_env expr
--   return expr'



-- easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
-- easySubstFunc expr fn_id fn_body = substExpr subst expr
--   where
--     delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id 
--     subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body

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
--     * prettyPrintBinds (cm_binds coreMod)
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