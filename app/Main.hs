{-# LANGUAGE RecordWildCards, FlexibleContexts, LambdaCase #-}

module Main where

import GHC
import GHC.Paths (libdir)
import GHC.Core
import GHC.Core.Map.Type (DeBruijn(..), deBruijnize)
import GHC.Core.Make (mkCoreApps) -- maybe mkApps
import GHC.Driver.DynFlags ( gopt_set )
import GHC.Driver.Env (mainModIs, hsc_HUE)
import GHC.Types.Literal (Literal(..))
import GHC.Types.Name.Occurrence (occNameString)
-- Subst
import GHC.Core.Subst (extendSubst, mkEmptySubst, substExpr)
import GHC.Core.FVs (exprFreeVars)
import GHC.Types.Var.Env (mkInScopeSet, extendInScopeSetSet)
import GHC.Types.Var.Set (delVarSet)

import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Lazy
import Control.Monad.Except
import Control.Applicative ((<|>))
import Data.Generics.Uniplate.Data (universe)
import qualified Data.ByteString.Char8 as BS8
import Data.Functor
-- import Data.List (isPrefixOf)

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
    liftIO $ analyzeModuleSt session astState
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

getModule :: HscEnv -> Module
getModule = mainModIs . hsc_HUE
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
logMsg msg = liftIO $ putStrLn $ "LOG\n" ++ msg

-- incCounter :: CheckerM ()
-- incCounter = modify (\st -> st { counter = counter st + 1 })

------ TODO-1
prettyStringEqPairs :: (CoreExpr, CoreExpr) -> String
prettyStringEqPairs (e1, e2) = 
  "LHS: " ++ prettyString e1 ++ "\n" ++
  "==?==\n" ++
  "RHS: " ++ prettyString e2 ++ "\n" ++
  "Result: " ++ show (alphaEq e1 e2)  ++ "\n"


analyzeModuleSt :: HscEnv -> CheckerST -> IO [()]
analyzeModuleSt session checkerST =

  do
    let (_, d1) = head (st_declconvrs checkerST)
    let c1 = head d1
    -- map analyzeConvrs (st_declconvrs checkerST)
    -- let initState = CheckerST 0

    -- (result, st) <- runStateT (runExceptT (analyzeConvrs c1)) checkerST
    -- putStrLn $ case result of 
    --   Left s -> "ERROR: " ++ s
    --   Right r -> prettyStringEqPairs r
    result <- mapM amb d1
    mapM fff result
  
  where
    amb a = runStateT (runExceptT (analyzeConvrs a)) checkerST
    fff (r, _) = putStrLn $ case r of 
      Left s -> "ERROR: " ++ s
      Right r -> prettyStringEqPairs r
    -- (m (a, s) -> n (b, s))
    -- m a -> (a -> m b) -> m b
-- analyzeModule :: HscEnv -> CheckerM String
-- analyzeModule = 
--   do
--     runStateT (mapStateT f m) initState = f (runStateT m initState)


------ TODO-2

---- ANALYZE SINGLE CONVERSION
analyzeConvrs :: Conversion -> CheckerM (CoreExpr, CoreExpr)
analyzeConvrs Conversion{..} =
  do
    let analyzeFirstDiff = case expr_info of
          Func  comment -> getFirstDiff (analyzeFuncConv  comment)
          Postl comment -> getFirstDiff (analyzePostlConv comment)
          Eta           -> getFirstDiff  analyzeEtaConv
          Beta          -> analyzeBetaConv
    new_expr <- analyzeFirstDiff control_expr expr
    return (new_expr, control_expr)
-- TODO no simplify subs or postulate. raw substing

  where
    (expr, control_expr, expr_info) = case cn_info of
      Left  info -> (cn_lhs, cn_rhs, info)
      Right info -> (cn_rhs, cn_lhs, info)

getFirstDiff :: (CoreExpr -> CheckerM CoreExpr) -> CoreExpr -> CoreExpr -> CheckerM CoreExpr
getFirstDiff analyzer = go -- (suc, _) (suc, err) (err, _)
  where 
    go (Lam cntr_b cntr_body) (Lam b body) = do
      new_body <- go cntr_body body
      return $ Lam b new_body
    go (App cntr_f cntr_arg)  (App f arg) = 
      go cntr_f f <|> (go cntr_arg arg <&> App f)
      --
      -- WHAT IF
      -- get expr=(f, [arg])
      -- f==cntr_f -> App f (go arg_lll)
      -- f!=cntr_f -> analyze expr
      --

      -- `catchError` 
      --   (\e -> do
      --     logMsg $ "Catches: " ++ e
      --     throwError e)
    go ce e
      | alphaEq ce e = throwError $ "No difference.\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e
      | otherwise    = do
        logMsg $ "Get diff:\n  cntr_expr: " ++ prettyString ce ++ "\n       expr: " ++ prettyString e ++ "\n"
        analyzer e


analyzeBetaConv :: CoreExpr -> CoreExpr -> CheckerM CoreExpr
analyzeBetaConv control_expr expr
  | alphaEq control_expr expr = return expr -- TODO: check alphaEq
  | otherwise = throwError "Not Beta equivalent"

analyzeEtaConv :: CoreExpr -> CheckerM CoreExpr
analyzeEtaConv expr = case expr of
  (Lam v1 (App f (Var v2))) | v1 == v2
    -> do
      logMsg $ "Evaluate Eta for expr:\n  " ++ prettyString expr
      return f  -- TODO: check and fix
  _ -> throwError $ "Error in analyzeEtaConv:\n" ++ prettyString expr

analyzeFuncConv :: String -> CoreExpr -> CheckerM CoreExpr
analyzeFuncConv comment expr =
  do
    let (func, args) = collectArgs expr
    func_id   <- checkComment func
    func_defs <- gets st_funcdefs

    subst_func <- case lookup func_id func_defs of
      Just func_body -> easySubstFunc func func_id func_body
      Nothing        -> throwError $ "Function definition not found for:\n" ++ prettyString func_id
    return $ mkCoreApps subst_func args -- maybe mkApps

  where
    checkComment :: CoreExpr -> CheckerM Id
    checkComment (Var func_id)
      | getStrById func_id == comment = return func_id
      | otherwise  = throwError $ "Applied function_id does not match comment:\n" ++ prettyString func_id ++ "\nExpected: " ++ comment
    checkComment e = throwError $ "Applied expression not a function call!\nGot: " ++ prettyString e

{- 
  when to do simplify and subst
  problem
    (m >>= return) `postulate` m
    expr = (m >>= return) >>= return

    (return a >>= k) `postulate` (k a)
    (return a >>= (\a1 -> (return a1 >>= k)))
    (\a1 -> (return a1 >>= k)) a              (return a >>= (\a1 -> k a1))
-}
analyzePostlConv :: String -> CoreExpr -> CheckerM CoreExpr
analyzePostlConv comment expr =
  do
    postl_defs <- gets st_postldefs
    let matchedPstls = filter ((comment ==) . getStrById . pstl_id) postl_defs
    case matchedPstls of
      [pstl] -> return $ pstl_rhs pstl
      (_:_)  -> throwError $ "Unexpected postulate. Found more than one matched with comment `" ++ comment ++ "`"
      []     -> throwError $ "Unexpected postulate. Not found match with comment `" ++ comment ++ "`"


---- SIMPLIFIERS
easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CheckerM CoreExpr
easySubstFunc expr fn_id fn_body = return $ substExpr subst expr
  where
    delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id
    subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body


-- simplifyFunc :: HscEnv -> [CoreRule] -> CoreExpr -> CheckerM CoreExpr
-- simplifyFunc hscEnv rules expr =
--   do
--     -- hscEnv <- gets st_hscenv
--     let opts   = initSimplifyExprOpts (hsc_dflags hscEnv) (hsc_IC hscEnv)
--         logger = hsc_logger hscEnv

--     euc <- initExternalUnitCache
--     eps <- eucEPS euc
--     let fam_envs =  ( eps_fam_inst_env eps
--                     , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
--                     )

--         simpl_env = mkSimplEnv (se_mode opts) fam_envs
--         my_in_scope = getInScope simpl_env `extendInScopeSetSet` exprFreeVars expr
--         my_env = setInScopeSet simpl_env my_in_scope

--         top_env_cfg = se_top_env_cfg opts
--         read_eps_rules = eps_rule_base <$> eucEPS euc
--         my_rule_env = (`addLocalRules` rules) . updExternalPackageRules emptyRuleEnv <$> read_eps_rules

--     let sz = exprSize expr
--     (expr', counts) <- initSmpl logger my_rule_env top_env_cfg sz $
--                           simplExpr my_env expr
--     return expr'


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