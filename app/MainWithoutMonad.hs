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

-- Debug
import Data.Data (toConstr)
import Debug.Trace
import GHC.Types.Unique
import Data.Either (fromRight)
import Data.List (intercalate)
import GHC.Utils.Outputable (showSDocUnsafe, ppr)

import PrettyPrint
import AstInfo

myTrace :: (PrettyPrint a) => String -> a -> a 
myTrace str v = trace ("My trace-str:" ++ str ++ "\n" ++ prettyPrint v ++ "\n") v

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    _ <- setSessionDynFlags dflags
    session <- getSession

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example3.hs"
    coreMod <- compileToCoreModule filePath

    -- TODO: collectModule no dif just yet
    liftIO $ putStrLn "\n=== Core cm_types ===\n"
    liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_types coreMod)
    let astInfo = collectModule coreMod
    liftIO $ putStrLn "\n===== Collected AstInfo =====\n"
    liftIO $ putStrLn $ prettyPrint astInfo
    liftIO $ putStrLn "\n===== End AstInfo =====\n"
    let result = analyzeConversions astInfo
    case result of
      Left err -> liftIO $ putStrLn $ "Error: " ++ err
      Right convrs -> do
        liftIO $ putStrLn "\n=== Simplify Analysis ===\n"
        liftIO $ printMy session convrs
        -- liftIO $ putStrLn "\n=== End ===\n"
        -- mapM_ (\(e1, e2) -> (liftIO (simplifyFunc session e1), e2)) convrs
        -- liftIO $ putStrLn $ map prettyPrintEqPairs $ map (\(e1, e2) -> (inlineLets e1, e2)) m


    liftIO $ putStrLn "\n===== The End: App/Main ====="

printMy :: HscEnv -> [(CoreExpr, CoreExpr)] -> IO ()
printMy ses exprs = 
  do
    res <- mapM (printMyPair ses) exprs
    putStrLn $ intercalate "\n" $ map prettyPrintEqPairs res
    let onlyFalse = filter (\(e1, e2) -> not (alphaEq e1 e2)) res
    putStrLn "---- Print only false:----\n"
    putStrLn $ intercalate "\n" $ map prettyPrintEqPairs onlyFalse
    putStrLn $ "Number of false: " ++ show (length onlyFalse) ++ "\n"

printMyPair :: HscEnv -> (CoreExpr, CoreExpr) -> IO (CoreExpr, CoreExpr)
printMyPair ses (x, y) = 
  do
    x1 <- simplifyFunc ses x
    let x2 = inlineLets x1
    return (x2, y)

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

---- COLLECTING AST INFO
collectModule :: CoreModule -> AstInfo
collectModule CoreModule{..} = AstInfo {
  ast_declconvrs = map (onSnd collectExpr) binds,
  ast_funcdefs   = binds,
  ast_postldefs  = postulates
} 
  where
  binds      = flattenBinds cm_binds
  postulates = [ (f_id, l_postl, r_postl) |
    (f_id, f_expr) <- binds,
    (App (App (App (Var app_id) _) l_postl) r_postl) <- universe f_expr,
    "postulate" <- [getStrById app_id] ]

collectExpr :: CoreExpr -> [Conversion]
collectExpr expr = map getConvrs pairs where
  argAddInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe expr,
    "addInfo" <- [getStrById exprName] ]
  pairs  = zip argAddInfo (drop 1 argAddInfo)
  getConvrs ((lhe, c1), (rhe, _)) = Conversion lhe rhe (toSideExprInfo c1)

---- END COLLECTING AST INFO

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
toSideExprInfo e = error $ "Unexpected expression structure for comment, expected a function application with a string literal argument.\nGot: " ++ prettyPrint e


onSnd :: (b -> c) -> (a, b) -> (a, c)
onSnd f (x, y) = (x, f y)

-- alphaEqExpr :: CoreExpr -> CoreExpr -> Bool
-- alphaEqExpr lhs rhs = (deBruijnize lhs) == (deBruijnize rhs)

alphaEq :: (Eq (DeBruijn a)) => a -> a -> Bool
alphaEq lhv rhv = (deBruijnize lhv) == (deBruijnize rhv)

checkArgTypes :: CoreExpr -> CoreExpr -> Bool
checkArgTypes (Type tl) (Type tr) = (deBruijnize tl) == (deBruijnize tr)
checkArgTypes _ _ = True
---- END UTILS


---- DEBUG
prettyPrintEqPairs :: (CoreExpr, CoreExpr) -> String
prettyPrintEqPairs (e1, e2) = 
  "LHS: " ++ prettyPrint e1 ++ "\n" ++
  "==?==\n" ++
  "RHS: " ++ prettyPrint e2 ++ "\n" ++
  "Result: " ++ show (alphaEq e1 e2)  ++ "\n"
---- END DEBUG

---- analyze
analyzeConversions :: AstInfo -> Either String [(CoreExpr, CoreExpr)]
analyzeConversions AstInfo{..} = analyze $ concatMap snd ast_declconvrs
  where
    analyze :: [Conversion] -> Either String [(CoreExpr, CoreExpr)]
    analyze [] = Right []
    analyze (x:xs) = analyzeConvr ast_funcdefs ast_postldefs x >>= 
      \res -> analyze xs  >>= 
        \rest -> Right (res : rest)

analyzeConvr :: [FuncDef] -> [PostlDef] -> Conversion -> Either String (CoreExpr, CoreExpr)
analyzeConvr funcdefs postldefs Conversion{..} = (
  case expr_info of
    Func comment  -> getFirstDiff    control_expr expr (analyzeFuncConv  funcdefs comment)
    Postl comment -> getFirstDiff    control_expr expr (analyzePostlConv postldefs comment)
    Eta           -> getFirstDiff    control_expr expr analyzeEtaConv
    Beta          -> analyzeBetaConv control_expr expr)
  >>= (\new_expr -> Right (new_expr, control_expr))
  where
    (expr, control_expr, expr_info) = case cn_info of
      Left  info -> (cn_lhe, cn_rhe, info)
      Right info -> (cn_rhe, cn_lhe, info)

getFirstDiff :: CoreExpr -> CoreExpr -> (CoreExpr -> Either String CoreExpr) -> Either String CoreExpr
getFirstDiff (Lam b_contr body_contr) (Lam b body) checker
  = getFirstDiff body_contr body checker >>= \new_body -> Right (Lam b new_body)
  -- TODO: check wisely. They can not be the same, but all others should
  -- | alphaEq b_contr b = getFirstDiff body_contr body >>= \new_body -> Right (Lam b new_body) 
  -- | otherwise = Left $ "Lambda:\n" ++ prettyPrint b ++ "\ndoes not match control lambda binder:\n" ++ prettyPrint b_contr 
getFirstDiff e1@(App f_contr arg_contr) e2@(App f arg) checker
  | alphaEq f_contr f && checkArgTypes arg_contr arg     = getFirstDiff arg_contr arg checker >>= \new_arg -> Right (App f new_arg) 
  | otherwise = trace ("GET DIFF :\ncontrol: " ++ prettyPrint e1 ++ "\nexprexp: " ++ prettyPrint e1 ++ "\n") $ checker e2
  -- | otherwise = getFirstDiff f_contr f >>= \new_f -> Right (App new_f arg)
  -- | otherwise = Left $ "Application:\n" ++ prettyPrint e1 ++ "\ndoes not match control lambda binder:\n" ++ prettyPrint e2 
getFirstDiff ec app@(App _ _) checker = trace ("GET DIFF :\ncontrol: " ++ prettyPrint ec ++ "\nexprexp: " ++ prettyPrint app  ++ "\n") $ checker app
getFirstDiff ec e checker = trace ("GET DIFF :\ncontrol: " ++ prettyPrint ec ++ "\nexprexp: " ++ prettyPrint e ++ "\n") $ checker e
 

analyzeEtaConv :: CoreExpr -> Either String CoreExpr
analyzeEtaConv (Lam v1 (App f (Var v2))) | v1 == v2 = Right f  -- TODO: check and fix
analyzeEtaConv expr = Left $ "analyzeEtaConv:\n" ++ prettyPrint expr

analyzeBetaConv :: CoreExpr -> CoreExpr -> Either String CoreExpr
analyzeBetaConv control_expr expr 
  | alphaEq control_expr expr = Right expr -- TODO: check alphaEq
  | otherwise = Left "Not Beta equivalent"

analyzeFuncConv :: [FuncDef] -> String -> CoreExpr -> Either String CoreExpr
analyzeFuncConv funcdefs comment expr = getFuncArgs expr 
  >>= checkComment 
  >>= substAndRestoreFunc funcdefs
  where
    -- checker :: CoreExpr -> CoreExpr -> Either String CoreExpr
    -- checker = checkUntilRegex control_expr expr
    --   >>= getFuncArgs 
    --   >>= checkComment 
    --   >>= substAndRestoreFunc funcdefs
      -- >>= \new_expr -> Right [(new_expr, control_expr)]
   
    -- checkRegex :: CoreExpr -> Either String CoreExpr
    -- checkRegex app = getFuncArgs app 
    --   >>= checkComment 
    --   >>= substAndRestoreFunc funcdefs 
    --   >>= \new_expr -> Right [(new_expr, control_expr)]
      -- >>= simplifyFunc
    
    getFuncArgs :: CoreExpr -> Either String [CoreExpr]
    getFuncArgs expr = Right $ reverse $ getFunc expr
      where
        getFunc (App f a) = a : getFunc f
        getFunc f = [f]
    
    checkComment :: [CoreExpr] -> Either String [CoreExpr]
    checkComment e@((Var func_id) : _) 
      | getStrById func_id == comment = Right e
      | otherwise = Left $ "First applied function_id does not match comment:\n" ++ prettyPrint func_id ++ "\nExpected: " ++ comment
    checkComment (e:_) = Left $ "First applied not a function!\nGot: " ++ prettyPrint e
    checkComment [] = Left $ "No function found in application!"

    substAndRestoreFunc :: [FuncDef] -> [CoreExpr] -> Either String CoreExpr
    substAndRestoreFunc funcdefs (func_var@(Var func_id) : args) = 
      (case lookup func_id funcdefs of
        Just func_body -> Right $ easySubstFunc func_var func_id func_body
        Nothing        -> Left $ "Function definition not found for:\n" ++ prettyPrint func_id)
      >>= \subst_f -> Right $ foldl App subst_f args
    substAndRestoreFunc _ app = Left $ "Unexpected expression structure, expected a function application:\n" ++ prettyPrint app

    -- simplifyFunc :: CoreExpr -> Either String CoreExpr
    -- simplifyFunc = Right

analyzePostlConv :: [PostlDef] -> String -> CoreExpr -> Either String CoreExpr
analyzePostlConv postldefs comment expr = getPostl >>= substIfAlphaEq
  where
  matchedFuncs = filter (\(postl_id, _, _) -> getStrById postl_id == comment) postldefs
  getPostl = case matchedFuncs of
    [(_, l_postl, r_postl)] -> Right (l_postl, r_postl)
    (_:_) -> Left $ "Unexpected postulate. Found more than one matched with comment `" ++ comment ++ "`"
    []    -> Left $ "Unexpected postulate. Not found match with comment `" ++ comment ++ "`"
  
  substIfAlphaEq (l_postl, r_postl) = trace (
    "\nFREE VARS l_postl: " ++ prettyPrint l_postl ++ "\nFREE VARS        : " ++ showSDocUnsafe (ppr (exprFreeVars l_postl)) ++
    "\nFREE VARS expr.  : " ++ prettyPrint expr ++ "\nFREE VARS        : " ++ showSDocUnsafe (ppr (exprFreeVars expr))) $ Right r_postl
  -- TODO make meaningfull subst
  -- TODO fix alpha_eq
    -- | alphaEq l_postl expr = Right r_postl TODO fix alpha_eq
    -- | otherwise = Left $ "Left side of postulate: " ++ prettyPrint l_postl ++ "\n don't match expr: " ++ prettyPrint expr


simplifyFunc :: HscEnv -> CoreExpr -> IO CoreExpr
simplifyFunc hscEnv expr = do
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

  let sz = exprSize expr
  (expr', counts) <- initSmpl logger read_ruleenv top_env_cfg sz $
                        simplExpr my_env expr
  return expr'



easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubstFunc expr fn_id fn_body = substExpr subst expr
  where
    delFunFV = mkInScopeSet $ delVarSet (exprFreeVars expr) fn_id 
    subst = extendSubst (mkEmptySubst delFunFV) fn_id fn_body

{- TODO:
    * collectModule no dif just yet
    * analyze each conversion separatly
        * Chcek comment. 
        * if Func 
            * take correct hand-side
            * find first applied function: 
                * it could be inside lam 
                * compare that before that alphaEq
            * Check that function coresponds with comment
            * Find defenition for func
            * subst and restore function 
            * simplify ? (restored function) (whole expr) 
            * letinlined 
            * compare alphaEq
        * if Beta
            * compare alphaEq
    * prettyPrintBinds (cm_binds coreMod)
-}



{-
  Context: 
    variables with types or Types
    free variables?
  
  Variables at the moment:
    global
    params

  wrap in monad
    except
    store context
  
  TODO make meaningfull subst
    a==b
    k==(\x = expr expr expr)

    k a ==> (\x = expr expr expr) b

    expr_l ==> (\x y -> expr_l) == (\x y -> expr_r) <== expr_r
    expr_o ==> (\x y -> expr_o) x_o y_o

    expr_o ==> (\x y -> expr_o) x_o y_o ==> (\x y -> (\x y -> expr_l)) x_o y_o ==> 
    (\x_o y_o -> expr_l) ==> (\x_o y_o -> expr_r) ==> expr_r

  TWO STEPS
    match all variables from expr_o to expr_l (expr_l==expr_o)
    subst all variables into expr_r
-}

-- myM1
-- \ (@(m_aIR :: Type -> Type))
--   (@a_aIS)
--   (@b_aIT)
--   ($dMonad_aIU :: Monad m_aIR)
--   (a_azv :: a_aIS)
--   (k_azw :: a_aIS -> m_aIR b_aIT)

-- FREE VARS l_postl: App :: >>=
--   @m_aIR
--   $dMonad_aIU
--   @a_aIS
--   @b_aIT
--   (return @m_aIR $dMonad_aIU @a_aIS a_azv)
--   k_azw
-- FREE VARS        : {a_azv, k_azw, m_aIR, a_aIS, b_aIT, $dMonad_aIU}

-- FREE VARS expr.  : App :: >>=
--   @m_aMV
--   $dMonad_aMY
--   @(a_aMW -> b_aMX)
--   @b_aMX
--   (return @m_aMV $dMonad_aMY @(a_aMW -> b_aMX) g_azQ)
--   (\ (f_azS :: a_aMW -> b_aMX) ->
--      myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR)
-- FREE VARS        : {g_azQ, xs_azR, m_aMV, a_aMW, b_aMX, $dMonad_aMY, myLiftM}

-- m_aIR       == m_aMV
-- $dMonad_aIU == $dMonad_aMY
-- a_aIS       == (a_aMW -> b_aMX)
-- b_aIT.      == b_aMX
-- a_azv       == g_azQ
-- k_azw       == (\ (f_azS :: a_aMW -> b_aMX) -> myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR)

-- k_azw a_azv ==
--   (\ (f_azS :: a_aMW -> b_aMX) -> myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY f_azS xs_azR) g_azQ
--   myLiftM @m_aMV @a_aMW @b_aMX $dMonad_aMY g_azQ xs_azR
