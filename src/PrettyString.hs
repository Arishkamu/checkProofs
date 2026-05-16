{-# LANGUAGE RecordWildCards, FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module PrettyString (PrettyString, prettyString, prettyStringReport, prettyStringExpr) where

import GHC.Core
import GHC.Types.Id
import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)
import GHC.Types.Name.Occurrence (occNameString)
import GHC.Types.Name (getOccName)

import Data.List (intercalate)
import Data.Data (toConstr)

import AstInfo
import ProofBase
import GHC.Builtin.Names (Uniquable(getUnique))

class PrettyString a where
  prettyStringIdent :: Int -> a -> String
--   prettyStringIdent ident x = showSDocUnsafe (ppr x)

prettyString :: (PrettyString a) => a -> String
prettyString = prettyStringIdent 0

bslN :: Int -> String
bslN ident = "\n" ++ replicate ident ' '

prettyStringStrs :: Int -> [String] -> String
prettyStringStrs ident = intercalate (bslN ident)

-- instance (PrettyString a) => PrettyString (GenLocated SrcSpanAnnA a) where
--   rettyString (L _ x) = rettyString x

-- instance (Outputable a) => PrettyString Id where
--   prettyStringIdent _ x = "\n" ++ replicate ident ' ' ++ showSDocUnsafe (ppr x)

instance PrettyString Id where
  prettyStringIdent _ x = "ID: " ++ showSDocUnsafe (ppr x)

-- instance PrettyString (GenLocated SrcSpanAnnN Id) where
--   rettyString (L _ x) = rettyString x

instance PrettyString ExprInfo where
    prettyStringIdent _ expr_info = case expr_info of
        Decl  comment  -> "Decl: "  ++ comment
        DeclRec cmnt n -> "DeclRec: "  ++ cmnt ++ show n
        Prop comment   -> "Prop: " ++ comment
        Inst comment   -> "Inst: " ++ comment
        Beta           -> "Beta reduction"
        Eta            -> "Eta reduction"

instance PrettyString Conversion where
  prettyStringIdent ident Conversion{..} = 
    prettyStringIdent 0 cn_info ++ " :: "
    ++ bslN (ident + 2) ++ "l: " ++ prettyStringIdent 0 cn_lhs
    ++ bslN (ident + 2) ++ "r: " ++ prettyStringIdent 0 cn_rhs
    -- ++ showSDocUnsafe (ppr cn_lhe) ++ " => " ++ showSDocUnsafe (ppr cn_rhe) 
    -- ++
    -- bslN ident       ++ "Different constructors: " ++ show (toConstr lDiffCN) ++ " vs " ++ show (toConstr rDiffCN) ++
    -- bslN (ident + 2) ++ "l: " ++ rettyString lDiffCN ++ 
    -- bslN (ident + 2) ++ "r: " ++ rettyString rDiffCN

instance PrettyString PostlDef where
  prettyStringIdent ident PostlDef{..} = 
    bslN ident ++ "Postl_ID :: "  ++ prettyStringIdent 0 pstl_id ++
    bslN ident ++ "Postl_rule:\n" ++ prettyStringIdent 0 pstl_rule
-- instance PrettyString PostlDef where
-- prettyStringIdent ident PostlDef{..} = 
--   bslN ident ++ "Postl_ID :: " ++ prettyStringIdent 0 pstl_id ++
--   bslN ident ++ "Binds:" ++ prettyStringIdent (ident + 2) pstl_binds ++
--   bslN (ident + 2) ++ "l_pstl: " ++ prettyStringIdent 0 pstl_lhs ++
--   bslN (ident + 2) ++ "r_pstl: " ++ prettyStringIdent 0 pstl_rhs

instance PrettyString CheckerST where
  prettyStringIdent :: Int -> CheckerST -> String
  prettyStringIdent ident CheckerST{..} =
    "===== AstInfo =====" 
    ++ bslN ident ++ "ST_declconvrs:"  ++ prettyStringStrs  (ident + 2) (concatMap makePretty st_declconvrs)  
    ++ bslN ident ++ "ST_funcDefs:"    ++ prettyStringIdent (ident + 2) st_funcdefs
    ++ bslN ident ++ "ST_postlDefs:"   ++ prettyStringIdent (ident + 2) st_postldefs

    where
    makePretty (decl, convrs) =
        (bslN (ident + 2) ++ "DeclName: " ++  prettyStringIdent (ident + 2) decl) 
        : map (prettyStringIdent (ident + 4)) convrs

-- -- Represent: LHsBindLR GhcTc
-- --instance PrettyString (HsBindLR GhcTc GhcTc) where
-- --  prettyString (L _ bind) = prettyString bind

prettyStringBinds :: [FuncDef] -> String
prettyStringBinds binds = intercalate (bslN 2) $ map prettyStringBind binds
  where
    prettyStringBind (fnId, fnBody) = "Function: " ++ prettyString fnId ++ "\nBody: " ++ prettyStringExpr fnBody

prettyStringExpr :: CoreExpr -> String
prettyStringExpr expr = case expr of
  Lam args body -> "Lam: " ++ "\n    " ++ showSDocUnsafe (ppr args) ++ "\n" ++ prettyStringExpr body
  App f arg -> "App: " ++ prettyStringExpr f ++ "\n to " ++ prettyStringExpr arg
  Var v -> "Var: " ++ showSDocUnsafe (ppr v) 
  _ -> "NotImpl: " ++ showSDocUnsafe (ppr expr)

instance PrettyString CoreBind where
  prettyStringIdent ident bind = prettyStringIdent ident $ flattenBinds [bind]
-- instance PrettyString CoreBind where
--     prettyStringIdent ident (NonRec v expr) =
--       "NonRec: " ++ prettyStringIdent (ident + 2) v 
--     --   ++ "\n" ++ prettyStringIdent (ident + 2) expr
--     prettyStringIdent ident (Rec vExprs) =
--       "Rec: " ++ intercalate (bslN (ident + 2)) (map (\(v, e) -> prettyStringIdent (ident + 4) v {- ++ "\n" ++ prettyStringIdent (ident + 4) e -}) vExprs)

-- instance PrettyString (HsBindLR GhcTc GhcTc) where
--   prettyString bind =
-- --  show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))
--     case bind of
--       fb@FunBind{ fun_matches = mg } -> "FUNBIND: " ++ "\nID:" ++ showSDocUnsafe (ppr (unLoc (fun_id fb))) ++ "\n" ++ (showSDocUnsafe (ppr bind))
-- --      analyzeMatchGroup mg
-- --          PatBind{} -> []
-- --          VarBind{} ->
-- --          PatSynBind{} -> "PatSynBind"
--       (XHsBindsLR a) -> "XHsBindsLR" ++ " :: " ++ prettyString (abs_binds a)
--       _ -> show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))

instance PrettyString CoreExpr where
--   prettyStringIdent _ (App f arg) = "APP " ++ " :: " ++ "\nF: " ++ (showSDocUnsafe (ppr f)) ++ "\nA: " ++ (showSDocUnsafe (ppr arg))
  prettyStringIdent _ expr = show (toConstr expr) ++ " :: " ++ showSDocUnsafe (ppr expr)

instance PrettyString CoreRule where
--   prettyStringIdent _ (App f arg) = "APP " ++ " :: " ++ "\nF: " ++ (showSDocUnsafe (ppr f)) ++ "\nA: " ++ (showSDocUnsafe (ppr arg))
  prettyStringIdent _ rule = showSDocUnsafe (ppr rule)

instance PrettyString SideExprInfo where
  prettyStringIdent ident (L l)  = "L-" ++ prettyStringIdent ident l
  prettyStringIdent ident (R r) = "R-" ++ prettyStringIdent ident r
  prettyStringIdent _ QED = "QED"
  prettyStringIdent _ Postulate = "Postulate"

-- type Report = ([Id], [String])
prettyStringReport :: Report -> String
prettyStringReport (succs, fails) = 
  "\n----- REPORT -----" ++ "\n" ++
  "Succsessfully proved:" ++ "\n" ++
  "  " ++ intercalate "\n  " (map (occNameString . getOccName) succs) ++ "\n" ++
  "Failures proved:" ++ "\n" ++
  "  " ++ intercalate (bslN 2) fails ++ "\n"


instance (PrettyString a, PrettyString b) => PrettyString (a, b) where
  prettyStringIdent ident (x, y) = bslN ident ++ "(" 
    ++ "\n" ++ prettyStringIdent (ident + 2) x 
    ++ "\n" ++ prettyStringIdent (ident + 2) y
    ++ bslN ident ++ ")"

instance (PrettyString a, PrettyString b, PrettyString c) => PrettyString (a, b, c) where
  prettyStringIdent ident (x, y, z) = bslN ident ++ "(" 
    ++ "\n" ++ prettyStringIdent (ident + 2) x 
    ++ "\n" ++ prettyStringIdent (ident + 2) y 
    ++ "\n" ++ prettyStringIdent (ident + 2) z 
    ++ bslN ident ++ ")"


instance (PrettyString a) => PrettyString [a] where
  prettyStringIdent ident as = intercalate (bslN ident) $ map (prettyStringIdent (ident + 2)) as

instance (PrettyString a) => PrettyString (Either String a) where
  prettyStringIdent ident (Left e)  = "Either-Left:"  ++ bslN (ident + 2) ++ e
  prettyStringIdent ident (Right a) = "Either-Right:" ++ bslN (ident + 2) ++ prettyString a

instance (PrettyString a) => PrettyString (Maybe a) where
  prettyStringIdent _ Nothing  = "Nothing"
  prettyStringIdent _ (Just a) = "Just" ++ prettyString a



-- instance (PrettyString a) => PrettyString (Bag a) where
--   prettyString = prettyString . bagToList
---- PrettyString