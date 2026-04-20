{-# LANGUAGE RecordWildCards, FlexibleInstances #-}
module PrettyPrint (PrettyPrint, prettyPrint) where

import GHC.Core
import GHC.Types.Id
import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)

import Data.List (intercalate)
import Data.Data (toConstr)

import AstInfo

class PrettyPrint a where
  prettyPrintIdent :: Int -> a -> String
--   prettyPrintIdent ident x = showSDocUnsafe (ppr x)

prettyPrint :: (PrettyPrint a) => a -> String
prettyPrint = prettyPrintIdent 0

bslN :: Int -> String
bslN ident = "\n" ++ replicate ident ' '

prettyPrintStrs :: Int -> [String] -> String
prettyPrintStrs ident = intercalate (bslN ident)

-- instance (PrettyPrint a) => PrettyPrint (GenLocated SrcSpanAnnA a) where
--   prettyPrint (L _ x) = prettyPrint x

-- instance (Outputable a) => PrettyPrint Id where
--   prettyPrintIdent _ x = "\n" ++ replicate ident ' ' ++ showSDocUnsafe (ppr x)

instance PrettyPrint Id where
  prettyPrintIdent _ x = "ID: " ++ showSDocUnsafe (ppr x)

-- instance PrettyPrint (GenLocated SrcSpanAnnN Id) where
--   prettyPrint (L _ x) = prettyPrint x

instance PrettyPrint Conversion where
  prettyPrintIdent ident Conversion{..} = 
    comment ++ " :: " ++ showSDocUnsafe (ppr lhs) ++ " => " ++ showSDocUnsafe (ppr rhs) ++
    bslN ident       ++ "Different constructors: " ++ show (toConstr lDiff) ++ " vs " ++ show (toConstr rDiff) ++
    bslN (ident + 2) ++ "l: " ++ prettyPrint lDiff ++ 
    bslN (ident + 2) ++ "r: " ++ prettyPrint rDiff

instance PrettyPrint AstInfo where
  prettyPrintIdent ident AstInfo{..} =
    "===== AstInfo =====" 
    ++ bslN ident ++ "DeclConvrs:" ++ prettyPrintStrs  (ident + 2) (concatMap makePretty declConvrs)  
    ++ bslN ident ++ "FunDefs:"    ++ prettyPrintIdent (ident + 2) (map fst funcDefs)

    where
    makePretty (decl, convrs) = (
        (bslN (ident + 2) ++ "DeclName: " ++  prettyPrintIdent (ident + 2) decl) 
        : map (prettyPrintIdent (ident + 4)) convrs)

-- -- Represent: LHsBindLR GhcTc
-- --instance PrettyPrint (HsBindLR GhcTc GhcTc) where
-- --  prettyPrint (L _ bind) = prettyPrint bind

-- instance PrettyPrint CoreBind where
--     prettyPrintIdent ident (NonRec v expr) =
--       "NonRec: " ++ prettyPrintIdent (ident + 2) v 
--     --   ++ "\n" ++ prettyPrintIdent (ident + 2) expr
--     prettyPrintIdent ident (Rec vExprs) =
--       "Rec: " ++ intercalate (bslN (ident + 2)) (map (\(v, e) -> prettyPrintIdent (ident + 4) v {- ++ "\n" ++ prettyPrintIdent (ident + 4) e -}) vExprs)

-- instance PrettyPrint (HsBindLR GhcTc GhcTc) where
--   prettyPrint bind =
-- --  show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))
--     case bind of
--       fb@FunBind{ fun_matches = mg } -> "FUNBIND: " ++ "\nID:" ++ showSDocUnsafe (ppr (unLoc (fun_id fb))) ++ "\n" ++ (showSDocUnsafe (ppr bind))
-- --      analyzeMatchGroup mg
-- --          PatBind{} -> []
-- --          VarBind{} ->
-- --          PatSynBind{} -> "PatSynBind"
--       (XHsBindsLR a) -> "XHsBindsLR" ++ " :: " ++ prettyPrint (abs_binds a)
--       _ -> show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))

instance PrettyPrint CoreExpr where
  prettyPrintIdent _ expr = show (toConstr expr) ++ " :: " ++ (showSDocUnsafe (ppr expr))

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a, b) where
  prettyPrintIdent ident (x, y) = "(\n" ++ prettyPrintIdent (ident + 2) x ++ "\n" ++ prettyPrintIdent (ident + 2) y ++ bslN ident ++ ")"

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrintIdent ident as = intercalate (bslN ident) $ map (prettyPrintIdent (ident + 2)) as

-- instance (PrettyPrint a) => PrettyPrint (Bag a) where
--   prettyPrint = prettyPrint . bagToList