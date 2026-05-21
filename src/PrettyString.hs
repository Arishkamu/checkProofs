{-# LANGUAGE RecordWildCards, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : PrettyString
Description : Creat pretty string for app data types

This module creates string representations for types and data from AstInfo and ProofBase using instance Outputable.
-}
module PrettyString (prettyString, prettyStringReport) where

import GHC.Utils.Outputable
    ( Outputable(..),
      IsLine((<+>), text),
      doubleQuotes,
      int,
      integer,
      nest,
      parens,
      showSDocUnsafe,
      IsDoc(($$)) )

import Data.List (intercalate)

import AstInfo
import ProofBase ( ExprInfo(..), SideExprInfo(..) )



instance Outputable Conversion where
  ppr c =
    text "Conversion"
      $$ nest 2 (
           text "lhs:"  <+> ppr (cn_lhs c)
        $$ text "rhs:"  <+> ppr (cn_rhs c)
        $$ text "info:" <+> ppr (cn_info c)
      )

instance Outputable CheckerST where
  ppr CheckerST{..} =
    text "===== AstInfo CheckerST ====="
      $$ nest 2 (
           text "ST_declconvrs:"
             $$ nest 2 ( ppr st_declconvrs )
        $$ text "ST_funcDefs:"
             <+> int (length st_funcdefs)
        $$ text "ST_postlDefs:"
             <+> int (length st_postldefs)
        $$ text "ST_baseDefs:"
             <+> int (length st_base_defs)
        $$ text "current conversion number:"
             <+> int st_cnvrs_count
        $$ text "current decl:"
             <+> ppr st_declconvr_id
      )

instance Outputable PostlDef where
  ppr p =
    text "PostlDef"
      $$ nest 2 (
           text "id:"   <+> ppr (pstl_id p)
        $$ text "fid:"  <+> ppr (pstl_fid p)
        $$ text "rule:" <+> ppr (pstl_rule p)
      )

instance Outputable ExprInfo where
  ppr exprInfo =
    case exprInfo of
      Def name ->
        text "Def " <+> doubleQuotes (text name)
      Prop name ->
        text "Prop" <+> doubleQuotes (text name)
      Inst name ->
        text "Inst" <+> doubleQuotes (text name)
      Beta ->
        text "Beta"
      Eta ->
        text "Eta "
      DefRec name depth ->
        text "DefRec"
          <+> doubleQuotes (text name)
          <+> parens (text "depth =" <+> integer depth)


instance Outputable SideExprInfo where
  ppr sideInfo =
    case sideInfo of
      L expr ->
        text "L" <+> ppr expr
      R expr ->
        text "R" <+> ppr expr
      QED ->
        text "QED"
      Postulate ->
        text "Postulate"



prettyString :: (Outputable a) => a -> String
prettyString = showSDocUnsafe . ppr

-- type Report = ([Id], [(Id, String)])
-- Bool - with reasons or without
prettyStringReport :: Bool -> Report -> String
prettyStringReport withReasons (succs, failsWithReasons) =
  "\n============================================" ++
  "\n================== REPORT ==================" ++
  "\nSuccsessfully proved: " ++ prettyRes succs ++ "\n" ++
  "\nFailures proved: "      ++ prettyRes fails ++ "\n" ++
  (if withReasons
    then "Reasons for failures:\n\n" ++ intercalate "\n" reasons ++ "\n"
    else "\n")
  ++ "============================================\n"
  where
    prettyRes [] = "0" ++ "\n  " ++ "<None>"
    prettyRes xs = show (length xs) ++ "\n  " ++ intercalate "\n  " (map prettyString xs)
    (fails, reasons) = unzip failsWithReasons
