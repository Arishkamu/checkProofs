module SortDecls (sorteDeclConvrs) where

import GHC (Id, getOccName)
import GHC.Types.Name.Occurrence (occNameString)
import Data.Graph
import Data.Maybe (mapMaybe)
import Data.List (find)
import Data.List.NonEmpty (toList)

import AstInfo
import PrettyString

sorteDeclConvrs :: [DeclConversions] -> Either Cyrcles [DeclConversions]
sorteDeclConvrs declConvrs = topoSort $ toNodes declConvrs

cmpIdString :: String -> Id -> Bool
cmpIdString str var = occNameString (getOccName var) == str

--            (value,              key, depend_on)
type EdgeDC = (DeclConversions,    Id,  [Id])
type Cyrcles = [[Id]]

toNodes :: [DeclConversions] -> [EdgeDC]
toNodes decls = map (\dc@(decl_id, cnvrs) -> (dc, decl_id, cnInfoStr cnvrs)) decls
  where
    cnInfoStr :: [Conversion] -> [Id]
    cnInfoStr = mapMaybe (exprInfoToStr . cnToExprInfo)
    exprInfoToStr cnvr = case cnvr of
      Just (Decl s) -> findIdByStr s
      Just (Prop s) -> findIdByStr s
      _             -> Nothing
    cnToExprInfo  cnvr = case cn_info cnvr of
      L ei -> Just ei
      R ei -> Just ei
      Postulate -> Nothing
      info -> error $ "Unexpected comment for conversion. Expected L or R. Got:" ++ prettyString info
    findIdByStr s_id = find (cmpIdString s_id) (map fst decls)



topoSort :: [EdgeDC] -> Either Cyrcles [DeclConversions]
topoSort dc_edges =
  case stronglyConnComp dc_edges of
    cyclic@(_:_)
      | any isCycle cyclic -> Left (collectCycles cyclic)
    sccs -> Right [ v | AcyclicSCC v <- sccs ]
  where

    isCycle :: SCC DeclConversions -> Bool
    isCycle (AcyclicSCC _) = False
    isCycle _              = True

    collectCycles :: [SCC DeclConversions] -> Cyrcles
    collectCycles =
      foldr go []
      where
        go :: SCC DeclConversions -> Cyrcles -> Cyrcles
        go (NECyclicSCC vs) acc = map fst (toList vs) : acc
        go _ acc                = acc

