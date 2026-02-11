{-# LANGUAGE TemplateHaskell #-}
module Extra where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

headDecl :: Dec -> Exp
headDecl d = case d of
    FunD _ ((Clause _ (NormalB expr) _):_) -> headExp expr

headExp :: Exp -> Exp
headExp (AppE f _)        = headExp f
headExp (InfixE _ op _)   = op
headExp (UInfixE _ op _)  = op
headExp (ParensE e)       = headExp e
headExp e                 = e

myAST1 :: Q [Dec]
myAST1 = [d| res f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x) |]

myAST2 :: Q [Dec]
myAST2 = [d| res f g h = f . (g . h) where (.) f g = \x -> f (g x) |]
--    expr <- exprQ
--    return $ headExp expr

--module Extra (hello) where
--hello :: String
--hello = "Hello, world!"