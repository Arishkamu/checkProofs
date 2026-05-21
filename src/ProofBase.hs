{-|
Module      : ProofBase
Description : Annotation operators and base function defenition from Haskell report.

This module contains operators for  annotating equation reasonings and basic functions coppied from Haskell report.
-}
module ProofBase where

import Prelude hiding ((.), ($), id, flip)

-- | Constructor for expression info, QED and Postulate.
data SideExprInfo = L ExprInfo | R ExprInfo  | QED | Postulate
-- | Constructor for expression info
data ExprInfo =     Def String | Prop String | Inst String | Beta | Eta | DefRec String Integer

-- | Operator for adding annotation to expression
(--.) :: a -> SideExprInfo -> a
(--.) x _ = x

-- | Main operator for checking type equality and combining expressions into chain.
infixl 0 ===
(===) :: a -> a -> a
(===) _ y = y




-- MY FUNCTIONS
infixr 9 .
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

infixr 0 $
($)    :: (a -> b) -> a -> b
($) f x = f x

id                      :: a -> a
id x                    =  x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x

const :: a -> b -> a
const x _  =  x