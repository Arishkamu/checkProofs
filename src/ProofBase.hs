module ProofBase where

import Prelude hiding ((.), ($), id, flip)

data SideExprInfo = L ExprInfo | R ExprInfo | QED | Postulate
data ExprInfo = Decl String | Prop String | Inst String | Beta | Eta | DeclRec String Integer
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

(--.) :: a -> SideExprInfo -> a
(--.) x _ = x


infixl 0 ===
(===) :: a -> a -> a
(===) _ y = y

importThisFunc :: a -> a
importThisFunc x = x

importThisFuncHiding :: a -> a
importThisFuncHiding x = x



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