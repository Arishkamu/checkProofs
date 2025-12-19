infixl 0 ===
(===) :: a -> a -> a
(===) = const

{-
Композиция (.) является моноидом с id в качестве нейтрального элемента

GHC.Internal.Base
Композиция определена как функция двух аргументов, поэтому она инлайнится на двух аргументах!!
{-# INLINE (.) #-}
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

id                      :: a -> a
id x                    =  x

Доллар тоже функция одного аргумента!
{-# INLINE ($) #-}
($) :: forall repa repb (a :: TYPE repa) (b :: TYPE repb). (a -> b) -> a -> b
($) f = f

const                   :: a -> b -> a
const x _               =  x

flip :: forall repc a b (c :: TYPE repc). (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x -- hihihi
-}
-- heeeee
composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc f g h =
     f . (g . h)                     -- (.)
 === (\x -> f ((g . h) x))           -- (.)
 === (\x -> f ((\x' -> g (h x')) x)) -- {beta}
 === (\x -> f (g (h x)))             -- {beta привет}
 === (\x -> (\x' -> f (g x')) (h x)) -- (.)
 === (\x -> (f . g) (h x))           -- (.)
 ===  (f . g) . h

theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x =
  fs <*>.. return x  ===         -- [lemma1]
  fs >>= \f -> return (f x) ===  -- [lemma2]
  return ($ x) <*>.. fs
