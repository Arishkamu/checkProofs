-- Ver. 1
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

-- Ver. 2
infixl 0 =====
(=====) :: (a -> String) -> (a -> String) -> (a -> String)
(=====) x y = y

infixl 0 ======
(======) :: (a -> String) -> a -> a
(======) x y = y


composeAssoc2 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> (d -> String)
composeAssoc2 f g h =
     (f . (g . h)) "(.)"
 ===== ((\x -> f ((g . h) x))) "(.)"
 ===== ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
 ===== ((\x -> f (g (h x)))) "{beta привет}"
 ===== ((\x -> (\x' -> f (g x')) (h x))) "(.)"
 ===== ((\x -> (f . g) (h x))) "(.)"
 ====== ((f . g) . h)



-- Ver. 3
data WithInfo a = WithInfo { value :: a, info :: String }

infixl 0 ====
(====) :: WithInfo a -> WithInfo a -> WithInfo a
(====) x y = y


composeAssoc2 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc2 f g h =
     WithInfo (f . (g . h)) "(.)"
 ==== WithInfo ((\x -> f ((g . h) x))) "(.)"
 ==== WithInfo ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
 ==== WithInfo ((\x -> f (g (h x)))) "{beta привет}"
 ==== WithInfo ((\x -> (\x' -> f (g x')) (h x))) "(.)"
 ==== WithInfo ((\x -> (f . g) (h x))) "(.)"
 ==== value $ WithInfo ((f . g) . h) "(.)"

--theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
--theoremApplicative3 fs x =
--  fs <*>.. return x  ===         -- [lemma1]
--  fs >>= \f -> return (f x) ===  -- [lemma2]
--  return ($ x) <*>.. fs

res1 f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x)

res2 f g h = f . (g . h) where (.) f g = \x -> f (g x)
