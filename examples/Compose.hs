module Compose where

import ProofsBase ( (===) )

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
flip f x y              =  f y x
-}

composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc f g h = 
     f . (g . h)                     -- (.)
 === (\x -> f ((g . h) x))           -- (.)
 === (\x -> f ((\x' -> g (h x')) x)) -- {beta} 
 === (\x -> f (g (h x)))             -- {beta} 
 === (\x -> (\x' -> f (g x')) (h x)) -- (.)
 === (\x -> (f . g) (h x))           -- (.)
 ===  (f . g) . h 

composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
     id . f            -- (.)
 === (\x -> id (f x))  -- id
 === (\x -> f x)       -- {eta}
 === f

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
     f . id            -- (.)
 === (\x -> f (id x))  -- id
 === (\x -> f x)       -- {eta}
 === f

{-
несколько версий, иллюстрирующих разные  (по степени бесточечности) способы записи одной и той же теоремы
-}
{- flip . flip === id -}
flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = 
     flip . flip                           -- (.) 
 === (\f -> flip (flip f))                 -- {eta}
 === (\f -> \x -> flip (flip f) x)         -- {eta}
 === (\f -> \x -> \y -> flip (flip f) x y) -- flip
 === (\f -> \x -> \y -> flip f y x)        -- flip
 === (\f -> \x -> \y -> f x y)             -- {eta}
 === (\f -> \x -> f x)                     -- {eta}
 === (\f -> f)                             -- id
 === (\f -> id f)                          -- {eta}
 === id

{- forall f x y. flip (flip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y  = 
     flip (flip f) x y  -- flip
 === flip f y x         -- flip
 === f x y              