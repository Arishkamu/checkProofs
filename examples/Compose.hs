module Compose where

import ProofBase

import Prelude hiding ((.), id, const, flip)

{-
Композиция (.) является моноидом с id в качестве нейтрального элемента

GHC.Internal.Base
Композиция определена как функция двух аргументов, поэтому она инлайнится на двух аргументах!!
{-# INLINE (.) #-}
-}
{-
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

id                      :: a -> a
id x                    =  x

-- Доллар тоже функция одного аргумента!
-- {-# INLINE ($) #-}
($) :: forall repa repb (a :: TYPE repa) (b :: TYPE repb). (a -> b) -> a -> b
($) f = f

const                   :: a -> b -> a
const x _               =  x

flip :: forall repc a b (c :: TYPE repc). (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x
-}

composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc f g h = 
     (f . (g . h))                   --. L (Decl ".")
 === (\x -> f ((g . h) x))           --. L (Decl ".")
 === (\x -> f ((\x' -> g (h x')) x)) --. L Beta 
 === (\x -> f (g (h x)))             --. L Beta 
 === (\x -> (\x' -> f (g x')) (h x)) --. R (Decl ".")
 === (\x -> (f . g) (h x))           --. R (Decl ".")
 === ((f . g) . h)                   --. QED

composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
     (id . f)          --. L (Decl ".")
 === (\x -> id (f x))  --. L (Decl "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
     (f . id)          --. L (Decl ".")
 === (\x -> f (id x))  --. L (Decl "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

{-
несколько версий, иллюстрирующих разные  (по степени бесточечности) способы записи одной и той же теоремы
-}
{- flip . flip === id -}
flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = 
     (flip . flip)                         --. L (Decl ".") 
 === (\f -> flip (flip f))                 --. R Eta
 === (\f -> \x -> flip (flip f) x)         --. R Eta
 === (\f -> \x -> \y -> flip (flip f) x y) --. L (Decl "flip")
 === (\f -> \x -> \y -> flip f y x)        --. L (Decl "flip")
 === (\f -> \x -> \y -> f x y)             --. L Eta
 === (\f -> \x -> f x)                     --. L Eta
 === (\f -> f)                             --. R (Decl "id")
 === (\f -> id f)                          --. L Eta
 === id                                    --. QED

{- forall f x y. flip (flip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y  = 
     flip (flip f) x y  --. L (Decl "flip")
 === flip f y x         --. L (Decl "flip")
 === f x y              --. QED