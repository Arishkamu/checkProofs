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
     (f . (g . h))                   --. L (Def  ".")
 === (\x -> f ((g . h) x))           --. L (Def  ".")
 === (\x -> f ((\x' -> g (h x')) x)) --. L Beta 
 === (\x -> f (g (h x)))             --. L Beta 
 === (\x -> (\x' -> f (g x')) (h x)) --. R (Def  ".")
 === (\x -> (f . g) (h x))           --. R (Def  ".")
 === ((f . g) . h)                   --. QED

composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
     (id . f)          --. L (Def  ".")
 === (\x -> id (f x))  --. L (Def  "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
     (f . id)          --. L (Def  ".")
 === (\x -> f (id x))  --. L (Def  "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

{-
несколько версий, иллюстрирующих разные  (по степени бесточечности) способы записи одной и той же теоремы
-}
{- flip . flip === id -}
flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = 
     (flip . flip)                         --. L (Def  ".") 
 === (\f -> flip (flip f))                 --. R Eta
 === (\f -> \x -> flip (flip f) x)         --. R Eta
 === (\f -> \x -> \y -> flip (flip f) x y) --. L (Def  "flip")
 === (\f -> \x -> \y -> flip f y x)        --. L (Def  "flip")
 === (\f -> \x -> \y -> f x y)             --. L Eta
 === (\f -> \x -> f x)                     --. L Eta
 === (\f -> f)                             --. R (Def  "id")
 === (\f -> id f)                          --. L Eta
 === id                                    --. QED

{- forall f x y. flip (flip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y  = 
     flip (flip f) x y  --. L (Def  "flip")
 === flip f y x         --. L (Def  "flip")
 === f x y              --. QED