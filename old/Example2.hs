module Example where

--infixl 0 ===
--(===) :: a -> a -> a
--(===) = const
--
--composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
--composeAssoc f g h =
--     f . (g . h)                     -- (.)
-- === (\x -> f ((g . h) x))           -- (.)
-- === (\x -> f ((\x' -> g (h x')) x)) -- {beta}
-- === (\x -> f (g (h x)))             -- {beta привет}
-- === (\x -> (\x' -> f (g x')) (h x)) -- (.)
-- === (\x -> (f . g) (h x))           -- (.)
-- ===  (f . g) . h

data ExprInfo = LFunc String | RFunc String | Beta | LEta | REta
data WithInfo a = WithInfo { value :: a, info :: ExprInfo }


addInfo :: a -> ExprInfo -> WithInfo a
addInfo x info = WithInfo x info


infixl 0 ====
(====) :: WithInfo a -> WithInfo a -> WithInfo a
(====) x y = y

infixr 9 =.
(=.)    :: (b -> c) -> (a -> b) -> a -> c
(=.) f g = \x -> f (g x)

myId                      :: a -> a
myId x                    =  x

myFlip :: (a -> b -> c) -> b -> a -> c
myFlip f x y              =  f y x

-- composeAssoc2 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc2 f g h = value (
--      WithInfo (f . (g . h)) "(.)"
--  ==== WithInfo ((\x -> f ((g . h) x))) "(.)"
--  ==== WithInfo ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
--  ==== WithInfo ((\x -> f (g (h x)))) "{beta привет}"
--  ==== WithInfo ((\x -> (\x' -> f (g x')) (h x))) "(.)"
--  ==== WithInfo ((\x -> (f . g) (h x))) "(.)"
--  ==== WithInfo ((f . g) . h) "(.)")


-- composeAssoc3 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc3 f g h = value (
--      WithInfo (f =. (g =. h)) "(=.)"
--  ==== WithInfo ((\x -> f ((g =. h) x))) "(=.)"
--  ==== WithInfo ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
--  ==== WithInfo ((\x -> f (g (h x)))) "{beta привет}"
--  ==== WithInfo ((\x -> (\x' -> f (g x')) (h x))) "(=.) Right"
--  ==== WithInfo ((\x -> (f =. g) (h x))) "(=.)"
--  ==== WithInfo ((f =. g) =. h) "(=.)")


composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc4 f g h = value (
    (f =. (g =. h))                   `addInfo` LFunc "=."
 ==== (\x -> f ((g =. h) x))          `addInfo` LFunc "=."
 ==== (\x -> f ((\x' -> g (h x')) x)) `addInfo` Beta
 ==== (\x -> f (g (h x)))             `addInfo` Beta
 ==== (\x -> (\x' -> f (g x')) (h x)) `addInfo` RFunc "=."
 ==== (\x -> (f =. g) (h x))          `addInfo` RFunc "=."
 ==== ((f =. g) =. h)                 `addInfo` RFunc "=.")


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f = value (
      (myId =. f)           `addInfo` LFunc "=."
 ==== (\x -> myId (f x))    `addInfo` LFunc "myId"
 ==== (\x -> f x)           `addInfo` LEta
 ==== f                     `addInfo` RFunc "=.")

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f = value (
      (f =. myId)        `addInfo` LFunc "=."
 ==== (\x -> f (myId x)) `addInfo` LFunc "myId"
 ==== (\x -> f x)        `addInfo` LEta
 ==== f                  `addInfo` Beta)


flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = value (
     (myFlip =. myFlip)                        `addInfo` LFunc "=."
 ==== (\f -> myFlip (myFlip f))                 `addInfo` REta
 ==== (\f -> \x -> myFlip (myFlip f) x)         `addInfo` REta
 ==== (\f -> \x -> \y -> myFlip (myFlip f) x y) `addInfo` LFunc "myFlip"
 ==== (\f -> \x -> \y -> myFlip f y x)        `addInfo` LFunc "myFlip"
 ==== (\f -> \x -> \y -> f x y)             `addInfo` LEta
 ==== (\f -> \x -> f x)                     `addInfo` LEta
 ==== (\f -> f)                            `addInfo`  RFunc "myId"
 ==== (\f -> myId f)                        `addInfo` LEta
 ==== myId                                  `addInfo` LEta)

{- forall f x y. myFlip (myFlip f) x y ==== f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y = value (
     myFlip (myFlip f) x y  `addInfo` LFunc "myFlip"
 ==== myFlip f y x         `addInfo` LFunc "myFlip"
 ==== f x y                 `addInfo` LEta)


res1 f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x)

res2 f g h = f . (g . h) where (.) f g = \x -> f (g x)

main :: IO ()
main = do
  putStrLn "The End for ExampleMain.hs"