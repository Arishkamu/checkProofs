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

type SideExprInfo = Either ExprInfo ExprInfo
data ExprInfo = Func String | Beta | Eta
data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

addInfo :: a -> SideExprInfo -> WithInfo a
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
    (f =. (g =. h))                   `addInfo` Left (Func "=.")
 ==== (\x -> f ((g =. h) x))          `addInfo` Left (Func "=.")
 ==== (\x -> f ((\x' -> g (h x')) x)) `addInfo` Left Beta
 ==== (\x -> f (g (h x)))             `addInfo` Left Beta
 ==== (\x -> (\x' -> f (g x')) (h x)) `addInfo` Right (Func "=.")
 ==== (\x -> (f =. g) (h x))          `addInfo` Right (Func "=.")
 ==== ((f =. g) =. h)                 `addInfo` Right (Func "=."))


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f = value (
      (myId =. f)           `addInfo` Left (Func "=.")
 ==== (\x -> myId (f x))    `addInfo` Left (Func "myId")
 ==== (\x -> f x)           `addInfo` Left Eta
 ==== f                     `addInfo` Right (Func "=."))

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f = value (
      (f =. myId)        `addInfo` Left (Func "=.")
 ==== (\x -> f (myId x)) `addInfo` Left (Func "myId")
 ==== (\x -> f x)        `addInfo` Left Eta
 ==== f                  `addInfo` Left Beta)


flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = value (
     (myFlip =. myFlip)                         `addInfo` Left (Func "=.")
 ==== (\f -> myFlip (myFlip f))                 `addInfo` Right Eta
 ==== (\f -> \x -> myFlip (myFlip f) x)         `addInfo` Right Eta
 ==== (\f -> \x -> \y -> myFlip (myFlip f) x y) `addInfo` Left (Func "myFlip")
 ==== (\f -> \x -> \y -> myFlip f y x)          `addInfo` Left (Func "myFlip")
 ==== (\f -> \x -> \y -> f x y)                 `addInfo` Left Eta
 ==== (\f -> \x -> f x)                         `addInfo` Left Eta
 ==== (\f -> f)                                 `addInfo` Right (Func "myId")
 ==== (\f -> myId f)                            `addInfo` Left Eta
 ==== myId                                      `addInfo` Left Eta)

{- forall f x y. myFlip (myFlip f) x y ==== f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y = value (
      myFlip (myFlip f) x y  `addInfo` Left (Func "myFlip")
 ==== myFlip f y x           `addInfo` Left (Func "myFlip")
 ==== f x y                  `addInfo` Left Eta)

res1 f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x)

res2 f g h = f . (g . h) where (.) f g = \x -> f (g x)

main :: IO ()
main = do
  putStrLn "The End for ExampleMain.hs"