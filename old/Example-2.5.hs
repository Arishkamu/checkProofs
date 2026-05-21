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
data ExprInfo = Func String | Beta | Eta | FuncRec String Integer
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

infixl 9 --.
(--.) :: a -> SideExprInfo -> a
(--.) x _ = x


infixl 0 ===
(===) :: a -> a -> a
(===) _ y = y

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
--  === WithInfo ((\x -> f ((g . h) x))) "(.)"
--  === WithInfo ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
--  === WithInfo ((\x -> f (g (h x)))) "{beta привет}"
--  === WithInfo ((\x -> (\x' -> f (g x')) (h x))) "(.)"
--  === WithInfo ((\x -> (f . g) (h x))) "(.)"
--  === WithInfo ((f . g) . h) "(.)")


-- composeAssoc3 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc3 f g h = value (
--      WithInfo (f =. (g =. h)) "(=.)"
--  === WithInfo ((\x -> f ((g =. h) x))) "(=.)"
--  === WithInfo ((\x -> f ((\x' -> g (h x')) x))) "{beta}"
--  === WithInfo ((\x -> f (g (h x)))) "{beta привет}"
--  === WithInfo ((\x -> (\x' -> f (g x')) (h x))) "(=.) Right"
--  === WithInfo ((\x -> (f =. g) (h x))) "(=.)"
--  === WithInfo ((f =. g) =. h) "(=.)")


composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc4 f g h = 
    (f =. (g =. h))                  --. Left (Func "=.")
 === (\x -> f ((g =. h) x))          --. Left (Func "=.")
 === (\x -> f ((\x' -> g (h x')) x)) --. Left Beta
 === (\x -> f (g (h x)))             --. Left Beta
 === (\x -> (\x' -> f (g x')) (h x)) --. Right (Func "=.")
 === (\x -> (f =. g) (h x))          --. Right (Func "=.")
 === ((f =. g) =. h)


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f = 
      (myId =. f)          --. Left (Func "=.")
 === (\x -> myId (f x))    --. Left (Func "myId")
 === (\x -> f x)           --. Left Eta
 === f

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f = 
      (f =. myId)       --. Left (Func "=.")
 === (\x -> f (myId x)) --. Left (Func "myId")
 === (\x -> f x)        --. Left Eta
 === f


flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = 
     (myFlip =. myFlip)                         --. Left (Func "=.")
 === (\f -> myFlip (myFlip f))                 --. Right Eta
 === (\f -> \x -> myFlip (myFlip f) x)         --. Right Eta
 === (\f -> \x -> \y -> myFlip (myFlip f) x y) --. Left (Func "myFlip")
 === (\f -> \x -> \y -> myFlip f y x)          --. Left (Func "myFlip")
 === (\f -> \x -> \y -> f x y)                 --. Left Eta
 === (\f -> \x -> f x)                         --. Left Eta
 === (\f -> f)                                 --. Right (Func "myId")
 === (\f -> myId f)                            --. Left Eta
 === myId

{- forall f x y. myFlip (myFlip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y =
      myFlip (myFlip f) x y  --. Left (Func "myFlip")
 === myFlip f y x           --. Left (Func "myFlip")
 === f x y

res1 f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x)

res2 f g h = f . (g . h) where (.) f g = \x -> f (g x)

main :: IO ()
main = do
  putStrLn "The End for ExampleMain.hs"