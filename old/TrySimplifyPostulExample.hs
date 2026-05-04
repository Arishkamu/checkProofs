module Main where

import Control.Monad

infixl 0 ===
(===) :: a -> a -> a
(===) = const


type SideExprInfo = Either ExprInfo ExprInfo
data ExprInfo = Func String | Postl String | Beta | Eta
data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

addInfo :: a -> SideExprInfo -> WithInfo a
addInfo x info = WithInfo x info

postulate :: a -> a -> a
postulate = const

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

myLiftM :: Monad m => (a -> b) -> m a -> m b
myLiftM f xs  =  xs >>= return =. f

(<*>..) :: Monad m => m (a -> b) -> m a -> m b
fs <*>.. xs = fs >>= \f -> myLiftM f xs -- см. liftM выше

myM1 :: Monad m => a -> (a -> m b) -> m b
myM1 a k = (return a >>= k) `postulate` (k a)     -- {POSTULATE}

{-# RULES
"myM1/left-identity"
  forall (k :: a -> m b) (a :: a).
    return a >>= k = k a
#-}

{-# RULES
    "map/map"    forall f g xs.  map f (map g xs) = map (f . g) xs
#-}

tt :: [Int] -> [Int]
tt xs = map (\x -> x * 2) (map (\x -> x + 1) xs)

theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
theoremApplicative0 g xs = value (
  (return g <*>.. xs)                    `addInfo` Left (Func "<*>..")
  ==== (return g >>= \f -> myLiftM f xs) `addInfo` Left (Postl "myM1")
  ==== ((\f -> myLiftM f xs) g)          `addInfo` Left Beta
  ==== (myLiftM g xs)                    `addInfo` Left Beta)

myCoreExpr2 :: Monad m => (a -> b) -> m a -> m b
myCoreExpr2 g xs = (return g >>= \f -> myLiftM f xs)

myCoreExpr1 :: Monad m => (a -> m b) -> a -> m b
myCoreExpr1 k a = (return a >>= k)



-- (<*>..) :: Monad m => m (a -> b) -> m a -> m b
-- fs <*>.. xs = fs >>= \f -> liftM f xs -- см. liftM выше

-- theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
-- theoremApplicative0 g xs =
--   return g <*>.. xs ===              -- (<*>..)
--   return g >>= \f -> liftM f xs ===  -- [m1]
--   (\f -> liftM f xs) g ===           -- beta-reduction
--   liftM g xs

main :: IO ()
main = do
  putStrLn $ show $ tt [0, 1, 2, 3]
  putStrLn $ show $ theoremApplicative0 (\x -> x + 1) (Just 4)
  putStrLn $ show $ myCoreExpr2 (\x -> x + 1) (Just 4)
  putStrLn $ show $ myCoreExpr1 (\x -> Just (x + 1)) 4

-- tt
--   = \ (xs_axd :: [Int]) ->
--       map
--         @Int
--         @Int
--         (. @Int
--            @Int
--            @Int
--            (\ (x_axg :: Int) ->
--               * @Int GHC.Internal.Num.$fNumInt x_axg (GHC.Types.I# 2#))
--            (\ (x_azW :: Int) ->
--               + @Int GHC.Internal.Num.$fNumInt x_azW (GHC.Types.I# 1#)))
--         xs_axd

-- tt
--   = \ (xs_axd :: [Int]) ->
--       map
--         @Int
--         @Int
--         (\ (x_axg :: Int) ->
--            * @Int GHC.Internal.Num.$fNumInt x_axg (GHC.Types.I# 2#))
--         (map
--            @Int
--            @Int
--            (\ (x_azW :: Int) ->
--               + @Int GHC.Internal.Num.$fNumInt x_azW (GHC.Types.I# 1#))
--            xs_axd)
