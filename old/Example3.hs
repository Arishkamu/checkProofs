module Example where

infixl 0 ===
(===) :: a -> a -> a
(===) = const
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
data ExprInfo = Func String | Postl String | Beta | Eta
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

postulate :: a -> a -> a
postulate = const

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

-- -- myAssoc 

-- composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc4 f g h = value (
--     (f =. (g =. h))                   `addInfo` Left (Func "=.")
--  ==== (\x -> f ((g =. h) x))          `addInfo` Left (Func "=.")
--  ==== (\x -> f ((\x' -> g (h x')) x)) `addInfo` Left Beta
--  ==== (\x -> f (g (h x)))             `addInfo` Left Beta
--  ==== (\x -> (\x' -> f (g x')) (h x)) `addInfo` Right (Func "=.")
--  ==== (\x -> (f =. g) (h x))          `addInfo` Right (Func "=.")
--  ==== ((f =. g) =. h)                 `addInfo` Right (Func "=."))


-- composeLeftNeutral :: (a -> b) -> a -> b
-- composeLeftNeutral f = value (
--       (myId =. f)           `addInfo` Left (Func "=.")
--  ==== (\x -> myId (f x))    `addInfo` Left (Func "myId")
--  ==== (\x -> f x)           `addInfo` Left Eta
--  ==== f                     `addInfo` Right (Func "=."))

-- composeRightNeutral :: (a -> b) -> a -> b
-- composeRightNeutral f = value (
--       (f =. myId)        `addInfo` Left (Func "=.")
--  ==== (\x -> f (myId x)) `addInfo` Left (Func "myId")
--  ==== (\x -> f x)        `addInfo` Left Eta
--  ==== f                  `addInfo` Left Beta)


-- flipFlipIsId :: (a -> b -> c) -> a -> b -> c
-- flipFlipIsId  = value (
--      (myFlip =. myFlip)                         `addInfo` Left (Func "=.")
--  ==== (\f -> myFlip (myFlip f))                 `addInfo` Right Eta
--  ==== (\f -> \x -> myFlip (myFlip f) x)         `addInfo` Right Eta
--  ==== (\f -> \x -> \y -> myFlip (myFlip f) x y) `addInfo` Left (Func "myFlip")
--  ==== (\f -> \x -> \y -> myFlip f y x)          `addInfo` Left (Func "myFlip")
--  ==== (\f -> \x -> \y -> f x y)                 `addInfo` Left Eta
--  ==== (\f -> \x -> f x)                         `addInfo` Left Eta
--  ==== (\f -> f)                                 `addInfo` Right (Func "myId")
--  ==== (\f -> myId f)                            `addInfo` Left Eta
--  ==== myId                                      `addInfo` Left Eta)

-- {- forall f x y. myFlip (myFlip f) x y ==== f x y -}
-- flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
-- flipFlipIsId' f x y = value (
--       myFlip (myFlip f) x y  `addInfo` Left (Func "myFlip")
--  ==== myFlip f y x           `addInfo` Left (Func "myFlip")
--  ==== f x y                  `addInfo` Left Eta)


res1 f g h = (\x -> f ((g . h) x)) where (.) f g = \x -> f (g x)

res2 f g h = f . (g . h) where (.) f g = \x -> f (g x)

-- {-# ANN m1 "postul" #-}
myM1 :: Monad m => a -> (a -> m b) -> m b
myM1 a k = (return a >>= k) `postulate` (k a)     -- {POSTULATE}

myM2 :: Monad m => m a -> m a
myM2 m = (m >>= return) `postulate` m      -- {POSTULATE}

-- ----------------------
-- ----------------------
-- ----------------------
-- ----------------------
-- ----------------------
-- ----------------------
-- ----------------------
-- m1 :: Monad m => a -> (a -> m b) -> m b
-- m1 a k =
--      return a >>= k -- {POSTULATE}
--  === k a

-- m2 :: Monad m => m a -> m a
-- m2 m =
--      m >>= return    -- {POSTULATE}
--  === m

-- m3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
-- m3 m k k' =
--      m >>= k >>= k'   -- {POSTULATE}
--  ===  m >>= \x -> k x >>= k'

-- myM1 :: Monad m => (a -> m b) -> a -> m b
-- myM1 k a = return a >>= k

-- myMm2 :: Monad m => m a -> m a
-- myMm2 m = m >>= return

-- -- myMm3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
-- -- myMm3 m k k' =
-- --      m >>= k >>= k'   -- {POSTULATE}
-- --  ===  m >>= \x -> k x >>= k'

{-
Покажите, что каждая монада - это функтор. 
Для этого выразите fmap через (>>=) и return:
-}
myLiftM :: Monad m => (a -> b) -> m a -> m b
myLiftM f xs  =  xs >>= return =. f
--liftM f xs  =  xs >>= \x -> return (f x)
-- Control.Monad.liftM
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Functor.
-}
{-
1 Functor law
liftM id xs == xs
-}
theoremFunctor1 :: Monad m => m b -> m b
theoremFunctor1 xs = value (
  (myLiftM myId xs)                   `addInfo` Left (Func "myLiftM")
  ==== (xs >>= return =. myId)        `addInfo` Left (Func "=.")
  ==== (xs >>= \x -> return (myId x)) `addInfo` Left (Func "myId")
  ==== (xs >>= \x -> return x)        `addInfo` Left Eta
  ==== (xs >>= return)                `addInfo` Left (Postl "myM2")
  ==== xs                             `addInfo` Left Eta)
{-
2 Functor law
liftM (f . g) xs == liftM f (liftM g xs)
-}



-- -- LFunc: myLiftM ::
-- -- l: App :: myLiftM @m_aTl @b_aTm @b_aTm $dMonad_aTn (id @b_aTm) xs_az9
-- -- r: App :: >>=
-- --   @m_aTl
-- --   $dMonad_aTn
-- --   @b_aTm
-- --   @b_aTm
-- --   xs_az9
-- --   (=.
-- --      @b_aTm
-- --      @(m_aTl b_aTm)
-- --      @b_aTm
-- --      (return @m_aTl $dMonad_aTn @b_aTm)
-- --      (myId @b_aTm))







-- theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
-- theoremFunctor2 f g xs = value (
--   liftM f (liftM g xs)                              `addInfo` LFunc "myLiftM"
--   === liftM f (xs >>= return . g)                   `addInfo` LFunc "myLiftM"
--   === (xs >>= return . g) >>= return . f            `addInfo` RFunc "myM3"
--   === xs >>= \x -> (return . g) x >>= return . f    `addInfo` LFunc "=."
--   === xs >>= \x -> return (g x) >>= return . f      `addInfo` RFunc "myM1"
--   === xs >>= \x -> (return . f) (g x)               `addInfo` RFunc "=."
--   === xs >>= \x -> ((return . f) . g) x             `addInfo` REta
--   === xs >>= (return . f) . g 
--   ===                    -- assoc (.) ?????????
--   xs >>= return . (f . g) 
--   ===                    -- liftM
--   liftM (f . g) xs 

-----------------------------------------------------------------------------------
{-
Покажите, что каждая монада --- это аппликативный функтор. 
Для этого выразите (<*>) :: Applicative f => f (a -> b) -> f a -> f b
на языке монад:
-}
(<*>..) :: Monad m => m (a -> b) -> m a -> m b
fs <*>.. xs = fs >>= \f -> myLiftM f xs -- см. liftM выше
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Applicative.
-}
{-
0 Applicative law
liftM g xs == return g <*>.. xs
-}
theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
theoremApplicative0 g xs = value (
  (return g <*>.. xs)                    `addInfo` Left (Func "<*>..")
  ==== (return g >>= \f -> myLiftM f xs) `addInfo` Left (Postl "myM1")
  ==== ((\f -> myLiftM f xs) g)          `addInfo` Left Beta
  ==== (myLiftM g xs)                    `addInfo` Left Beta)

-- {-
-- 1 Applicative law (Identity)
-- return id <*>.. xs  == xs
-- -}
-- theoremApplicative1 :: Monad m => m b -> m b
-- theoremApplicative1 xs =
--   return id <*>.. xs ===              -- (<*>..)
--   return id >>= \f -> liftM f xs ===  -- [m1]
--   (\f -> liftM f xs) id ===           -- beta-reduction
--   liftM id xs ===                     -- [theoremFunctor1]
--   xs

{-
2 Applicative law (Homomorphism)
return g <*>.. return x  == return (g x)
-}
-- theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
-- theoremApplicative2 g x =
--   return g <*>.. return x ===               -- (<*>..)
--   return g >>= \f -> liftM f (return x) === -- [m1]
--   (\f -> liftM f (return x)) g ===          -- beta-reduction
--   liftM g (return x) ===                    -- liftM
--   return x >>= return . g ===               -- [m1]
--   (return . g) x  ===                       -- (.)
--   return (g x)

-- {-
-- 3 Applicative law (Interchange)
-- fs <*>.. return x  ===  return ($ x) <*>.. fs
-- -}
-- theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
-- theoremApplicative3 fs x =
--   fs <*>.. return x  ===         -- [lemma1]
--   fs >>= \f -> return (f x) ===  -- [lemma2]
--   return ($ x) <*>.. fs
--   where
--     lemma1 = -- left hand side transformation
--       fs <*>.. return x  ===                    -- (<*>..)
--       fs >>= \f -> liftM f (return x) ===       -- liftM
--       fs >>= \f -> return x >>= return . f ===  -- [m1]
--       fs >>= \f -> (return . f) x  ===          -- (.)
--       fs >>= \f -> return (f x)
--     lemma2 = -- right hand side transformation
--       return ($ x) <*>.. fs ===              -- (<*>..)
--       return ($ x) >>= \f -> liftM f fs ===  -- [m1]
--       (\f -> liftM f fs) ($ x) ===           -- beta-reduction
--       liftM ($ x) fs  ===                    -- liftM
--       fs >>= return . ($ x) ===              -- (.)
--       fs >>= \f -> return (($ x) f) ===      -- ($)
--       fs >>= \f -> return (f x)
-- {-
-- 4 Applicative law (Composition)
-- return (.) <*>.. us <*>.. vs <*>.. xs  ==  us <*>.. (vs <*>.. xs)
-- -}
-- theoremApplicative4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
-- theoremApplicative4 us vs xs =
--   return (.) <*>.. us <*>.. vs <*>.. xs  ===      -- [lemma1]
--   us >>= \u -> vs >>= \v -> liftM (u . v) xs ===  -- [lemma2]
--   us <*>.. (vs <*>.. xs)
--   where
--     lemma1 = -- left hand side transformation
--       return (.) <*>.. us <*>.. vs <*>.. xs  ===                            -- (<*>..)
--       (return (.) >>= \c -> liftM c us) <*>.. vs <*>.. xs ===               -- [m1]
--       (\c -> liftM c us) (.) <*>.. vs <*>.. xs ===                          -- beta-reduction
--       liftM (.) us <*>.. vs <*>.. xs ===                                    -- liftM
--       (us >>= return . (.)) <*>.. vs <*>.. xs ===                           -- (<*>..)
--       ((us >>= return . (.)) >>= \r -> liftM r vs) <*>.. xs ===             -- [m3] 
--       (us >>= \u -> (return . (.)) u >>= \r -> liftM r vs) <*>.. xs ===     -- (.)
--       (us >>= \u -> return (u .) >>= \r -> liftM r vs) <*>.. xs ===         -- [m1]
--       (us >>= \u -> (\r -> liftM r vs) (u .)) <*>.. xs ===                  -- beta-reduction
--       (us >>= \u -> liftM (u .) vs) <*>.. xs ===                            -- liftM
--       (us >>= \u -> vs >>= return . (u .)) <*>.. xs ===                     -- (<*>..)
--       (us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs ===         -- [m3] + beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
--       us >>= \u -> vs >>= return . (u .) >>= \f -> liftM f xs ===           -- [m3] 
--       us >>= \u -> vs >>= \v -> (return . (u .)) v >>= \f -> liftM f xs === -- beta-reduction
--       us >>= \u -> vs >>= \v -> return  (u . v) >>= \f -> liftM f xs ===    -- [m1]
--       us >>= \u -> vs >>= \v ->  (\f -> liftM f xs) (u . v) ===             -- beta-reduction
--       us >>= \u -> vs >>= \v ->  liftM (u . v) xs
--     lemma2 = -- right hand side transformation
--       us <*>.. (vs <*>.. xs)  ===                                -- (<*>..)
--       us >>= \u -> liftM u (vs <*>.. xs) ===                     -- (<*>..)
--       us >>= \u -> liftM u (vs >>= \v -> liftM v xs) ===         -- liftM
--       us >>= \u -> (vs >>= \v -> liftM v xs) >>= return . u ===  -- [m3] + beta-reduction ??????
--       us >>= \u -> vs >>= \v -> liftM v xs >>= return . u ===    -- liftM
--       us >>= \u -> vs >>= \v -> liftM u (liftM v xs)  ===        -- [theoremFunctor2]
--       us >>= \u -> vs >>= \v -> liftM (u . v) xs


-- --------------------------------------------
-- -- Законы класса Monad

-- {-
-- Покажите, что из законов класса типов Monad 

-- return a >>= k   ==  k a                     -- m1
-- m >>= return     ==  m                       -- m2
-- (m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- m3

-- следует, что стрелки Клейсли образуют моноид относительно операции их композиции (>=>)
-- c return в качестве нейтрального элемента. Иными словами докажите, что верны равенства

-- return >=> k     ==  k
-- k >=> return     ==  k
-- (u >=> v) >=> w  ==  u >=> (v >=> w)
-- -}

-- -- Определение рыбки через >>=
-- (>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
-- g >=> h = \x -> g x >>= h

-- -- return >=> k  ==  k
-- fishLeftNeutral :: Monad m => (a -> m b) -> a -> m b
-- fishLeftNeutral k =
--       return >=> k          -- >=>
--  === (\a -> return a >>= k) -- [m1]
--  === (\a -> k a)            -- eta-reduction
--  === k

-- -- k >=> return  ==  k
-- fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
-- fishRightNeutral k =
--      k >=> return           -- >=>
--  === (\a -> k a >>= return) -- [m2]
--  === (\a -> k a)            -- eta-reduction
--  === k

-- -- (u >=> v) >=> w  ==  u >=> (v >=> w)
-- fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
-- fishAssoc u v w =
--      (u >=> v) >=> w                      -- >=>
--  === (\a -> (u >=> v) a >>= w)            -- >=>
--  === (\a -> (\a' -> u a' >>= v) a >>= w)  -- beta-reduction
--  === (\a -> (u a >>= v) >>= w)            -- [m3]
--  === (\a -> u a >>= \b -> v b >>= w)      -- >=>
--  === (\a -> u a >>= (v >=> w))            -- >=>
--  === u >=> (v >=> w)

-- -----------------------------------------------------

-- {-
-- Покажите, что законы

-- join . return       ==  id           -- mjfr1
-- join . fmap return  ==  id           -- mjfr2
-- join . fmap join    ==  join . join  -- mjfr3

-- следуют из законов класса типов Monad

-- return a >>= k   ==  k a                     -- [m1]
-- m >>= return     ==  m                       -- [m2]
-- (m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- [m3]

-- используя реализации join через (>>=) и liftM через (>>=) и return.
-- -- 
-- join x  =  x >>= id 
-- liftM f xs  =  xs >>= return . f 
-- -}

-- join :: Monad m => m (m a) -> m a
-- join x  =  x >>= id 

-- --- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
-- --  join . return == id  -- :: m a -> m a
-- mjfr1 :: Monad m => m a -> m a
-- mjfr1 xs = 
--      (join . return) xs -- (.)
--  === join (return xs)   -- join
--  === return xs >>= id   -- [m1]
--  === id xs              -- id

-- ---
-- --   join . fmap return == id  -- :: m a -> m a
-- mjfr2 :: Monad m => m a -> m a
-- mjfr2 xs = 
--      (join . liftM return) xs                -- (.)
--  === join (liftM return xs)                  -- join
--  === liftM return xs >>= id                  -- liftM
--  === xs >>= return . return >>= id           -- [m3]
--  === xs >>= \x -> (return . return) x >>= id -- (.)
--  === xs >>= \x -> return (return x) >>= id   -- [m1]
--  === xs >>= \x -> id (return x)              -- id
--  === xs >>= \x -> return x                   -- eta-reduction
--  === xs >>= return                           -- [m2]
--  === xs                                      -- id
--  === id xs

-- ---
-- --  join . fmap join  ==  join . join  -- :: m (m (m a)) -> m a
-- mjfr3 :: Monad m => m (m (m a)) -> m a
-- mjfr3 x3s = 
--      (join . liftM join) x3s                    -- (.)
--  === join (liftM join x3s)                      -- liftM
--  === join (x3s >>= return . join)               -- join
--  === x3s >>= return . join >>= id               -- [m3]
--  === x3s >>= \x2s -> (return . join) x2s >>= id -- (.)
--  === x3s >>= \x2s -> return (join x2s) >>= id   -- [m1]
--  === x3s >>= \x2s -> id (join x2s)              -- id
--  === x3s >>= \x2s -> join x2s                   -- join
--  === x3s >>= \x2s -> x2s >>= id                 -- id
--  === x3s >>= \x2s -> id x2s >>= id              -- [m3]
--  === x3s >>= id >>= id                          -- join
--  === join x3s >>= id                            -- join
--  === join (join x3s)                            -- (.)
--  === (join . join) x3s





-- ----------------------------------------------------
-- ----------------------------------------------------
-- -- Concrete Monad Laws
-- {-
-- return a >>= k  ===  k a                     -- 1 Monad Law
-- m >>= return    ===  m                       -- 2 Monad Law
-- m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-- -}

-- -- Maybe (TODO для пруфчекинга типы и их инстансы надо выписывать явно или иметь встроенный псевдобиблиотечный референс)
-- {-
-- instance  Monad Maybe  where
--   Just x  >>= k  =  k x     -- (1)
--   Nothing >>= _  =  Nothing -- (2)

--   return  =  Just
-- -}
-- monad1LawMaybe :: a -> (a -> Maybe b) -> Maybe b
-- monad1LawMaybe a k =
--      return a >>= k  -- inst return
--  === Just a >>= k    -- inst (>>=) (1)
--  === k a

-- monad2LawMaybe ::  Maybe a -> Maybe a
-- monad2LawMaybe (Just a) =
--      Just a >>= return   -- inst (>>=) (1)
--  === return a            -- inst return
--  === Just a
-- monad2LawMaybe Nothing =
--      Nothing >>= return  -- inst (>>=) (2)
--  === Nothing

-- monad3LawMaybe ::  Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Maybe c
-- monad3LawMaybe (Just a) k k' =
--      Just a >>= \x -> k x >>= k'  -- inst (>>=) (1)
--  === (\x -> k x >>= k') a         -- beta-reduction
--  === k a >>= k'                   -- inst (>>=) (1)
--  === (Just a >>= k) >>= k'
-- monad3LawMaybe Nothing k k' =
--      Nothing >>= \x -> k x >>= k' -- inst (>>=) (2)
--  === Nothing                      -- inst (>>=) (2)
--  === Nothing >>= k'               -- inst (>>=) (2)
--  === (Nothing >>= k) >>= k'          


--  -- Lists (TODO тут понадобятся гипотезы индукции, это второй этап)