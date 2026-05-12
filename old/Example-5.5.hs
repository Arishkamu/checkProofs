module ProofsMonad where
-- доказательства в виде равенств, не проверяемых системой содержательно, но контролируемых по типу 
-- псевдоэквивалентность, обеспечивает только правильность типизации
-- import ProofsBase ( (===) )
-- infixl 0 ===
-- (===) :: a -> a -> a
-- (===) = const

{-
СИНТАКСИС КОММЕНТАРИЕВ
eta-reduction     -- применена или контрпременена бета-редукция
Left Beta-reduction    -- применена или контрпременена эта-редукция

liftM             -- применено или контрпременено определение функции (NB должно быть доступно)
foldr (2)         -- применено или контрпременено определение функции (с уточнением конкретного равенства в определении) 

[theoremFunctor1] -- применена или контрпременена теорема

{POSTULATE}       -- не пруфчекаем переход, верим на слово

inst return       -- применено или контрпременено определение реализации метода представителя для класса типов 
                  -- (TODO надо ли указывать для какого типа? Или это всегда выводится?)


-}


type SideExprInfo = Either ExprInfo ExprInfo

-- lFunc str = Left (Func str)
-- rFunc str = Right (Func str)
-- lPostl str = Left (Postl str)
-- rPostl str = Right (Postl str)
-- Left Eta = Left Eta
-- Right Eta = Right Eta
-- Left Beta = Left Beta

data ExprInfo = Func String | Postl String | Beta | Eta | QED
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

(--.) :: a -> SideExprInfo -> a
(--.) x _ = x

postulate :: a -> a -> a
postulate = const

infixl 0 ===
(===) :: a -> a -> a
(===) x y = y


-- MY FUNCTIONS
infixr 9 =.
(=.)    :: (b -> c) -> (a -> b) -> a -> c
(=.) f g = \x -> f (g x)

infixr 0 =$
(=$)    :: (a -> b) -> a -> b
(=$) f x = f x

myId                      :: a -> a
myId x                    =  x

myFlip :: (a -> b -> c) -> b -> a -> c
myFlip f x y              =  f y x









--- ANOTHER FILE
composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc4 f g h =
    (f =. (g =. h))                   --. Left (Func "=.")
 === (\x -> f ((g =. h) x))          --. Left (Func "=.")
 === (\x -> f ((\x' -> g (h x')) x)) --. Left Beta
 === (\x -> f (g (h x)))             --. Left Beta
 === (\x -> (\x' -> f (g x')) (h x)) --. Right (Func "=.")
 === (\x -> (f =. g) (h x))          --. Right (Func "=.")
 === ((f =. g) =. h)                 --. Left QED


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
      (myId =. f)           --. Left (Func "=.")
 === (\x -> myId (f x))    --. Left (Func "myId")
 === (\x -> f x)           --. Left Eta
 === f                     --. Left QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
      (f =. myId)        --. Left (Func "=.")
 === (\x -> f (myId x)) --. Left (Func "myId")
 === (\x -> f x)        --. Left Eta
 === f                  --. Left QED


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
 === myId                                      --. Left QED

{- forall f x y. myFlip (myFlip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y =
      myFlip (myFlip f) x y  --. Left (Func "myFlip")
 === myFlip f y x           --. Left (Func "myFlip")
 === f x y                  --. Left QED






{- TODO надо продумать как давать канонические определения типа (.) и ($) и часто используемые теоремы типа ассоциативности композиции  -}

------------------------------------------------------------------
-- MonadLaws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}
-- postulates (это не доказывается, а является частью определения монады)
myM1 :: Monad m => a -> (a -> m b) -> m b
myM1 a k =
     (return a >>= k) -- {POSTULATE}
 `postulate` (k a)

myM2 :: Monad m => m a -> m a
myM2 m =
     (m >>= return)    -- {POSTULATE}
 `postulate` m

myM3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
myM3 m k k' =
     (m >>= k >>= k')   -- {POSTULATE}
 `postulate`  (m >>= \x -> k x >>= k')

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
theoremFunctor1 xs =
  (myLiftM myId xs)                      --. Left (Func "myLiftM")
  === (xs >>= return =. myId)           --. Left (Func "=.")
  === (xs >>= \x -> return (myId x))  --. Left (Func "myId")
  === (xs >>= \x -> return x)         --. Left Eta
  === (xs >>= return)                 --. Left (Postl "myM2")
  === xs                              --. Left QED
{-
2 Functor law
liftM (f . g) xs == liftM f (liftM g xs)
-}
theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
theoremFunctor2 f g xs =
       (myLiftM f (myLiftM g xs))                     --. Left (Func "myLiftM")-- liftM
  === (myLiftM f (xs >>= return =. g))               --. Left (Func "myLiftM")-- liftM
  === ((xs >>= return =. g) >>= return =. f)         --. Left (Postl "myM3")-- [m3]
  === (xs >>= \x -> (return =. g) x >>= return =. f) --. Left (Func "=.")-- (.)
  === (xs >>= \x -> return (g x) >>= return =. f)    --. Left (Postl "myM1")-- [m1]
  === (xs >>= \x -> (return =. f) (g x))             --. Right (Func "=.")-- (.)
  === (xs >>= \x -> ((return =. f) =. g) x)          --. Left Eta-- eta-reduction
  === (xs >>= (return =. f) =. g)                    --. Right (Postl "composeAssoc4")-- assoc (.) ?????????
  === (xs >>= return =. (f =. g))                    --. Right (Func "myLiftM")-- liftM
  === (myLiftM (f =. g) xs)                          --. Left QED

-- f =. (g =. h) === (f =. g) =. h

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
theoremApplicative0 g xs =
       (return g <*>.. xs)                --. Left (Func "<*>..")-- (<*>..)
  === (return g >>= \f -> myLiftM f xs)  --. Left (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f xs) g)           --. Left Beta-- Left Beta-reduction
  === (myLiftM g xs)                     --. Left QED

{-
1 Applicative law (Identity)
return id <*>.. xs  == xs
-}
theoremApplicative1 :: Monad m => m b -> m b
theoremApplicative1 xs =
       (return myId <*>.. xs)                 --. Left (Func "<*>..")-- (<*>..)
  === (return myId >>= \f -> myLiftM f xs)   --. Left (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f xs) myId)            --. Left Beta-- Left Beta-reduction
  === (myLiftM myId xs)                      --. Left (Postl "theoremFunctor1")-- [theoremFunctor1]
  === xs                                     --. Left QED

{-
2 Applicative law (Homomorphism)
return g <*>.. return x  == return (g x)
-}
theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
theoremApplicative2 g x =
       (return g <*>.. return x)                 --. Left (Func "<*>..")-- (<*>..)
  === (return g >>= \f -> myLiftM f (return x)) --. Left (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f (return x)) g)          --. Left Beta-- Left Beta-reduction
  === (myLiftM g (return x))                    --. Left (Func "myLiftM")-- myLiftM
  === (return x >>= return =. g)                --. Left (Postl "myM1")-- [m1]
  === ((return =. g) x )                        --. Left (Func "=.")-- (=.)
  === (return (g x))                             --. Left QED

{-
3 Applicative law (Interchange)
fs <*>.. return x  ===  return ($ x) <*>.. fs
-}
theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x =
       (fs <*>.. return x )         --. Left  (Postl "lemma1")-- [lemma1]
  === (fs >>= \f -> return (f x))  --. Right (Postl "lemma2")-- [lemma2]
  === (return (=$ x) <*>.. fs)      --. Left QED


lemma1 fs x = -- left hand side transformation
        (fs <*>.. return x )                     --. Left (Func "<*>..")-- (<*>..)
    === (fs >>= \f -> myLiftM f (return x))      --. Left (Func "myLiftM") -- myLiftM
    === (fs >>= \f -> return x >>= return =. f)  --. Left (Postl "myM1")-- [m1]
    === (fs >>= \f -> (return =. f) x )          --. Left (Func "=.")-- (=.)
    === (fs >>= \f -> return (f x))              --. Left QED

lemma2 fs x = -- right hand side transformation
        (return (=$ x) <*>.. fs)                --. Left (Func "<*>..")-- (<*>..)
    === (return (=$ x) >>= \f -> myLiftM f fs)  --. Left (Postl "myM1")-- [m1]
    === ((\f -> myLiftM f fs) (=$ x))           --. Left Beta-- Left Beta-reduction
    === (myLiftM (=$ x) fs )                    --. Left (Func "myLiftM")-- myLiftM
    === (fs >>= return =. (=$ x))               --. Left (Func "=.")-- (=.)
    === (fs >>= \f -> return ((=$ x) f))       --. Left (Func "=$")-- ($)
    === (fs >>= \f -> return (f x))            --. Left QED

-- Expected: App :: >>=
--   @m_a1mZ
--   $dMonad_a1n2
--   @(a_a1n0 -> b_a1n1)
--   @b_a1n1
--   fs_aBU
--   (\ (f_aBW :: a_a1n0 -> b_a1n1) ->
--      return @m_a1mZ $dMonad_a1n2 @b_a1n1 (f_aBW x_aBV))
-- Got: App :: <*>..
-- @m_a1mZ
-- @a_a1n0
-- @b_a1n1
-- $dMonad_a1n2
-- fs_aBU
-- (return @m_a1mZ $dMonad_a1n2 @a_a1n0 x_aBV)

{-
4 Applicative law (Composition)
return (.) <*>.. us <*>.. vs <*>.. xs  ==  us <*>.. (vs <*>.. xs)
-}
theoremApplicative4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
theoremApplicative4 us vs xs =
      (return (=.) <*>.. us <*>.. vs <*>.. xs )      --. Left (Postl "ta4_lemma1")-- [lemma1]
 === (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs) --. Right (Postl "ta4_lemma2")-- [lemma2]
 === (us <*>.. (vs <*>.. xs))                        --. Left QED

ta4_lemma1 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma1 us vs xs = -- left hand side transformation
      (return (=.) <*>.. us <*>.. vs <*>.. xs )                              --. Left (Func "<*>..")-- (<*>..)
 === ((return (=.) >>= \c -> myLiftM c us) <*>.. vs <*>.. xs)               --. Left (Postl "myM1")-- [m1]
 === ((\c -> myLiftM c us) (=.) <*>.. vs <*>.. xs)                          --. Left Beta-- Left Beta-reduction
 === (myLiftM (=.) us <*>.. vs <*>.. xs)                                    --. Left (Func "myLiftM")-- myLiftM
 === ((us >>= return =. (=.)) <*>.. vs <*>.. xs)                            --. Left (Func "<*>..")-- (<*>..)
 === (((us >>= return =. (=.)) >>= \r -> myLiftM r vs) <*>.. xs)            --. Left (Postl "myM3")-- [m3] 
 === ((us >>= \u -> (return =. (=.)) u >>= \r -> myLiftM r vs) <*>.. xs)    --. Left (Func "=.")-- (=.)
 === ((us >>= \u -> return (u =.) >>= \r -> myLiftM r vs) <*>.. xs)         --. Left (Postl "myM1")-- [m1]
 === ((us >>= \u -> (\r -> myLiftM r vs) (u =.)) <*>.. xs)                  --. Left Beta-- Left Beta-reduction
 === ((us >>= \u -> myLiftM (u =.) vs) <*>.. xs)                            --. Left (Func "myLiftM")-- myLiftM
 === ((us >>= \u -> vs >>= return =. (u =.)) <*>.. xs)                      --. Left (Func "<*>..")-- (<*>..)
 === ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         --. Left (Postl "myM3")
--  === ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         --. Left Beta-- [m3] + Left Beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
 === (us >>= \u -> vs >>= return =. (u =.) >>= \f -> myLiftM f xs)           --. Left (Postl "myM3")-- [m3] 
 === (us >>= \u -> vs >>= \v -> (return =. (u =.)) v >>= \f -> myLiftM f xs) --. Left (Func "=.")-- Left Beta-reduction
 === (us >>= \u -> vs >>= \v -> return  (u =. v) >>= \f -> myLiftM f xs)    --. Left (Postl "myM1")-- [m1]
 === (us >>= \u -> vs >>= \v ->  (\f -> myLiftM f xs) (u =. v))             --. Left Beta-- Left Beta-reduction
 === (us >>= \u -> vs >>= \v ->  myLiftM (u =. v) xs)                        --. Left QED

-- -- myM3 m k k' = (m >>= k >>= k')  `postulate`  (m >>= \x -> k x >>= k')

ta4_lemma2 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma2 us vs xs = -- right hand side transformation
      (us <*>.. (vs <*>.. xs) )                                   --. Left (Func "<*>..")-- (<*>..)
 === (us >>= \u -> myLiftM u (vs <*>.. xs))                      --. Left (Func "<*>..")-- (<*>..)
 === (us >>= \u -> myLiftM u (vs >>= \v -> myLiftM v xs))        --. Left (Func "myLiftM") -- myLiftM
 === (us >>= \u -> (vs >>= \v -> myLiftM v xs) >>= return =. u)  --. Left (Postl "myM3")-- [m3] + Left Beta-reduction ??????
--  === (us >>= \x -> (\u -> (vs >>= \v -> myLiftM v xs)) x >>= return =. u)  -- [m3] + Left Beta-reduction ??????
 === (us >>= \u -> vs >>= \v -> myLiftM v xs >>= return =. u)    --. Right (Func "myLiftM")-- myLiftM
 === (us >>= \u -> vs >>= \v -> myLiftM u (myLiftM v xs) )       --. Left (Postl "theoremFunctor2") -- [theoremFunctor2]
 === (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs)             --. Left QED

--------------------------------------------
-- Законы класса Monad

{-
Покажите, что из законов класса типов Monad 

return a >>= k   ==  k a                     -- m1
m >>= return     ==  m                       -- m2
(m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- m3

следует, что стрелки Клейсли образуют моноид относительно операции их композиции (>=>)
c return в качестве нейтрального элемента. Иными словами докажите, что верны равенства

return >=> k     ==  k
k >=> return     ==  k
(u >=> v) >=> w  ==  u >=> (v >=> w)
-}

-- Определение рыбки через >>=
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=> h = \x -> g x >>= h

-- return >=> k  ==  k
fishLeftNeutral :: Monad m => (a -> m b) -> a -> m b
fishLeftNeutral k =
      (return >=> k)         --. Left (Func ">=>") -- >=>
 === (\a -> return a >>= k) --. Left (Postl "myM1")-- [m1]
 === (\a -> k a)            --. Left Eta-- eta-reduction
 === k                      --. Left QED

-- k >=> return  ==  k
fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
fishRightNeutral k =
      (k >=> return)         --. Left (Func ">=>")  -- >=>
 === (\a -> k a >>= return) --. Left (Postl "myM2")-- [m2]
 === (\a -> k a)            --. Left Eta-- eta-reduction
 === k                      --. Left QED

-- (u >=> v) >=> w  ==  u >=> (v >=> w)
fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fishAssoc u v w =
      ((u >=> v) >=> w)                      --. Left (Func ">=>")-- >=>
 === (\a -> (u >=> v) a >>= w)              --. Left (Func ">=>")-- >=>
 === (\a -> (\a' -> u a' >>= v) a >>= w)    --. Left Beta-- Left Beta-reduction
 === (\a -> (u a >>= v) >>= w)              --. Left (Postl "myM3")-- [m3]
 === (\a -> u a >>= \b -> v b >>= w)        --. Right (Func ">=>")-- >=>
 === (\a -> u a >>= (v >=> w))              --. Right (Func ">=>")-- >=>
 === (u >=> (v >=> w))                      --. Left QED

-----------------------------------------------------

{-
Покажите, что законы

join . return       ==  id           -- mjfr1
join . fmap return  ==  id           -- mjfr2
join . fmap join    ==  join . join  -- mjfr3

следуют из законов класса типов Monad

return a >>= k   ==  k a                     -- [m1]
m >>= return     ==  m                       -- [m2]
(m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- [m3]

используя реализации join через (>>=) и liftM через (>>=) и return.
-- 
join x  =  x >>= id 
liftM f xs  =  xs >>= return . f 
-}

join :: Monad m => m (m a) -> m a
join x  =  x >>= myId 

--- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
--  join . return == id  -- :: m a -> m a
mjfr1 :: Monad m => m a -> m a
mjfr1 xs =
      ((join =. return) xs)   --. Left (Func "=.")-- (=.)
 === (join (return xs))      --. Left (Func "join")-- join
 === ( return xs >>= myId)   --. Left (Postl "myM1")-- [m1]
 === ( myId xs)              --. Left (Func "myId")-- myId
 === ( xs)                   --. Left QED -- myId

---
--   join . fmap return == id  -- :: m a -> m a
mjfr2 :: Monad m => m a -> m a
mjfr2 xs =
     ((join =. myLiftM return) xs )                 --. Left (Func "=.")-- (=.)
 === ( join (myLiftM return xs)  )                 --. Left (Func "join")-- join
 === ( myLiftM return xs >>= myId   )              --. Left (Func "myLiftM") -- myLiftM
 === ( xs >>= return =. return >>= myId  )         --. Left (Postl "myM3")-- [m3]
 === ( xs >>= \x -> (return =. return) x >>= myId) --. Left (Func "=.")-- (=.)
 === ( xs >>= \x -> return (return x) >>= myId)    --. Left (Postl "myM1")-- [m1]
 === ( xs >>= \x -> myId (return x))               --. Left (Func "myId")-- myId
 === ( xs >>= \x -> return x  )                    --. Left Eta-- eta-reduction
 === ( xs >>= return)                              --. Left (Postl "myM2")-- [m2]
 === ( xs      )                                   --. Right (Func "myId")-- myId
 === ( myId xs)                                    --. Left QED -- myId

---
--  join . fmap join  ==  join . join  -- :: m (m (m a)) -> m a
mjfr3 :: Monad m => m (m (m a)) -> m a
mjfr3 x3s =
     ((join =. myLiftM join) x3s  )                    --. Left (Func "=.")-- (=.)
 === ( join (myLiftM join x3s)     )                  --. Left (Func "myLiftM")-- myLiftM
 === ( join (x3s >>= return =. join) )                --. Left (Func "join")-- join
 === ( x3s >>= return =. join >>= myId )              --. Left (Postl "myM3")-- [m3]
 === ( x3s >>= \x2s -> (return =. join) x2s >>= myId) --. Left (Func "=.")-- (=.)
 === ( x3s >>= \x2s -> return (join x2s) >>= myId)    --. Left (Postl "myM1")-- [m1]
 === ( x3s >>= \x2s -> myId (join x2s))               --. Left (Func "myId")-- myId
 === ( x3s >>= \x2s -> join x2s     )                 --. Left (Func "join")-- join
 === ( x3s >>= \x2s -> x2s >>= myId )                 --. Right (Func "myId")-- myId
 === ( x3s >>= \x2s -> myId x2s >>= myId )            --. Left (Postl "myM3")-- [m3]
 === ( x3s >>= myId >>= myId )                        --. Right (Func "join")  -- join
 === ( join x3s >>= myId )                            --. Right (Func "join") -- join
 === ( join (join x3s)   )                            --. Right (Func "=.") -- (=.)
 === ( (join =. join) x3s)                            --. Left QED -- myId





----------------------------------------------------
----------------------------------------------------
-- Concrete Monad Laws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}

-- Maybe (TODO для пруфчекинга типы и их инстансы надо выписывать явно или иметь встроенный псевдобиблиотечный референс)
{-
instance  Monad Maybe  where
  Just x  >>= k  =  k x     -- (1)
  Nothing >>= _  =  Nothing -- (2)

  return  =  Just
-}
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
--  === (\x -> k x >>= k') a         -- Left Beta-reduction
--  === k a >>= k'                   -- inst (>>=) (1)
--  === (Just a >>= k) >>= k'
-- monad3LawMaybe Nothing k k' =
--      Nothing >>= \x -> k x >>= k' -- inst (>>=) (2)
--  === Nothing                      -- inst (>>=) (2)
--  === Nothing >>= k'               -- inst (>>=) (2)
--  === (Nothing >>= k) >>= k'          


 -- Lists (TODO тут понадобятся гипотезы индукции, это второй этап)