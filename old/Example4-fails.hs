module ProofsMonad where
-- type SideExprInfo = Either ExprInfo ExprInfo

-- lFunc str = Left (Func str)
-- rFunc str = Right (Func str)
-- lPostl str = Left (Postl str)
-- rPostl str = Right (Postl str)
-- Left Eta = Left Eta
-- Right Eta = Right Eta
-- Left Beta = Left Beta

-- data ExprInfo = Func String | Postl String | Beta | Eta
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

-- addInfo :: a -> SideExprInfo -> WithInfo a
-- addInfo x info = WithInfo x info

-- postulate :: a -> a -> a
-- postulate = const

-- infixl 0 ====
-- (====) :: WithInfo a -> WithInfo a -> WithInfo a
-- (====) x y = y

-- import ProofBase hiding ((.))
import ProofBase
import Prelude hiding ((.), id, ($), const, flip)

--------------------------------------------------------
class Functor m => AltMonad m where 
  ret :: a -> m a
  joi :: m (m a) -> m a

mjfr3 :: AltMonad m => m (m (m a)) -> m a
mjfr3  = 
     (joi . fmap joi)  --. Postulate
 === (joi . joi)       --. QED

(>=>..) :: AltMonad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=>.. h = joi . fmap h . g

-- (fish3)  (u >=> v) >=> w  ===  u >=> (v >=> w)
fish3 :: AltMonad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fish3 u v w =
     ((u >=>.. v) >=>.. w)                           --. Postulate
 === ((joi . joi) . fmap (fmap w) . fmap v . u)      --. R (Prop "mjfr3")
 === ((joi . fmap joi) . fmap (fmap w) . fmap v . u) --. QED
-- mjfr3  = 
--      (joi . fmap joi) === (joi . joi)       --. QED




{-
(--.
   @(a_aZm -> m_aZl d_aZp)
   (. @(m_aZl (m_aZl (m_aZl d_aZp)))
      @(m_aZl d_aZp)
      @a_aZm
      (. @(m_aZl (m_aZl d_aZp))
         @(m_aZl d_aZp)
         @(m_aZl (m_aZl (m_aZl d_aZp)))
         (joi @m_aZl $dAltMonad_aZq @d_aZp)
         (joi @m_aZl $dAltMonad_aZq @(m_aZl d_aZp)))
      (. @(m_aZl (m_aZl c_aZo))
         @(m_aZl (m_aZl (m_aZl d_aZp)))
         @a_aZm
         (fmap
            @m_aZl
            ($p1AltMonad @m_aZl $dAltMonad_aZq)
            @(m_aZl c_aZo)
            @(m_aZl (m_aZl d_aZp))
            (fmap
               @m_aZl
               ($p1AltMonad @m_aZl $dAltMonad_aZq)
               @c_aZo
               @(m_aZl d_aZp)
               w_aWp))
         (. @(m_aZl b_aZn)
            @(m_aZl (m_aZl c_aZo))
            @a_aZm
            (fmap
               @m_aZl
               ($p1AltMonad @m_aZl $dAltMonad_aZq)
               @b_aZn
               @(m_aZl c_aZo)
               v_aWo)
            u_aWn)))
   (R (Prop (unpackCString# "mjfr3"#)))))
(--.
   @(a_aZm -> m_aZl d_aZp)
   (. @(m_aZl (m_aZl (m_aZl d_aZp)))
      @(m_aZl d_aZp)
      @a_aZm
      (. @(m_aZl (m_aZl d_aZp))
         @(m_aZl d_aZp)
         @(m_aZl (m_aZl (m_aZl d_aZp)))
         (joi @m_aZl $dAltMonad_aZq @d_aZp)
         (fmap
            @m_aZl
            ($p1AltMonad @m_aZl $dAltMonad_aZq)
            @(m_aZl (m_aZl d_aZp))
            @(m_aZl d_aZp)
            (joi @m_aZl $dAltMonad_aZq @d_aZp)))
      (. @(m_aZl (m_aZl c_aZo))
         @(m_aZl (m_aZl (m_aZl d_aZp)))
         @a_aZm
         (fmap
            @m_aZl
            ($p1AltMonad @m_aZl $dAltMonad_aZq)
            @(m_aZl c_aZo)
            @(m_aZl (m_aZl d_aZp))
            (fmap
               @m_aZl
               ($p1AltMonad @m_aZl $dAltMonad_aZq)
               @c_aZo
               @(m_aZl d_aZp)
               w_aWp))
         (. @(m_aZl b_aZn)
            @(m_aZl (m_aZl c_aZo))
            @a_aZm
            (fmap
               @m_aZl
               ($p1AltMonad @m_aZl $dAltMonad_aZq)
               @b_aZn
               @(m_aZl c_aZo)
               v_aWo)
            u_aWn)))
       QED)

-}




-- data SideExprInfo = L ExprInfo | R ExprInfo | QED | Postulate
-- data ExprInfo = Def  String | Prop String | Beta | Eta
-- -- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

-- (--.) :: a -> SideExprInfo -> a
-- (--.) x _ = x

-- -- postulate :: a -> a -> a
-- -- postulate = const

-- infixl 0 ===
-- (===) :: a -> a -> a
-- (===) x y = y


-- -- MY FUNCTIONS
-- infixr 9 .
-- (.)    :: (b -> c) -> (a -> b) -> a -> c
-- (.) f g = \x -> f (g x)

-- infixr 0 $
-- ($)    :: (a -> b) -> a -> b
-- ($) f x = f x

-- id                      :: a -> a
-- id x                    =  x

-- flip :: (a -> b -> c) -> b -> a -> c
-- flip f x y              =  f y x


-- m1 :: Monad m => a -> (a -> m b) -> m b
-- m1 a k =
--      (return a >>= k) --. Postulate
--  === (k a)            --. QED

-- m2 :: Monad m => m a -> m a
-- m2 m =
--      (m >>= return) --. Postulate
--  === m              --. QED

-- m3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
-- m3 m k k' =
--      (m >>= k >>= k')          --. Postulate
--  ===  (m >>= \x -> k x >>= k') --. QED

-- {-
-- Покажите, что каждая монада - это функтор. 
-- Для этого выразите fmap через (>>=) и return:
-- -}
-- liftM :: Monad m => (a -> b) -> m a -> m b
-- liftM f xs  =  xs >>= return . f

-- (<*>..) :: Monad m => m (a -> b) -> m a -> m b
-- fs <*>.. xs = fs >>= \f -> liftM f xs -- см. liftM выше

-- theoremFunctor1 :: Monad m => m b -> m b
-- theoremFunctor1 xs =
--   (myLiftM myId xs)                      --. L (Func "myLiftM")
--   === (xs >>= return =. myId)           --. L (Func "=.")
--   === (xs >>= \x -> return (myId x))  --. L (Func "myId")
--   === (xs >>= \x -> return x)         --. L Eta
--   === (xs >>= return)                 --. L (Postl "myM2")
--   === xs                              --. QED

-- theoremApplicative1 :: Monad m => m b -> m b
-- theoremApplicative1 xs =
--        (return myId <*>.. xs)                 --. L (Func "<*>..")-- (<*>..)
--   === (return myId >>= \f -> myLiftM f xs)   --. L (Postl "myM1")-- [m1]
--   === ((\f -> myLiftM f xs) myId)            --. L Beta-- L Beta-reduction
--   === (myLiftM myId xs)                      --. L (Postl "theoremFunctor1")-- [theoremFunctor1]
--   === xs                                     --. QED

-- theoremFunctor1 :: Monad m => m b -> m b
-- theoremFunctor1 xs = value (
--   (myLiftM myId xs)                      `addInfo` Left (Func "myLiftM")
--   ==== (xs >>= return =. myId)           `addInfo` Left (Func "=.")
--   ==== (xs >>= \x -> return (myId x))  `addInfo` Left (Func "myId")
--   ==== (xs >>= \x -> return x)         `addInfo` Left Eta
--   ==== (xs >>= return)                 `addInfo` Left (Postl "myM2")
--   ==== xs                              `addInfo` Left Beta)

-- fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
-- fishAssoc u v w = value (
--       ((u >=> v) >=> w)                      `addInfo` Left (Func ">=>")-- >=>
--  ==== (\a -> (u >=> v) a >>= w)              `addInfo` Left (Func ">=>")-- >=>
--  ==== (\a -> (\a' -> u a' >>= v) a >>= w)    `addInfo` Left Beta-- Left Beta-reduction
--  ==== (\a -> (u a >>= v) >>= w)              `addInfo` Left (Postl "myM3")-- [m3]
--  ==== (\a -> u a >>= \b -> v b >>= w)        `addInfo` Right (Func ">=>")-- >=>
--  ==== (\a -> u a >>= (v >=> w))              `addInfo` Right (Func ">=>")-- >=>
--  ==== (u >=> (v >=> w))                      `addInfo` Left Beta)

-- no diff example
-- theoremFunctor1 :: Monad m => m b -> m b
-- theoremFunctor1 xs = value (
--   (myLiftM myId xs)                      `addInfo` Left (Func "myLiftM")
--   ==== (xs >>= return =. myId)           `addInfo` Left (Func "=.")
--   ==== (xs >>= \x -> return (myId x))  `addInfo` Left (Func "myId")
--   ==== (xs >>= \x -> return x)         `addInfo` Left Eta
--   ==== (xs >>= return)                 `addInfo` Left (Postl "myM")
--   ==== xs                              `addInfo` Left Beta)

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

{- forall f x y. myFlip (myFlip f) x y ==== f x y -}
-- flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
-- flipFlipIsId' f x y = value (
--       myFlip (myFlip f) x y  `addInfo` Left (Func "myFlip")
--  ==== myFlip f y x           `addInfo` Left (Func "myFlip")
--  ==== f x y                  `addInfo` Left Eta)

-- myConst :: a -> b -> a
-- myConst x y = x

-- id2Id2IsId2' :: a -> b -> a
-- id2Id2IsId2' x y = value (
--       myConst (myConst x y) y  `addInfo` Left (Func "myConst")
--  ==== myConst x y           `addInfo` Left (Func "myConst")
--  ==== x                  `addInfo` Left Eta)

-- id2Id2IsId2'' :: a -> b -> a
-- id2Id2IsId2'' x y = value (
--       myConst (myConst x y) y  `addInfo` Left (Func "myConst")
--  ==== myConst x y           `addInfo` Left (Func "myConst")
--  ==== x                  `addInfo` Left Eta)


-- flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
-- flipFlipIsId' f x y = value (
--       myFlip (myFlip f) x y                `addInfo` Left (Func "myFlip")
--  ==== (myFlip (\x1 -> (\y1 ->  f y1 x1)) x y)    `addInfo` Left (Func "myFlip")
--  ==== ((\x1 -> (\y1 ->  f y1 x1)) y x)           `addInfo` Left Beta
-- --  ==== myFlip f y x                         `addInfo` Left (Func "myFlip")
--  ==== f x y                                `addInfo` Left Eta)
{-
                  (myFlip
                     @b_a12m
                     @a_a12l
                     @c_a12n
                     (myFlip @a_a12l @b_a12m @c_a12n f_aT8)
                     x_aT9
                     y_aTa)
                  (Left @ExprInfo @ExprInfo (Func (unpackCString# "myFlip"#))))
               (addInfo
                  @c_a12n
                  (myFlip @a_a12l @b_a12m @c_a12n f_aT8 y_aTa x_aT9)
                  (Left @ExprInfo @ExprInfo (Func (unpackCString# "myFlip"#)))))
-}
{-
               (addInfo
                  @c_aJc
                  (myFlip
                     @b_aJb
                     @a_aJa
                     @c_aJc
                     (myFlip @a_aJa @b_aJb @c_aJc f_azz)
                     x_azA
                     y_azB)
                  (Left @ExprInfo @ExprInfo (Func (unpackCString# "myFlip"#))))
               (addInfo
                  @c_aJc
                  (myFlip @b_aJb @a_aJa @c_aJc
                     (\ (x1_azI :: b_aJb) (y1_azJ :: a_aJa) -> f_azz y1_azJ x1_azI)
                     x_azA
                     y_azB)
                  (Left @ExprInfo @ExprInfo (Func (unpackCString# "myFlip"#)))))
-}
-- theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
-- theoremFunctor2 f g xs = value (
--        (myLiftM f (myLiftM g xs))                     `addInfo` Left (Func "myLiftM")-- liftM
--   ==== (myLiftM f (xs >>= return =. g))               `addInfo` Left (Func "myLiftM")-- liftM
--   ==== ((xs >>= return =. g) >>= return =. f)         `addInfo` Left (Postl "myM3")-- [m3]
--   ==== (xs >>= \x -> (return =. g) x >>= return =. f) `addInfo` Left (Func "=.")-- (.)
--   ==== (xs >>= \x -> return (g x) >>= return =. f)    `addInfo` Left (Postl "myM1")-- [m1]
--   ==== (xs >>= \x -> (return =. f) (g x))             `addInfo` Right (Func "=.")-- (.)
--   ==== (xs >>= \x -> ((return =. f) =. g) x)          `addInfo` Left Eta-- eta-reduction
--   ==== (xs >>= (return =. f) =. g)                    `addInfo` Right (Postl "composeAssoc4")-- assoc (.) ?????????
--   ==== (xs >>= return =. (f =. g))                    `addInfo` Right (Func "myLiftM")-- liftM
--   ==== (myLiftM (f =. g) xs)                          `addInfo` Left Beta)


-- lemma1 fs x = value (-- left hand side transformation
--         (fs <*>.. return x )                     `addInfo` Left (Func "<*>..")-- (<*>..)
--     ==== (fs >>= \f -> myLiftM f (return x))      `addInfo` Left (Func "myLiftM") -- myLiftM
--     ==== (fs >>= \f -> return x >>= return =. f)  `addInfo` Left (Postl "myM1")-- [m1]
--     ==== (fs >>= \f -> (return =. f) x )          `addInfo` Left (Func "=.")-- (=.)
--     ==== (fs >>= \f -> return (f x))              `addInfo` Left Beta)

-- lemma1_op fs x = value (-- left hand side transformation
--           (fs >>= \f -> return (f x))              `addInfo` Right (Func "=.")
--      ==== (fs >>= \f -> (return =. f) x )          `addInfo` Right (Postl "myM1")
--      ==== (fs >>= \f -> return x >>= return =. f)  `addInfo` Right (Func "myLiftM")
--      ==== (fs >>= \f -> myLiftM f (return x))      `addInfo` Right (Func "<*>..")
--      ==== (fs <*>.. return x )                     `addInfo` Left Beta)

-- -- lemma1_op_postl fs x = () `postulate` ()

-- lemma1 fs x = value (-- left hand side transformation
--         (fs <*>.. return x )                     `addInfo` Left (Func "<*>..")-- (<*>..)
--     ==== (fs >>= \f -> myLiftM f (return x))      `addInfo` Left (Func "myLiftM") -- myLiftM
--     ==== (fs >>= \f -> return x >>= return =. f)  `addInfo` Left (Postl "myM1")-- [m1]
--     ==== (fs >>= \f -> (return =. f) x )          `addInfo` Left (Func "=.")-- (=.)
--     ==== (fs >>= \f -> return (f x))              `addInfo` Left Beta)

-- lemma2 fs x = value (-- right hand side transformation
--         (return (=$ x) <*>.. fs)                `addInfo` Left (Func "<*>..")-- (<*>..)
--     ==== (return (=$ x) >>= \f -> myLiftM f fs)  `addInfo` Left (Postl "myM1")-- [m1]
--     ==== ((\f -> myLiftM f fs) (=$ x))           `addInfo` Left Beta-- Left Beta-reduction
--     ==== (myLiftM (=$ x) fs )                    `addInfo` Left (Func "myLiftM")-- myLiftM
--     ==== (fs >>= return =. (=$ x))               `addInfo` Left (Func "=.")-- (=.)
--     ==== (fs >>= \f -> return ((=$ x) f))       `addInfo` Left (Func "=$")-- ($)
--     ==== (fs >>= \f -> return (f x))            `addInfo` Left Beta)

-- theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
-- theoremApplicative3 fs x = value (
--        (fs <*>.. return x )         `addInfo` Right (Postl "lemma1_op")-- [lemma1]
--   ==== (fs >>= \f -> return (f x))  `addInfo` Right (Postl "lemma2")-- [lemma2]
--   ==== (return (=$ x) <*>.. fs)      `addInfo` Left Beta)

-- composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc4 f g h = value (
--     (f =. (g =. h))                   `addInfo` Left (Func "=.")
--  ==== (\x -> f ((g =. h) x))          `addInfo` Left (Func "=.")
--  ==== (\x -> f ((\x' -> g (h x')) x)) `addInfo` Left Beta
--  ==== (\x -> f (g (h x)))             `addInfo` Left Beta
--  ==== (\x -> (\x' -> f (g x')) (h x)) `addInfo` Right (Func "=.")
--  ==== (\x -> (f =. g) (h x))          `addInfo` Right (Func "=.")
--  ==== ((f =. g) =. h)                 `addInfo` Left Beta)


-- theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
-- theoremFunctor2 f g xs = value (
--        (myLiftM f (myLiftM g xs))                     `addInfo` Left (Func "myLiftM")-- liftM
--   ==== (myLiftM f (xs >>= return =. g))               `addInfo` Left (Func "myLiftM")-- liftM
--   ==== ((xs >>= return =. g) >>= return =. f)         `addInfo` Left (Postl "myM3")-- [m3]
--   ==== (xs >>= \x -> (return =. g) x >>= return =. f) `addInfo` Left (Func "=.")-- (.)
--   ==== (xs >>= \x -> return (g x) >>= return =. f)    `addInfo` Left (Postl "myM1")-- [m1]
--   ==== (xs >>= \x -> (return =. f) (g x))             `addInfo` Right (Func "=.")-- (.)
--   ==== (xs >>= \x -> ((return =. f) =. g) x)          `addInfo` Left Eta-- eta-reduction
--   ==== (xs >>= (return =. f) =. g)                    `addInfo` Right (Postl "composeAssoc4")-- assoc (.) ?????????
--   ==== (xs >>= return =. (f =. g))                    `addInfo` Right (Func "myLiftM")-- liftM
--   ==== (myLiftM (f =. g) xs)                          `addInfo` Left Beta)

-- -}
{-
      --   l_pstl: App :: =. @c_aUX @d_aUY @a_aV0 f_aAq (=. @b_aUZ @c_aUX @a_aV0 g_aAr h_aAs)
        -- r_pstl: App :: =. @b_aUZ @d_aUY @a_aV0 (=. @c_aUX @d_aUY @b_aUZ f_aAq g_aAr) h_aAs

  (=.
     @b_a14x
     @(m_a14w c_a14y)
     @a_a14z
     (=.
        @c_a14y
        @(m_a14w c_a14y)
        @b_a14x
        (return @m_a14w $dMonad_a14A @c_a14y)
        f_aBl)
     g_aBm)

  (=.
     @c_a14y
     @(m_a14w c_a14y)
     @a_a14z
     (return @m_a14w $dMonad_a14A @c_a14y)
     (=. @b_a14x @c_a14y @a_a14z f_aBl g_aBm))
  (=.
     @b_a14x
     @(m_a14w c_a14y)
     @a_a14z
     (=. 
        @c_a14y 
        @(m_a14w c_a14y) 
        @b_a14x 
        (return @m_a14w $dMonad_a14A @c_a14y) 
        f_aBl) 
     g_aBm)
  
  Expected:
  (=.
     @b_a14x
     @(m_a14w c_a14y)
     @a_a14z
     (=.
        @c_a14y
        @(m_a14w c_a14y)
        @b_a14x
        (return @m_a14w $dMonad_a14A @c_a14y)
        f_aBl)
     g_aBm)
  Got:
  (=.
     @c_a14y
     @(m_a14w c_a14y)
     @a_a14z
     (return @m_a14w $dMonad_a14A @c_a14y)
     (=. @b_a14x @c_a14y @a_a14z f_aBl g_aBm))
  
-}


-- (m >>= k >>= k') === (m >>= \x -> (k x >>= k'))
-- ==== ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         `addInfo` Left Beta-- [m3] + Left Beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
-- ==== (us >>= \v -> (\u -> vs >>= return =. (u =.) >>= \f -> myLiftM f xs) v)
-- ==== ((us >>= \v -> vs >>= return =. (v =.)) >>= \f -> myLiftM f xs)
-- ==== ( us >>= \u -> vs >>= return =. (u =.)  >>= \f -> myLiftM f xs)
-- (addInfo
--    @(m_a1sJ c_a1sL)
--    (>>=
--       @m_a1sJ
--       $dMonad_a1sN
--       @(a_a1sM -> c_a1sL)
--       @c_a1sL
--       (>>=
--          @m_a1sJ
--          $dMonad_a1sN
--          @(b_a1sK -> c_a1sL)
--          @(a_a1sM -> c_a1sL)
--          us_aCh
--          (\ (u_aCv :: b_a1sK -> c_a1sL) ->
--             >>=
--             @m_a1sJ
--             $dMonad_a1sN
--             @(a_a1sM -> b_a1sK)
--             @(a_a1sM -> c_a1sL)
--             vs_aCi
--             (=.
--                @(a_a1sM -> c_a1sL)
--                @(m_a1sJ (a_a1sM -> c_a1sL))
--                @(a_a1sM -> b_a1sK)
--                (return @m_a1sJ $dMonad_a1sN @(a_a1sM -> c_a1sL))
--                (=. @b_a1sK @c_a1sL @a_a1sM u_aCv))))
--       (\ (f_aCw :: a_a1sM -> c_a1sL) ->
--          myLiftM @m_a1sJ @a_a1sM @c_a1sL $dMonad_a1sN f_aCw xs_aCj))
--    (Left @ExprInfo @ExprInfo Beta)))
-- (addInfo
-- @(m_a1sJ c_a1sL)
-- (>>=
--    @m_a1sJ
--    $dMonad_a1sN
--    @(b_a1sK -> c_a1sL)
--    @c_a1sL
--    us_aCh
--    (\ (u_aCx :: b_a1sK -> c_a1sL) ->
--       >>=
--       @m_a1sJ
--       $dMonad_a1sN
--       @(a_a1sM -> c_a1sL)
--       @c_a1sL
--       (>>=
--          @m_a1sJ
--          $dMonad_a1sN
--          @(a_a1sM -> b_a1sK)
--          @(a_a1sM -> c_a1sL)
--          vs_aCi
--          (=.
--             @(a_a1sM -> c_a1sL)
--             @(m_a1sJ (a_a1sM -> c_a1sL))
--             @(a_a1sM -> b_a1sK)
--             (return @m_a1sJ $dMonad_a1sN @(a_a1sM -> c_a1sL))
--             (=. @b_a1sK @c_a1sL @a_a1sM u_aCx)))
--       (\ (f_aCy :: a_a1sM -> c_a1sL) ->
--          myLiftM @m_a1sJ @a_a1sM @c_a1sL $dMonad_a1sN f_aCy xs_aCj)))
-- (Left @ExprInfo @ExprInfo (Postl (unpackCString# "myM3"#)))))














--  ==== (
--    us >>= 
--    (\u -> 
--       vs >>= 
--       (\v -> 
--          ((return =. (u =.)) v) >>= 
--          (\f -> myLiftM f xs)))) `addInfo` Left Beta-- Left Beta-reduction
--  ==== (
--    us >>= 
--    (\u -> 
--       vs >>= 
--       (\v -> 
--          (return  (u =. v)) >>= 
--          (\f -> myLiftM f xs))))
-- (addInfo
--    @(m_a3iV c_a3iX)
--    (>>=
--       @m_a3iV
--       $dMonad_a3iZ
--       @(b_a3iW -> c_a3iX)
--       @c_a3iX
--       us_a2sL
--       (\ (u_a2t3 :: b_a3iW -> c_a3iX) ->
--          >>=
--          @m_a3iV
--          $dMonad_a3iZ
--          @(a_a3iY -> b_a3iW)
--          @c_a3iX
--          vs_a2sM
--          (\ (v_a2t4 :: a_a3iY -> b_a3iW) ->
--             >>=
--                @m_a3iV
--                $dMonad_a3iZ
--                @(a_a3iY -> c_a3iX)
--                @c_a3iX
--                (=.
--                   @(a_a3iY -> c_a3iX)
--                   @(m_a3iV (a_a3iY -> c_a3iX))
--                   @(a_a3iY -> b_a3iW)
--                   (return @m_a3iV $dMonad_a3iZ @(a_a3iY -> c_a3iX))
--                   (=. @b_a3iW @c_a3iX @a_a3iY u_a2t3)
--                   v_a2t4)
--                (\ (f_a2t5 :: a_a3iY -> c_a3iX) ->
--                   myLiftM @m_a3iV @a_a3iY @c_a3iX $dMonad_a3iZ f_a2t5 xs_a2sN))))
--    (Left @ExprInfo @ExprInfo Beta)))
-- (addInfo
-- @(m_a3iV c_a3iX)
-- (>>=
--    @m_a3iV
--    $dMonad_a3iZ
--    @(b_a3iW -> c_a3iX)
--    @c_a3iX
--    us_a2sL
--    (\ (u_a2t6 :: b_a3iW -> c_a3iX) ->
--       >>=
--       @m_a3iV
--       $dMonad_a3iZ
--       @(a_a3iY -> b_a3iW)
--       @c_a3iX
--       vs_a2sM
--       (\ (v_a2t7 :: a_a3iY -> b_a3iW) ->
--          >>=
--             @m_a3iV
--             $dMonad_a3iZ
--             @(a_a3iY -> c_a3iX)
--             @c_a3iX
--             (return
--                @m_a3iV
--                $dMonad_a3iZ
--                @(a_a3iY -> c_a3iX)
--                (=. @b_a3iW @c_a3iX @a_a3iY u_a2t6 v_a2t7))
--             (\ (f_a2t8 :: a_a3iY -> c_a3iX) ->
--                myLiftM @m_a3iV @a_a3iY @c_a3iX $dMonad_a3iZ f_a2t8 xs_a2sN))))
-- (Left @ExprInfo @ExprInfo (Postl (unpackCString# "myM1"#)))))

-- myConst :: a -> b -> a
-- myConst x _ = x

-- myConstConst :: Int
-- myConstConst = 
--    (myConst myConst 1 42 2) --. L (Func "myConst")
--  === (myConst 42 2)         --. L (Func "myConst")
--  === 42                     --. QED


-- myConstConstConst :: Int
-- myConstConstConst = 
--      (myConst myConst myConst 42 2) --. L (Func "myConst")
--  === (myConst 42 2)                 --. L (Func "myConst")
--  === 42                             --. QED

-- myFoldl :: (a -> b -> a) -> a -> [b] -> a  
-- myFoldl f z [] = z
-- myFoldl f z (x:xs) = myFoldl f (f z x) xs

-- myAdd :: Int -> Int -> Int
-- myAdd 10 c = c
-- myAdd n c = myAdd (n + 1) c

-- mySub :: [a] -> Int
-- mySub xs = 10

-- mySub_postl :: [a] -> Int
-- mySub_postl (x:xs) =
--    case xss of
--       (x:xs)
--      mySub (x:xs)       --. Postulate
--  === mySub xs --. QED

-- {-# INLINE mySub #-}
-- {-# RULES
-- "mySun_postl/base"
--   forall .
--     mySub [] = 0
-- #-}
-- {-# RULES
-- "mySun_postl/mmm"
--   forall (x :: a) (xs :: [a]).
--     mySub (x:xs) = mySub xs
-- #-}

-- mySubDecl :: [a] -> Int
-- mySubDecl xss =
--        (mySub xss)        --. L (Prop "mySub_postl")
--    === (mySub xss)  --. QED

-- myFoldl_2_postl :: (a -> b -> a) -> a -> [b] -> a  
-- myFoldl_2_postl f z (x:xs) = 
--        (myFoldl f z (x:xs))   --. Postulate
--    === (myFoldl f (f z x) xs) --. QED

-- -- {-# RULES
-- -- "myFoldl_2_postl/mmm"
-- --   forall (f :: a -> b -> a) (z :: a) (xss :: [b]).
-- --     (myFoldl_2 f z xss) = z
-- -- #-}

-- foldlMy :: a -> [b] -> a
-- foldlMy z xss = 
--    myFoldl myConst z xss         --. L (Func "myFoldl")
--  === myFoldl myConst (myConst z (head xss)) (tail xss) --. QED


-- --  Actualy, the problem with diff is only
-- -- 

-- foldlMy :: (a -> b -> a) -> a -> [b] -> a
-- foldlMy f z (x:xs) = 
--    myFoldl f z (x:xs)           --. L (Prop "myFoldl_2_postl")
--  === myFoldl f (myConst z x) xs --. L (DeclRec "myConst" 1)
--  === myFoldl (\a b -> a) (myConst z x) xs             --. QED


-- composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
-- composeAssoc4 f g h =
--     (f =. (g =. h))                   --. L (Func "=.")
--  === (\x -> f ((g =. h) x))          --. L (Func "=.")
--  === (\x -> f ((\x' -> g (h x')) x)) --. L Beta
--  === (\x -> f (g (h x)))             --. L Beta
--  === (\x -> (\x' -> f (g x')) (h x)) --. R (Func "=.")
--  === (\x -> (f =. g) (h x))          --. R (Func "=.")
--  === ((f =. g) =. h)                 --. QED

-- lemma2 fs x = -- R hand side transformation
--         (return (=$ x) <*>.. fs)                --. L (Func "<*>..")-- (<*>..)
--     === (return (=$ x) >>= \f -> myLiftM f fs)  --. L (Postl "myM1")-- [m1]
--     === ((\f -> myLiftM f fs) (=$ x))           --. L Beta-- L Beta-reduction
--    --  myLiftM f xs  =  xs >>= return =. f
--     === (myLiftM (=$ x) fs )                    --. L (Func "myLiftM")-- myLiftM
--    --  fs >>= return =. (=$ x)
--     === (fs >>= return =. (=$ x))               --. L (Func "=.")-- (=.)
--    --  fs >>= return =. (\v -> v =$ x)
--    --  (=.) f g = \x -> f (g x)
--    -- fs >>= \f -> return ((\v -> v =$ x) f)
--    -- fs >>= \f -> return ((\v -> v =$ x) f)
--     === (fs >>= \f -> return (f =$ x))       --. L (Func "=$")-- ($)
--     === (fs >>= \f -> return (f x))            --. QED

-- theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
-- theoremApplicative0 g xs =
--        (return g <*>.. xs)             --. L (Def  "<*>..")-- (<*>..)
--   === (return g >>= \f -> liftM f xs)  --. L (Prop "m1")-- [m1]
--   === ((\f -> liftM f xs) g)           --. L Beta-- L Beta-reduction
--   === (liftM g xs)                     --. QED

-- theorem :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m (a -> c)
-- theorem us vs xs = 
--        ((return (.) >>= \c -> liftM c us) <*>.. vs) --. L (Prop "m1")
--    === (((\c -> liftM c us) (.)) <*>.. vs)         --. QED

-- ta4_lemma1 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
-- ta4_lemma1 us vs xs = -- L hand side transformation
--       (return (.) <*>.. us <*>.. vs <*>.. xs )                            --. L (Def  "<*>..")-- (<*>..)
--  === ((return (.) >>= \c -> liftM c us) <*>.. vs <*>.. xs)                --. L (Prop "m1")-- [m1]
--  === ((\c -> liftM c us) (.) <*>.. vs <*>.. xs)                           --. L Beta-- L Beta-reduction
--  === (liftM (.) us <*>.. vs <*>.. xs)                                     --. L (Def  "liftM")-- liftM
--  === ((us >>= return . (.)) <*>.. vs <*>.. xs)                            --. L (Def  "<*>..")-- (<*>..)
--  === (((us >>= return . (.)) >>= \r -> liftM r vs) <*>.. xs)              --. L (Prop "m3")-- [m3] 
--  === ((us >>= \u -> (return . (.)) u >>= \r -> liftM r vs) <*>.. xs)      --. L (Def  ".")-- (.)
--  === ((us >>= \u -> return (u .) >>= \r -> liftM r vs) <*>.. xs)          --. L (Prop "m1")-- [m1]
--  === ((us >>= \u -> (\r -> liftM r vs) (u .)) <*>.. xs)                   --. L Beta-- L Beta-reduction
--  === ((us >>= \u -> liftM (u .) vs) <*>.. xs)                             --. L (Def  "liftM")-- liftM
--  === ((us >>= \u -> vs >>= return . (u .)) <*>.. xs)                      --. L (Def  "<*>..")-- (<*>..)
--  === ((us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs)          --. L (Prop "m3")
-- --  === ((us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs)         --. L Beta-- [m3] + L Beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
--  === (us >>= \u -> vs >>= return . (u .) >>= \f -> liftM f xs)            --. L (Prop "m3")-- [m3] 
--  === (us >>= \u -> vs >>= \v -> (return . (u .)) v >>= \f -> liftM f xs)  --. L (Def  ".")-- L Beta-reduction
--  === (us >>= \u -> vs >>= \v -> return  (u . v) >>= \f -> liftM f xs)     --. L (Prop "m1")-- [m1]
--  === (us >>= \u -> vs >>= \v ->  (\f -> liftM f xs) (u . v))              --. L Beta-- L Beta-reduction
--  === (us >>= \u -> vs >>= \v ->  liftM (u . v) xs)                        --. QED