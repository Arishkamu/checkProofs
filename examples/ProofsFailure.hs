module ProofsFailure where
import ProofBase
import Prelude hiding ((.), id, ($), const, flip, Monad(..))


class Applicative m => Monad m where
    (>>=) :: m a -> (a -> m b) -> m b 
    return :: a -> m a

instance  Monad ((->) e)  where
  f  >>= k  = \r -> k (f r) r     -- (1)
  return  =  const

myConst :: a -> b -> a
myConst = const 

monad2LawArrow_wrongDef :: (a -> a) -> (a -> a)
monad2LawArrow_wrongDef f =
     (f >>= return)           --. L (Inst ">>=")
 === (\r -> return  (f r) r)  --. L (Inst "return")
 === (\r -> myConst (f r) r)  --. L (Def  "myConst")
 === (\r -> f r)              --. L Eta
 === f                        --. QED



class Functor m => AltMonad m where 
  ret :: a -> m a
  joi :: m (m a) -> m a

(>=>..) :: AltMonad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=>.. h = joi . fmap h . g

fish2_skipStep :: AltMonad m => (a -> m b) -> a -> m b
fish2_skipStep k = 
     (k >=>.. ret)          --. L (Def  ">=>..")
--   (joi . fmap ret . k)   --. L (Prop "composeAssoc")
 === ((joi . fmap ret) . k) --. L (Prop "mjfr2")
 === (id . k)               --. L (Prop "composeLeftNeutral")
 === k                      --. QED


{-
app1Law_cyrcle :: Applicative f => f a -> f a
app1Law_cyrcle as =
     pure id <*> as   --. L (Prop "a0_cyrcle")
 === fmap id as       --. L (Prop "f1")
 === id as            --. L (Def  "id")
 === as               --. QED


a0_cyrcle :: Applicative f => f a -> f a
a0_cyrcle as  =
     pure id <*> as  --. L (Prop "app1Law_cyrcle")
 === as              --. R (Inst "fmap")
 === fmap id as      --. QED
-}




