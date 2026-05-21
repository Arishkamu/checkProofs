module MyMonadArrow where
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях

import Prelude hiding ((.), id, ($), const, flip, Monad(..), map, concat, foldr, (++))

------------------------------------------------------------------
infixl 1 >>=

class Applicative m => Monad m where
    (>>=) :: m a -> (a -> m b) -> m b 
    return :: a -> m a




instance  Monad ((->) e)  where
  f  >>= k  = \r -> k (f r) r     -- (1)
  return  =  const
-- -}

-- {- AAAAA-3
-- forall a k . return a >>= k === k a
monad1LawArrow :: a -> (a -> (c -> b)) -> (c -> b)
monad1LawArrow a k =
     (return a >>= k)  --. L (Inst "return")
 === (const a >>= k)   --. L (Inst ">>=")
 === (\r -> k (const a r) r)   --. L (Def  "const")
 === (\r -> k a r)     --. L Eta
 === k a               --. QED

-- forall m . m >>= return === m  
monad2LawArrow :: (a -> c) -> (a -> c)
monad2LawArrow f =
     (f >>= return)   --. L (Inst ">>=")
 === (\r -> return (f r) r)    --. L (Inst "return")
 === (\r -> const (f r) r)    --. L (Def  "const")
 === (\r -> f r)    --. L Eta
 === f                --. QED

-- monad3LawMaybe ::  Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Maybe c
-- forall m k k' . m >>= k >>= k'  ===  m >>= \x -> k x >>= k'
monad3LawArrow :: (d -> a) -> (a -> (d -> b)) -> (b -> (d -> c)) -> (d -> c)
monad3LawArrow f k k' =
     (f >>= (\x -> k x >>= k'))         --. L (Inst ">>=")
 === (\r -> (\x -> k x >>= k') (f r) r) --. L Beta
 === (\r -> (k (f r) >>= k') r)         --. L (Inst ">>=")
 === (\r -> (\u -> k' (k (f r) u) u) r) --. L Beta
 === (\r -> k' (k (f r) r) r)           --. R Beta
 === (\r -> k' ((\u -> k (f u) u) r) r) --. R (Inst ">>=")
 === (\r -> k' ((f >>= k) r) r)         --. R (Inst ">>=")
 === ((f >>= k) >>= k')                 --. QED



instance  Monad (Either e)  where
  Left e  >>= _  =  Left e     -- (1)
  Right r >>= k  =  k r -- (2)

  return  =  Right
-- -}


-- {- AAAAA-3
-- forall a k . return a >>= k === k a
monad1LawEither  :: a -> (a -> Either e b) -> Either e b
monad1LawEither  a k =
     (return a >>= k)  --. L (Inst "return")
 === (Right a >>= k)    --. L (Inst ">>=")
 === k a               --. QED

-- forall m . m >>= return === m  
monad2LawEither  ::  Either e b -> Either e b
monad2LawEither  (Right a) =
     (Right a >>= return)   --. L (Inst ">>=")
 === return a               --. L (Inst "return")
 === Right a                --. QED
monad2LawEither  (Left e) =
     (Left e >>= return)  --. L (Inst ">>=")
 === Left e               --. QED

-- forall m k k' . m >>= k >>= k'  ===  m >>= \x -> k x >>= k'
monad3LawEither  ::  Either e a -> (a -> Either e b) -> (b -> Either e c) -> Either e c
monad3LawEither  (Right a) k k' =
     (Right a >>= \x -> k x >>= k')  --. L (Inst ">>=")
 === ((\x -> k x >>= k') a)         --. L Beta
 === (k a >>= k')                   --. R (Inst ">>=")
 === ((Right a >>= k) >>= k')        --. QED
monad3LawEither  (Left e) k k' =
     (Left e >>= \x -> k x >>= k') --. L (Inst ">>=")
 === (Left e)                        --. R (Inst ">>=")
 === (Left e >>= k')               --. R (Inst ">>=")
 === ((Left e >>= k) >>= k')       --. QED     
-- AAAA-4 -}