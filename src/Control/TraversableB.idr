module Control.TraversableB

import Control.FunctorB

%default total

public export
interface FunctorB t => TraversableB t where
  constructor MkTraversableB
  btraverse_ :
       {0 f,g : _}
    -> Applicative e
    => ((0 a : Type) -> f a -> e (g a))
    -> t f -> e (t g)

public export
btraverse :
       {0 f,g : _}
    -> Applicative e
    => TraversableB t
    => (forall a . f a -> e (g a))
    -> t f -> e (t g)
btraverse fun = btraverse_ (\_ => fun)

public export
bsequence : {0 f : _} -> Applicative e => TraversableB t => t (e . f) -> e (t f)
bsequence = btraverse_ (\_,x => x)

public export
bsequence' : Applicative e => TraversableB t => t e -> e (t I)
bsequence' = btraverse_ (\_,x => x)
