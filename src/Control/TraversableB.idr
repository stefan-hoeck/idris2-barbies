module Control.TraversableB

import Control.Applicative.Const
import Control.FunctorB

%default total

public export
interface FunctorB k t => TraversableB k t | t where
  constructor MkTraversableB
  btraverse_ :
       {0 f,g : _}
    -> {auto app : Applicative e}
    -> ((0 a : k) -> f a -> e (g a))
    -> t f -> e (t g)

public export
btraverse :
     {0 f,g : _}
  -> {auto app : Applicative e}
  -> {auto trv : TraversableB k t}
  -> ({0 a : k} -> f a -> e (g a))
  -> t f -> e (t g)
btraverse fun = btraverse_ (\_ => fun)

public export
bsequence :
     {0 f : _}
  -> {auto app : Applicative e}
  -> {auto trv : TraversableB k t}
  -> t (e . f)
  -> e (t f)
bsequence = btraverse_ (\_,x => x)

public export
bsequence' : Applicative e => TraversableB Type t => t e -> e (t I)
bsequence' = btraverse_ (\_,x => x)

public export
bfoldMap :
     {0 f : _}
  -> {auto app : Monoid m}
  -> {auto trv : TraversableB k t}
  -> ({0 a : k} -> f a -> m)
  -> t f
  -> m
bfoldMap g b = runConst $ btraverse {g = f} (MkConst . g) b
