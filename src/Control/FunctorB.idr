module Control.FunctorB

%default total

public export
0 I : Type -> Type
I a = a

public export
0 K : Type -> Type -> Type
K e a = e

public export
interface FunctorB (0 k : Type) (0 t : (k -> Type) -> Type) | t where
  constructor MkFunctorB
  bmap_ : {0 f,g : k -> Type} -> ((0 a : k) -> f a -> g a) -> t f -> t g

public export
bmap : FunctorB k t => ({0 a : k} -> f a -> g a) -> t f -> t g
bmap f = bmap_ (\_ => f)
