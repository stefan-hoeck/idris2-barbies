module Control.FunctorB

%default total

public export
0 I : Type -> Type
I a = a

public export
0 K : Type -> Type -> Type 
K e a = e

public export
interface FunctorB (0 t : (Type -> Type) -> Type) where
  constructor MkFunctorB
  bmap_ : {0 f,g : _} -> ((0 a : Type) -> f a -> g a) -> t f -> t g

public export
bmap : FunctorB t => (forall a . f a -> g a) -> t f -> t g
bmap f = bmap_ (\_ => f)
