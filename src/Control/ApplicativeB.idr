module Control.ApplicativeB

import Control.FunctorB

%default total

public export
interface FunctorB t => ApplicativeB t where
  constructor MkApplicativeB
  bpure_ : {0 f : _} -> ((0 a : Type) -> f a) -> t f

  bprod : {0 f,g : _} -> t f -> t g -> t (\x => (f x, g x))

public export
bpure : {0 f : _} -> ApplicativeB t => (forall a . f a) -> t f
bpure fun = bpure_ (\_ => fun)

public export %inline
bempty : Alternative f => ApplicativeB t => t f
bempty = bpure empty

public export
bzipWith :
     {0 f,g,h : _}
  -> ApplicativeB t
  => (forall a . f a -> g a -> h a)
  -> t f
  -> t g
  -> t h
bzipWith fun tf tg = bmap (\(x,y) => fun x y) $ bprod tf tg

public export
bzipWith3 :
     {0 f,g,h,i : _}
  -> ApplicativeB t
  => (forall a . f a -> g a -> h a -> i a)
  -> t f
  -> t g
  -> t h
  -> t i
bzipWith3 fun tf tg th = bmap (\(x,y,z) => fun x y z) $ bprod tf (bprod tg th)

namespace Syntax
  public export %inline
  pure : {0 f : _} -> ApplicativeB t => (forall a . f a) -> t f
  pure = bpure

  public export
  (<*>) :
         ApplicativeB t
     => {0 f,g : Type -> Type}
     -> t (\x => f x -> g x)
     -> t f
     -> t g
  (<*>) x y = bzipWith id x y
