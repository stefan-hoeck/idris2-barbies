module Control.ApplicativeB

import Control.FunctorB

%default total

public export
interface FunctorB k t => ApplicativeB k t | t where
  constructor MkApplicativeB
  bpure_ : {0 f : _} -> ((0 a : k) -> f a) -> t f

  bprod : {0 f,g : _} -> t f -> t g -> t (\x => (f x, g x))

public export
bpure : {0 f : _} -> ApplicativeB k t => ({0 a : k} -> f a) -> t f
bpure fun = bpure_ (\_ => fun)

public export %inline
bempty : {0 g : k -> Type} -> Alternative f => ApplicativeB k t => t (f . g)
bempty = bpure empty

public export
bzipWith :
     {0 f,g,h : _}
  -> {auto _ : ApplicativeB k t}
  -> ({0 a : k} -> f a -> g a -> h a)
  -> t f
  -> t g
  -> t h
bzipWith fun tf tg = bmap (\(x,y) => fun x y) $ bprod tf tg

public export
bzipWith3 :
     {0 f,g,h,i : _}
  -> {auto _ : ApplicativeB k t}
  -> ({0 a : k} -> f a -> g a -> h a -> i a)
  -> t f
  -> t g
  -> t h
  -> t i
bzipWith3 fun tf tg th = bmap (\(x,y,z) => fun x y z) $ bprod tf (bprod tg th)

namespace Syntax
  public export %inline
  pure : {0 f : _} -> ApplicativeB k t => ({0 a : k} -> f a) -> t f
  pure = bpure

  public export
  (<*>) :
        {auto _ : ApplicativeB k t}
     -> {0 f,g : k -> Type}
     -> t (\x => f x -> g x)
     -> t f
     -> t g
  (<*>) x y = bzipWith id x y
