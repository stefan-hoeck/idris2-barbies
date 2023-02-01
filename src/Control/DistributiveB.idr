module Control.DistributiveB

import Control.FunctorB

%default total

public export
interface FunctorB k t => DistributiveB k t | t where
  constructor MkDistributiveB
  bdistribute : {0 g : k -> Type} -> Functor f => f (t g) -> t (f . g)
