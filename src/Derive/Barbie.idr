module Derive.Barbie

import public Derive.ApplicativeB
import public Derive.BarbieInfo
import public Derive.FunctorB
import public Derive.TraversableB

||| Generate declarations for all barbie interfaces
||| (`FunctorB`, `ApplicativeB`, and `TraversableB`)
||| for a given data type.
export
BarbieVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
BarbieVis vis nms p =
  sequenceJoin [
      FunctorBVis vis nms p
    , ApplicativeBVis vis nms p
    , TraversableBVis vis nms p
    ]

||| Alias for `BarbieVis Public`
export %inline
Barbie : List Name -> ParamTypeInfo -> Res (List TopLevel)
Barbie = BarbieVis Public