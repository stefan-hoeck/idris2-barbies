module Derive.ApplicativeB

import public Language.Reflection.Derive
import Derive.BarbieInfo

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

bpureTpe : TTImp -> TTImp
bpureTpe arg =
  `(
       {0 f : Type -> Type}
    -> ((0 a : Type) -> f a)
    -> ~(arg) f
  )

bprodTpe : TTImp -> TTImp
bprodTpe arg =
  `(
       {0 f,g : Type -> Type}
    -> ~(arg) f
    -> ~(arg) g
    -> ~(arg) (\x => Pair (f x) (g x))
  )

export
bpureClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
bpureClaim vis fun p =
  simpleClaim vis fun $ piAll (bpureTpe p.applied) p.implicits

export
bprodClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
bprodClaim vis fun p =
  simpleClaim vis fun $ piAll (bprodTpe p.applied) p.implicits

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
applicativeImplClaim : Visibility -> (impl : Name) -> (p : BarbieInfo) -> Decl
applicativeImplClaim vis impl p =
  let arg := p.applied
      tpe := piAll `(ApplicativeB ~(arg)) p.implicits
   in implClaimVis vis impl tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
applicativeImplDef : (bpure, bprod, impl : Name) -> Decl
applicativeImplDef bpure bprod impl =
  def impl [var impl .= var "MkApplicativeB" .$ var bpure .$ var bprod]

prodArg : BoundArg 2 Regular -> TTImp
prodArg (BA g [x,y] _) = `(MkPair ~(varStr x) ~(varStr y))

export
prodClause : (fun : Name) -> Con n vs -> Clause
prodClause f =
  mapArgs2 regular (\x,y => var f .$ x .$ y) prodArg

export
prodDef : Name -> Con n vs -> Decl
prodDef fun c = def fun [prodClause fun c]

export
pureDef : Name -> Con n vs -> Decl
pureDef f c =
  let rhs := injArgs explicit (const `(fun _)) c
   in def f [var f .$ `(fun) .= rhs ]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `ApplicativeB`
||| for a given data type.
export
ApplicativeBVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
ApplicativeBVis vis nms p = case barbieArgs p.info.args of
  Just prf => case p.info.cons of
    [c] =>
      let npure := funName p "bpure"
          nprod := funName p "bprod"
          impl  := implName p "ApplicativeB"
          bti   := BI p prf
       in Right [ TL (bpureClaim vis npure bti) (pureDef npure c)
                , TL (bprodClaim vis nprod bti) (prodDef nprod c)
                , TL (applicativeImplClaim vis impl bti)
                     (applicativeImplDef npure nprod impl)
                ]
    _ => failRecord "ApplicativeB"
  Nothing => Left $ "Not a barbie type"

||| Alias for `ApplicativeBVis Public`
export %inline
ApplicativeB : List Name -> ParamTypeInfo -> Res (List TopLevel)
ApplicativeB = ApplicativeBVis Public
