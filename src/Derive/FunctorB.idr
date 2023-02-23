module Derive.FunctorB

import Language.Reflection.Util
import Derive.BarbieInfo

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

bmapTpe : (k : TTImp) -> TTImp -> TTImp
bmapTpe k arg =
  `(
       {0 f,g : ~(k) -> Type}
    -> ((0 a : ~(k)) -> f a -> g a)
    -> ~(arg) f
    -> ~(arg) g
  )

export
bmapClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
bmapClaim vis fun p =
  simpleClaim vis fun $ piAll (bmapTpe p.kind p.applied) p.implicits

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
functorImplClaim : Visibility -> (impl : Name) -> (p : BarbieInfo) -> Decl
functorImplClaim vis impl p =
  let tpe := piAll `(FunctorB ~(p.kind) ~(p.applied)) p.implicits
   in implClaimVis vis impl tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
functorImplDef : (fun, impl : Name) -> Decl
functorImplDef fun impl =
  def impl [patClause (var impl) (var "MkFunctorB" `app` var fun)]

parameters (farg : Name)

  arg : BoundArg 1 Regular -> TTImp
  arg (BA g [x] _) =
    if hasFArg farg g.type then `(fun _ ~(varStr x)) else varStr x

  export
  functorClauses : (fun : Name) -> TypeInfo -> List Clause
  functorClauses fun ti = map clause ti.cons
   where
     clause : Con ti.arty ti.args -> Clause
     clause = mapArgs regular (\x => `(~(var fun) fun ~(x))) arg

  export
  functorDef : Name -> TypeInfo -> Decl
  functorDef fun ti = def fun (functorClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `FunctorB`
||| for a given data type.
export
FunctorBVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
FunctorBVis vis nms p = case barbieArgs p.info.args of
  Just prf =>
    let fun  := funName p "bmap"
        impl := implName p "FunctorB"
        farg := barbieArg prf
        bti  := BI p prf
     in Right [ TL (bmapClaim vis fun bti) (functorDef (barbieArg prf) fun p.info)
              , TL (functorImplClaim vis impl bti) (functorImplDef fun impl)
              ]
  Nothing => Left $ "Not a barbie type"

||| Alias for `FunctorBVis Public`
export %inline
FunctorB : List Name -> ParamTypeInfo -> Res (List TopLevel)
FunctorB = FunctorBVis Public
