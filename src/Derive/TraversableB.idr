module Derive.TraversableB

import Language.Reflection.Util
import Derive.BarbieInfo

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

btravTpe : (k : TTImp) -> TTImp -> TTImp
btravTpe k arg =
  `(
       {0 e : Type -> Type}
    -> {0 f,g : ~(k) -> Type}
    -> {auto _ : Applicative e}
    -> ((0 a : ~(k)) -> f a -> e (g a))
    -> ~(arg) f
    -> e (~(arg) g)
  )

export
btravClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
btravClaim vis fun p =
  simpleClaim vis fun $ piAll (btravTpe p.kind p.applied) p.implicits

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
travImplClaim : Visibility -> (impl : Name) -> (p : BarbieInfo) -> Decl
travImplClaim vis impl p =
  let tpe := piAll `(TraversableB ~(p.kind) ~(p.applied)) p.implicits
   in implClaimVis vis impl tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
travImplDef : (fun, impl : Name) -> Decl
travImplDef fun impl =
  def impl [patClause (var impl) `(MkTraversableB ~(var fun))]

rhs : Name -> SnocList TTImp -> TTImp
rhs nm [<]       = `(Prelude.pure ~(var nm))
rhs nm (sx :< x) = `(Prelude.(<*>) ~(rhs nm sx) ~(x))

parameters (farg : Name)

  arg : BoundArg 1 Regular -> TTImp
  arg (BA g [x] _) =
    if hasFArg farg g.type
       then `(fun _ ~(var x))
       else `(pure ~(var x))

  export
  travClauses : (fun : Name) -> TypeInfo -> List Clause
  travClauses fun ti = map clause ti.cons

   where
     clause : Con ti.arty ti.args -> Clause
     clause c =
       accumArgs regular (\x => `(~(var fun) fun ~(x))) (rhs c.name) arg c

  export
  travDef : Name -> TypeInfo -> Decl
  travDef fun ti = def fun (travClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `TraversableB`
||| for a given data type.
export
TraversableBVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
TraversableBVis vis nms p = case barbieArgs p.info.args of
  Just prf =>
    let fun  := funName p "btrav"
        impl := implName p "TraversableB"
        farg := barbieArg prf
        bti  := BI p prf
     in Right
          [ TL (btravClaim vis fun bti) (travDef (barbieArg prf) fun p.info)
          , TL (travImplClaim vis impl bti) (travImplDef fun impl)
          ]
  Nothing => Left $ "Not a barbie type"

||| Alias for `TraversableBVis Public`
export %inline
TraversableB : List Name -> ParamTypeInfo -> Res (List TopLevel)
TraversableB = TraversableBVis Public
