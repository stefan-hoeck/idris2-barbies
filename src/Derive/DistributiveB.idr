module Derive.DistributiveB

import public Language.Reflection.Derive
import Derive.BarbieInfo

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

bdistTpe : (k : TTImp) -> TTImp -> TTImp
bdistTpe k arg =
  `(
       {0 f : Type -> Type}
    -> {0 g : ~(k) -> Type}
    -> Functor f
    => f (~(arg) g)
    -> ~(arg) (f . g)
  )

export
bdistClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
bdistClaim vis fun p =
  simpleClaim vis fun $ piAll (bdistTpe p.kind p.applied) p.implicits

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
distImplClaim : Visibility -> (impl : Name) -> (p : BarbieInfo) -> Decl
distImplClaim vis impl p =
  let tpe := piAll `(DistributiveB ~(p.kind) ~(p.applied)) p.implicits
   in implClaimVis vis impl tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
distImplDef : (fun, impl : Name) -> Decl
distImplDef fun impl = def impl [var impl .= var "MkDistributiveB" .$ var fun]

rhs : Name -> SnocList TTImp -> TTImp
rhs nm [<]       = var nm
rhs nm (sx :< x) = rhs nm sx .$ x

arg : BoundArg 0 RegularNamed -> TTImp
arg (BA g [] _) = `(~(var $ argName g) <$> x_)

export
distClause : (fun : Name) -> Con n vs -> Clause
distClause fun c = var fun .$ `(x_) .= injArgs regularNamed arg c

export
distDef : Name -> Con n vs -> Decl
distDef fun c = def fun [distClause fun c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `DistributiveB`
||| for a given data type.
export
DistributiveBVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
DistributiveBVis vis nms p = case barbieArgs p.info.args of
  Just prf => case p.info.cons of
    [c] =>
      let ndist := funName p "bdist"
          impl  := implName p "DistributiveB"
          bti   := BI p prf
       in Right [ TL (bdistClaim vis ndist bti) (distDef ndist c)
                , TL (distImplClaim vis impl bti) (distImplDef ndist impl)
                ]
    _ => failRecord "DistributiveB"
  Nothing => Left $ "Not a barbie type"

||| Alias for `DistributiveBVis Public`
export %inline
DistributiveB : List Name -> ParamTypeInfo -> Res (List TopLevel)
DistributiveB = DistributiveBVis Public
