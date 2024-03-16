module Derive.RecordB

import Language.Reflection.Util
import Derive.BarbieInfo

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

blensTpe : (k : TTImp) -> TTImp -> TTImp
blensTpe k arg =
  `(
       (0 f : ~(k) -> Type)
    -> (v : ~(k))
    -> Lens' (~(arg) f) (f v)
  )

export
blensClaim : Visibility -> (fun : Name) -> (p : BarbieInfo) -> Decl
blensClaim vis fun p =
  simpleClaim vis fun $ piAll (blensTpe p.kind p.applied) p.implicits

||| Top-level declaration implementing the `Eq` interface for
||| the given data type.
export
recordImplClaim : Visibility -> (impl : Name) -> (p : BarbieInfo) -> Decl
recordImplClaim vis impl p =
  let tpe := piAll `(RecordB ~(p.kind) ~(p.applied)) p.implicits
   in implClaimVis vis impl tpe

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
recordImplDef : (fld, impl : Name) -> Decl
recordImplDef fld impl = def impl [patClause (var impl) `(MkRecordB ~(var fld))]

lclause : (String -> String) -> Name -> BoundArg 0 RegularNamed -> Clause
lclause f fun (BA x _ _) =
  let fld := argName x
      nme := UN $ Basic (f $ nameStr fld)
      u   := update [ISetField [nameStr fld] `(x)] `(y)
   in patClause `(~(var fun) _ ~(var nme)) `(lens ~(var fld) $ \x,y => ~(u))

export
lensDef : (String -> String) -> Name -> Con n vs -> Decl
lensDef f fun c =
  def fun (lclause f fun <$> (boundArgs regularNamed c.args [] <>> []))

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `RecordB`
||| for a given data type.
export
RecordBVis :
     (String -> String)
  -> Visibility
  -> List Name
  -> ParamTypeInfo
  -> Res (List TopLevel)
RecordBVis f vis nms p = case barbieArgs p.info.args of
  Just prf => case p.info.cons of
    [c] =>
      let nlens := funName p "bfield"
          impl  := implName p "RecordB"
          bti   := BI p prf
       in Right
            [ TL (blensClaim vis nlens bti) (lensDef f nlens c)
            , TL (recordImplClaim vis impl bti)
                 (recordImplDef nlens impl)
            ]
    _ => failRecord "RecordB"
  Nothing => Left $ "Not a barbie type"

||| Alias for `RecordBVis Public`
export %inline
RecordB :
     (String -> String)
  -> List Name
  -> ParamTypeInfo
  -> Res (List TopLevel)
RecordB f = RecordBVis f Public
