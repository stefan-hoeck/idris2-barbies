module Derive.BarbieInfo

import public Language.Reflection.Derive

%default total

||| Proof that a `TTImp` corresponds to `k -> Type` for some `k`.
public export
data ToType : TTImp -> Type where
  IsToType : {k : TTImp} -> ToType  (IPi f1 MW ExplicitArg n2 k (IType f3))

public export
toType : (t : TTImp) -> Maybe (ToType t)
toType (IPi _ MW ExplicitArg _ k (IType _)) = Just IsToType
toType _ = Nothing

||| Proof that the last in a list of arguments is of type `Type -> Type`
public export
data BarbieArgs : Vect n Arg -> Type where
  BAHere  :
       {0 t : TTImp}
    -> {n : Name}
    -> {auto prf : ToType t}
    -> BarbieArgs [MkArg c ExplicitArg (Just n) t]
  BAThere : BarbieArgs vs -> BarbieArgs (v :: vs)

public export
barbieArgs : (vs : Vect n Arg) -> Maybe (BarbieArgs vs)
barbieArgs [MkArg c ExplicitArg (Just n) t] =
  let Just _ := toType t | Nothing => Nothing
   in Just BAHere
barbieArgs (x :: xs) = BAThere <$> barbieArgs xs
barbieArgs [] = Nothing

||| Name of the last argument of a `Barbie` type constructor.
public export
barbieArg : BarbieArgs vs -> Name
barbieArg (BAHere {n}) = n
barbieArg (BAThere x)  = barbieArg x

||| Name of the last argument of a `Barbie` type constructor.
public export
barbieKind : BarbieArgs vs -> TTImp
barbieKind (BAHere @{IsToType {k}}) = k
barbieKind (BAThere x)  = barbieKind x

||| Proof that a parameterized type is actually a `Barbie`.
public export
record BarbieInfo where
  constructor BI
  info : ParamTypeInfo
  prf  : BarbieArgs info.info.args

public export
Named BarbieInfo where
  b.getName = b.info.getName

public export
hasFArg : (farg : Name) -> TTImp -> Bool
hasFArg farg (IApp _ (IVar _ n) _) = farg == n
hasFArg _    _                     = False

||| Names of all type arguments of a barbie, except the last one
public export
(.explicitArgs) : BarbieInfo -> List Name
(.explicitArgs) p = go Lin p.info.info.args p.prf p.info.info.argNames
  where
    go :
         SnocList Name
      -> (vs : Vect k Arg)
      -> BarbieArgs vs
      -> Vect k Name
      -> List Name
    go snm [_] BAHere [_] = snm <>> []
    go snm (MkArg _ ExplicitArg _ _:: vs) (BAThere x) (n :: ns) =
      go (snm :< n) vs x ns
    go snm (v :: vs) (BAThere x) (n :: ns) = go snm vs x ns

||| Returns a type constructor
||| applied to the names of its explicit arguments except the last one
public export
(.applied) : BarbieInfo -> TTImp
(.applied) p = appNames p.getName p.explicitArgs

||| Returns a list of implicit arguments corresponding
||| to the data type's explicit arguments (except the last one)
public export %inline
(.implicits) : BarbieInfo -> List Arg
(.implicits) p = implicits p.explicitArgs

||| Returns the kind of the first argument of the last parameter of
||| a barbie.
public export %inline
(.kind) : BarbieInfo -> TTImp
(.kind) p = barbieKind p.prf
