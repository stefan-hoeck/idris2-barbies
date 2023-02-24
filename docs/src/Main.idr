module Main

import Data.Maybe
import Control.Barbie
import Data.List1
import Data.String
import Derive.Barbie
import Derive.Prelude

%default total
%language ElabReflection

public export
data Field = Id | Name | Email

public export
0 Tpe : Field -> Type
Tpe Id    = Nat
Tpe Name  = String
Tpe Email = String

public export
0 Up : Field -> Type
Up x = Tpe x -> Tpe x

record User (f : Field -> Type) where
  constructor U
  id    : f Id
  name  : f Name
  email : f Email

%runElab derive "User" [Show,Eq,Barbie]

user : User Tpe
user = U 12 "Stefan" "gundi@gmail.com"

userM : User (Maybe . Tpe)
userM = bmap Just user

userEmpty : User (Maybe . Tpe)
userEmpty = bempty

user2 : User Tpe
user2 = [| apply (U {f = Up} (*2) reverse id) user |]

--------------------------------------------------------------------------------
--          Validation
--------------------------------------------------------------------------------

0 Val : Field -> Type
Val a = Tpe a -> Either String (Tpe a)

emailChar : Char -> Bool
emailChar '.' = True
emailChar '-' = True
emailChar '_' = True
emailChar c   = isAlphaNum c

valName : Val Name
valName s =
  if all (not . isControl) (unpack s)
     then Right s
     else Left "Invalid name: \{show s}"

invalidEmail : String -> Either String a
invalidEmail s = Left "Invalid email address: \{show s}"

valEmail : Val Email
valEmail s = case forget $ split ('@' ==) (unpack s) of
  [x,y] =>
    if all emailChar x && all emailChar y then Right s else invalidEmail s
  _     => invalidEmail s

userVal : User Val
userVal = U Right valName valEmail

validate : User Tpe -> Either String (User Tpe)
validate u = bsequence [| apply userVal u |]

--------------------------------------------------------------------------------
--          Tables
--------------------------------------------------------------------------------

0 UserColumns : Nat -> Type
UserColumns n = User (Vect n . Tpe)

0 UserRows : Nat -> Type
UserRows n = Vect n (User Tpe)

rows : {n : _} -> UserColumns n -> UserRows n
rows = bsequence

columns : UserRows n -> UserColumns n
columns = bdistribute

oopsie : User (const Void) -> a
oopsie (U _ _ _) impossible

--------------------------------------------------------------------------------
--          Constraint
--------------------------------------------------------------------------------

showFields : (prf : User (Show . f)) => User f -> User (const String)
showFields x = bzipWith (\_ => show) prf x

--------------------------------------------------------------------------------
--          Main
--------------------------------------------------------------------------------

main : IO ()
main = do
  printLn user
  printLn userM
  printLn userEmpty
  printLn user2
  printLn (validate user)
  printLn (validate $ U 0 "Stefan Höck" "foo @123.bar")
