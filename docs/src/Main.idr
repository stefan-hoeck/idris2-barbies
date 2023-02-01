module Main

import Control.Barbie
import Data.List1
import Data.String
import Derive.Barbie
import Derive.Prelude

%default total
%language ElabReflection

0 Up : Type -> Type
Up a = a -> a

record User (f : Type -> Type) where
  constructor U
  id    : f Nat
  name  : f String
  email : f String

%runElab derive "User" [Show,Eq,Barbie]

user : User I
user = U 12 "Gundi" "gundi@gmail.com"

userM : User Maybe
userM = bmap Just user

userEmpty : User Maybe
userEmpty = bempty

user2 : User I
user2 = [| apply (U {f = \x => x -> x} (*2) reverse id) user |]

--------------------------------------------------------------------------------
--          Validation
--------------------------------------------------------------------------------

0 Val : Type -> Type
Val a = a -> Either String a

emailChar : Char -> Bool
emailChar '.' = True
emailChar '-' = True
emailChar '_' = True
emailChar c   = isAlphaNum c

valName : Val String
valName s =
  if all (not . isControl) (unpack s)
     then Right s
     else Left "Invalid name: \{show s}"

invalidEmail : String -> Either String a
invalidEmail s = Left "Invalid email address: \{show s}"

valEmail : Val String
valEmail s = case forget $ split ('@' ==) (unpack s) of
  [x,y] => 
    if all emailChar x && all emailChar y then Right s else invalidEmail s
  _     => invalidEmail s

userVal : User Val
userVal = U Right valName valEmail

validate : User I -> Either String (User I)
validate u = bsequence' [| apply userVal u |]

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
