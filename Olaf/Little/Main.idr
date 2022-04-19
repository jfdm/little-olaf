module Olaf.Little.Main

import Data.List

import Toolkit

import DeBruijn.Renaming
import DeBruijn.Substitution

import Olaf.Little.Types
import Olaf.Little.Terms
import Olaf.Little.Values
import Olaf.Little.Semantics.Evaluation

Show (Term ctxt type) where
  show (Var (V pos prf)) = "\\{\{show pos}\\}"
  show (Fun body) = "(fun \{show body})"
  show (App func arg) = "(app \{show func} \{show arg})"
  show Zero = "Z"
  show (Plus x) = "(S\{show x})"
  show (Add l r) = "(+ \{show l} \{show r})"
  show True = "t"
  show False = "f"
  show (And l r) = "(& \{show l} \{show r})"

terms : Term Nil TyBool
terms = foldr And False (replicate 1000 True)

let_ : {a : Ty}
    -> Term ctxt a
    -> Term (ctxt += a) b
    -> Term ctxt b
let_ x y = (Fun y) `App` x

export
main : IO ()
main = do putStrLn "## Before"
          printLn (let_ terms (Var (V 0 Here)))
          case eval (let_ terms (Var (V 0 Here))) of
            Nothing => putStrLn "Out of fuel"
            Just (R t _ _)  => do putStrLn "## After"
                                  printLn t
