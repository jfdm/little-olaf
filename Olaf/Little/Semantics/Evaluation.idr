module Olaf.Little.Semantics.Evaluation

import Decidable.Equality

import Data.Fuel

import Toolkit

import DeBruijn.Renaming
import DeBruijn.Substitution

import Olaf.Little.Types
import Olaf.Little.Terms
import Olaf.Little.Values
import Olaf.Little.Semantics.Reductions
import Olaf.Little.Semantics.Progress

%default total

data Finished : (term : Term ctxt type)
                     -> Type
  where
    Normalised : {term : Term ctxt type}
                      -> Value term
                      -> Finished term
    OOF : Finished term

data Evaluate : (term : Term Nil type) -> Type where
  RunEval : {this, that : Term Nil type}
         -> (steps      : Inf (Reduces this that))
         -> (result     : Finished that)
                       -> Evaluate this


evaluate : {type : Ty}
        -> (fuel : Fuel)
        -> (term : Term Nil type)
                -> Evaluate term
evaluate Dry term
  = RunEval Refl OOF
evaluate (More fuel) term with (progress term)
  evaluate (More fuel) term | (Done value)
    = RunEval Refl (Normalised value)
  evaluate (More fuel) term | (Step step {that}) with (evaluate fuel that)
    evaluate (More fuel) term | (Step step {that = that}) | (RunEval steps result)
      = RunEval (Trans step steps) result

public export
data Result : (term : Term Nil type) -> Type where
  R : (that : Term Nil type)
   -> (0 val   : Value that)
   -> (0 steps : Reduces this that)
              -> Result this

export covering
eval : {type : Ty}
   -> (this : Term Nil type)
           -> Maybe (Result this)
eval this with (evaluate forever this)
  eval this | (RunEval steps (Normalised {term} x))
    = Just (R term x steps)
  eval this | (RunEval steps OOF) = Nothing

-- [ EOF ]
