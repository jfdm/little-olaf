module Olaf.Little.Values

import Decidable.Equality

import Toolkit

import Olaf.Little.Types
import Olaf.Little.Terms

%default total

public export
data Value : (term : Term ctxt type)
                  -> Type
  where
    Fun : Value (Fun body)

    Zero : Value Zero
    Plus : Value rest -> Value (Plus rest)

    True : Value True
    False : Value False

-- [ EOF ]
