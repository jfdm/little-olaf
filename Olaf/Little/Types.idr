module Olaf.Little.Types

import Decidable.Equality

import Toolkit

%default total


public export
data Ty = TyNat
        | TyBool
        | TyFunc Ty Ty
        | TyUnit


Uninhabited (TyNat = TyBool) where
  uninhabited Refl impossible

Uninhabited (TyNat = TyFunc x y) where
  uninhabited Refl impossible

Uninhabited (TyNat = TyUnit) where
  uninhabited Refl impossible

Uninhabited (TyBool = TyFunc x y) where
  uninhabited Refl impossible

Uninhabited (TyBool = TyUnit) where
  uninhabited Refl impossible

Uninhabited (TyFunc x y = TyUnit) where
  uninhabited Refl impossible

decEq : (x,y : Ty) -> Dec (x === y)
decEq TyNat TyNat
  = Yes Refl

decEq TyNat TyBool
  = No absurd

decEq TyNat (TyFunc x y)
  = No absurd

decEq TyNat TyUnit
  = No absurd

decEq TyBool TyNat
  = No (negEqSym absurd)

decEq TyBool TyBool
  = Yes Refl

decEq TyBool (TyFunc x y)
  = No absurd

decEq TyBool TyUnit
  = No absurd

decEq (TyFunc x z) TyNat
  = No (negEqSym absurd)

decEq (TyFunc x z) TyBool
  = No (negEqSym absurd)

decEq (TyFunc aA rA) (TyFunc aB rB) with (decEq aA aB)
  decEq (TyFunc aA rA) (TyFunc aA rB) | (Yes Refl) with (decEq rA rB)
    decEq (TyFunc aA rA) (TyFunc aA rA) | (Yes Refl) | (Yes Refl)
      = Yes Refl

    decEq (TyFunc aA rA) (TyFunc aA rB) | (Yes Refl) | (No contra)
      = No (\Refl => contra Refl)

  decEq (TyFunc aA rA) (TyFunc aB rB) | (No contra)
    = No (\Refl => contra Refl)

decEq (TyFunc x z) TyUnit
  = No absurd

decEq TyUnit TyNat
  = No (negEqSym absurd)

decEq TyUnit TyBool
  = No (negEqSym absurd)

decEq TyUnit (TyFunc x y)
  = No (negEqSym absurd)

decEq TyUnit TyUnit
  = Yes Refl

export
DecEq Ty where
  decEq = Types.decEq


-- [ EOF ]
