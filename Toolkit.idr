module Toolkit

import Decidable.Equality


%default total

namespace Decidable
  namespace Informative

    public export
    data DecInfo : (errType : Type) -> (prop : Type) -> Type where
       Yes : (prfWhy : prop) -> DecInfo errType prop
       No  : (msgWhyNot : errType) -> (prfWhyNot : prop -> Void) -> DecInfo errType prop

infixr 6 +=


namespace List

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : List a -> a -> List a
  (+=) xs x = x :: xs


  namespace AtIndex
  public export
  data AtIndex : (x   :      type)
              -> (xs  : List type)
              -> (idx : Nat)
                     -> Type
    where
      Here : AtIndex x (x::xs) Z
      There : (later : AtIndex x     rest     idx)
                    -> AtIndex x (y::rest) (S idx)

  namespace Check

    namespace IsAtIndex
      public export
      data Error = EmptyList
                 | SupposedToBeHere
                 | SupposedToBeLater
                 | Later Error

    listIsEmpty : AtIndex x [] 0 -> Void
    listIsEmpty Here impossible
    listIsEmpty (There later) impossible

    supposedToBeHere : (x = y -> Void) -> AtIndex x (y :: xs) 0 -> Void
    supposedToBeHere f Here = f Refl

    supposedToBeLater : AtIndex x [] (S k) -> Void
    supposedToBeLater Here impossible
    supposedToBeLater (There later) impossible

    isNotLater : (AtIndex x xs k -> Void) -> AtIndex x (y :: xs) (S k) -> Void
    isNotLater f (There later) = f later

    export
    isAtIndex : DecEq type
             => (idx : Nat)
             -> (x   : type)
             -> (xs  : List type)
                    -> DecInfo Error (AtIndex x xs idx)
    isAtIndex Z x []
      = No EmptyList (listIsEmpty)

    isAtIndex Z x (y :: xs) with (decEq x y)
      isAtIndex Z x (x :: xs) | (Yes Refl)
        = Yes Here
      isAtIndex Z x (y :: xs) | (No contra)
        = No SupposedToBeHere (supposedToBeHere contra)

    isAtIndex (S k) x []
      = No SupposedToBeLater (supposedToBeLater)

    isAtIndex (S k) x (_ :: xs) with (isAtIndex k x xs)
      isAtIndex (S k) x (_ :: xs) | (Yes prf)
        = Yes (There prf)
      isAtIndex (S k) x (_ :: xs) | (No msg contra)
        = No (Later msg) (isNotLater contra)

  namespace Find

    namespace HasIndex
      public export
      data Error = IsEmpty
                 | Later HasIndex.Error

    isEmpty : DPair Nat (AtIndex x []) -> Void
    isEmpty (MkDPair _ Here) impossible

    isNotElem : {x,y : type}
             -> (DPair Nat (AtIndex x xs) -> Void)
             -> (x = y -> Void)
             -> DPair Nat (AtIndex x (y :: xs))
             -> Void
    isNotElem {x} {y} f g (MkDPair fst snd) with (snd)
      isNotElem {x = x} {y = x} f g (MkDPair 0 snd) | Here
        = g Refl
      isNotElem {x = x} {y = y} f g (MkDPair (S idx) snd) | (There later)
        = f (MkDPair idx later)

    export
    hasIndex : DecEq type
            => (x : type)
            -> (xs : List type)
                  -> DecInfo HasIndex.Error
                             (DPair Nat (AtIndex x xs))
    hasIndex x []
      = No IsEmpty (isEmpty)
    hasIndex x (y :: xs) with (decEq x y)
      hasIndex x (x :: xs) | (Yes Refl)
        = Yes (MkDPair Z Here)

      hasIndex x (y :: xs) | (No contra) with (hasIndex x xs)
        hasIndex x (y :: xs) | (No contra) | (Yes (MkDPair idx prf))
          = Yes (MkDPair (S idx) (There prf))

        hasIndex x (y :: xs) | (No contra) | (No msg f)
          = No (Later msg) (isNotElem f contra)

namespace DList

  ||| A list construct for dependent types.
  |||
  ||| We differ from the standard `All` predicate by making the
  ||| element type's explicit, and making the `head` case bound.
  |||
  ||| @aTy    The type of the value contained within the list element type.
  ||| @elemTy The type of the elements within the list
  ||| @as     The List used to contain the different values within the type.
  public export
  data DList : (type  : Type)
            -> (item  : type -> Type)
            -> (items : List type)
                     -> Type
    where
      ||| Create an empty List
      Nil  : DList type item Nil

      ||| Cons
      |||
      ||| @elem The element to add
      ||| @rest The list for `elem` to be added to.
      (::) : {x : type}
          -> (head : item x)
          -> (tail : DList type item xs)
          -> DList type item (x::xs)

  namespace HoldsAtIndex

    ||| Proof that some element satisfies the predicate
    |||
    ||| @idx   The type of the element's index.
    ||| @type  The type of the list element.
    ||| @p     A predicate
    ||| @xs      The list itself.
    public export
    data HoldsAtIndex : (type   : Type)
                     -> (item   : type -> Type)
                     -> (p      : {i : type} -> (x : item i) -> Type)
                     -> {is     : List type}
                     -> (xs     : DList type item is)
                     -> (idx    : Nat)
                               -> Type
        where
          ||| Proof that the element is at the front of the list.
          Here : {p   : {i : type} -> (x : item i) -> Type}
              -> {i   : type}
              -> {x   : item i}
              -> (prf : p x)
                     -> HoldsAtIndex type item p (x::xs) Z


          ||| Proof that the element is found later in the list.
          There : {p      : {i : type} -> (x : item i) -> Type}
               -> (contra : p x' -> Void)
               -> (later  : HoldsAtIndex type item p      xs     loc)
                         -> HoldsAtIndex type item p (x'::xs) (S loc)

    namespace Find
      namespace HoldsAtIndex
        public export
        data Error type = IsEmpty
                        | Later type (HoldsAtIndex.Error type)

    isEmpty : {p  : {i : type} -> (x : item i) -> Type}
           -> DPair Nat (HoldsAtIndex type item p [])
           -> Void
    isEmpty (MkDPair loc prf) with (prf)
      isEmpty (MkDPair loc prf) | (MkDPair _ (Here _)) impossible
      isEmpty (MkDPair loc prf) | (MkDPair _ (There _)) impossible


    notLater : {p : {i : type} -> (x : item i) -> Type}
            -> (DPair Nat (HoldsAtIndex type item p rest) -> Void)
            -> (p i -> Void)
            -> DPair Nat (HoldsAtIndex type item p (i :: rest))
            -> Void
    notLater f g (MkDPair _ (Here prf))
      = g prf
    notLater f g (MkDPair _ (There contra later))
      = f (MkDPair _ later)

    export
    holdsAtIndex : {p  : {i : type} -> (x : item i) -> Type}
                -> (f  : {i : type} -> (x : item i) -> DecInfo err (p x))
                -> (xs : DList type item is)
                      -> DecInfo (HoldsAtIndex.Error err)
                                 (DPair Nat (HoldsAtIndex type item p xs))
    holdsAtIndex f Nil
      = No IsEmpty (isEmpty)

    holdsAtIndex f (x :: y) with (f x)
      holdsAtIndex f (x :: y) | (Yes prf)
        = Yes (MkDPair 0 (Here prf))

      holdsAtIndex f (x :: y) | (No msg contra) with (holdsAtIndex f y)
        holdsAtIndex f (x :: y) | (No msg contra) | (Yes (MkDPair loc prf))
          = Yes (MkDPair (S loc) (There contra prf))

        holdsAtIndex f (x :: y) | (No msg contra) | (No msgR contraR)
          = No (Later msg msgR)
               (notLater contraR contra)

-- [ EOF ]
