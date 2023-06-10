{-# OPTIONS --safe #-}

-- TODO: This could be generalized to handle monotone functions on
-- both preorders and posets.

module Cubical.Categories.Instances.Posets.Monotone where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function hiding (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Poset

open BinaryRelation


private
  variable
    ℓ ℓ' : Level



module _ {ℓ ℓ' : Level} where

  -- Because of a bug with Cubical Agda's reflection, we need to declare
  -- a separate version of MonFun where the arguments to the isMon
  -- constructor are explicit.
  -- See https://github.com/agda/cubical/issues/995.
  module _ {X Y : Poset ℓ ℓ'} where

    module X = PosetStr (X .snd)
    module Y = PosetStr (Y .snd)
    _≤X_ = X._≤_
    _≤Y_ = Y._≤_

    monotone' : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max ℓ ℓ')
    monotone' f = (x y : ⟨ X ⟩) -> x ≤X y → f x ≤Y f y

    monotone : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max ℓ ℓ')
    monotone f = {x y : ⟨ X ⟩} -> x ≤X y → f x ≤Y f y

  -- Monotone functions from X to Y
  -- This definition works with Cubical Agda's reflection.
  record MonFun' (X Y : Poset ℓ ℓ') : Type ((ℓ-max ℓ ℓ')) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone' {X} {Y} f

  -- This is the definition we want, where the first two arguments to isMon
  -- are implicit.
  record MonFun (X Y : Poset ℓ ℓ') : Type ((ℓ-max ℓ ℓ')) where
    field
      f : (X .fst) → (Y .fst)
      isMon : monotone {X} {Y} f

  open MonFun
  open IsPoset
  open PosetStr

  isoMonFunMonFun' : {X Y : Poset ℓ ℓ'} -> Iso (MonFun X Y) (MonFun' X Y)
  isoMonFunMonFun' = iso
    (λ g → record { f = MonFun.f g ; isMon = λ x y x≤y → isMon g x≤y })
    (λ g → record { f = MonFun'.f g ;
                    isMon = λ {x} {y} x≤y -> MonFun'.isMon g x y x≤y }
    )
    (λ g → refl)
    (λ g → refl)


  isPropIsMon : {X Y : Poset ℓ ℓ'} -> (f : MonFun X Y) ->
    isProp (monotone {X} {Y} (MonFun.f f))
  isPropIsMon {X} {Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> is-prop-valued (isPoset (str Y))
        (MonFun.f f x) (MonFun.f f y)))

  isPropIsMon' : {X Y : Poset ℓ ℓ'} -> (f : ⟨ X ⟩ -> ⟨ Y ⟩) ->
    isProp (monotone' {X} {Y} f)
  isPropIsMon' {X} {Y} f =
    isPropΠ3 (λ x y x≤y -> is-prop-valued (isPoset (str Y))
      (f x) (f y))

  -- Equivalence between MonFun' record and a sigma type
  unquoteDecl MonFun'IsoΣ = declareRecordIsoΣ MonFun'IsoΣ (quote (MonFun'))

  Sigma : (X Y : Poset ℓ ℓ') -> Type (ℓ-max ℓ ℓ')
  Sigma X Y =
     (Σ (X .fst → Y .fst)
     (λ z → (x y : ⟨ X ⟩) → _≤X_ {X} {Y} x y → _≤Y_ {X} {Y} (z x) (z y)))

  _ : {X Y : Poset ℓ ℓ'} -> Iso (MonFun' X Y) (Sigma X Y)
  _ = MonFun'IsoΣ

  MonFun≡Sigma : {X Y : Poset ℓ ℓ'} -> MonFun' X Y ≡ Sigma X Y
  MonFun≡Sigma = isoToPath MonFun'IsoΣ

  Sigma≡ : {X Y : Poset ℓ ℓ'} -> {s1 s2 : Sigma X Y} ->
    s1 .fst ≡ s2 .fst -> s1 ≡ s2
  Sigma≡ {X} {Y} = Σ≡Prop (λ f → isPropΠ3
    (λ x y x≤y -> is-prop-valued (isPoset (str Y)) (f x) (f y)))

  -- Equality of monotone functions is equivalent to equality of the
  -- underlying functions.
  eqMon' : {X Y : Poset ℓ ℓ'} -> (f g : MonFun' X Y) ->
    MonFun'.f f ≡ MonFun'.f g -> f ≡ g
  eqMon' {X} {Y} f g p = isoFunInjective MonFun'IsoΣ f g
    (Σ≡Prop (λ h → isPropΠ3 (λ y z q →
      is-prop-valued (isPoset (str Y)) (h y) (h z))) p)

  eqMon : {X Y : Poset ℓ ℓ'} -> (f g : MonFun X Y) ->
    MonFun.f f ≡ MonFun.f g -> f ≡ g
  eqMon {X} {Y} f g p = isoFunInjective isoMonFunMonFun' f g (eqMon' _ _ p)

  -- isSet for Sigma
  isSetSigma : {X Y : Poset ℓ ℓ'} -> isSet (Sigma X Y)
  isSetSigma {X} {Y} = isSetΣSndProp
    (isSet→ (is-set (isPoset (str Y))))
    λ f -> isPropIsMon' {X} {Y} f

  -- isSet for monotone functions
  MonFunIsSet : {X Y : Poset ℓ ℓ'} -> isSet (MonFun X Y)
  MonFunIsSet {X} {Y} =
    let composedIso = (compIso isoMonFunMonFun' MonFun'IsoΣ) in
      isSetRetract
        (Iso.fun composedIso) (Iso.inv composedIso) (Iso.leftInv composedIso)
        (isSetΣSndProp
          (isSet→ (is-set (isPoset (str Y))))
          (isPropIsMon' {X} {Y}))



  -- Ordering on monotone functions
  module _ {X Y : Poset ℓ ℓ'} where

    _≤mon_ :
      MonFun X Y → MonFun X Y → Type (ℓ-max ℓ ℓ')
    _≤mon_ f g = ∀ x -> (PosetStr._≤_ (Y .snd)) (MonFun.f f x) (MonFun.f g x)

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> (is-prop-valued (isPoset (str Y)))
        (MonFun.f f x) (MonFun.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → (is-refl (isPoset (str Y))) (MonFun.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      (is-trans (isPoset (str Y))) (MonFun.f f x) (MonFun.f g x) (MonFun.f h x)
        (f≤g x) (g≤h x)

    ≤mon-antisym : isAntisym _≤mon_
    ≤mon-antisym = λ f g f≤g g≤f → eqMon f g
      (funExt λ x →
        (is-antisym (isPoset (str Y))) (MonFun.f f x) (MonFun.f g x)
          (f≤g x) (g≤f x)
      )


    -- Alternate definition of ordering on monotone functions, where we allow
    -- for the arguments to be distinct
    _≤mon-het_ : MonFun X Y -> MonFun X Y -> Type (ℓ-max ℓ ℓ')
    _≤mon-het_ f f' = ∀ x x' ->
                      (PosetStr._≤_ (X .snd)) x x' ->
                      (PosetStr._≤_ (Y .snd)) (MonFun.f f x) (MonFun.f f' x')

    ≤mon→≤mon-het : (f f' : MonFun X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      MonFun.f f x    ≤⟨ MonFun.isMon f x≤x' ⟩
      MonFun.f f x'   ≤⟨ f≤f' x' ⟩
      MonFun.f f' x'  ◾
      where
        open PosetReasoning Y


 -- Poset of monotone functions between two posets
  IntHom : Poset ℓ ℓ' -> Poset ℓ ℓ' ->
    Poset (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  IntHom X Y =
    MonFun X Y ,
    (posetstr
      (_≤mon_)
      (isposet MonFunIsSet ≤mon-prop ≤mon-refl ≤mon-trans ≤mon-antisym))

    -- Notation
  _==>_ : Poset ℓ ℓ' -> Poset ℓ ℓ' ->
    Poset (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  X ==> Y = IntHom X Y -- IntHom X Y



  -- Some basic combinators/utility functions on monotone functions

  MonId : {X : Poset ℓ ℓ'} -> MonFun X X
  MonId = record { f = λ x -> x ; isMon = λ x≤y → x≤y }

  _$_ : {X Y : Poset ℓ ℓ'} -> MonFun X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = MonFun.f f x

  MonComp : {X Y Z : Poset ℓ ℓ'} ->
    MonFun X Y -> MonFun Y Z -> MonFun X Z
  MonComp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) }
