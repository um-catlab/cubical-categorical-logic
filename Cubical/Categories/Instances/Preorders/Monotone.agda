{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Preorders.Monotone where

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

open import Cubical.Relation.Binary.Preorder

open import Cubical.Reflection.RecordEquiv.More

open BinaryRelation


private
  variable
    ℓ ℓ' : Level



module _ {ℓ ℓ' : Level} where

  module _ {X Y : Preorder ℓ ℓ'} where

    module X = PreorderStr (X .snd)
    module Y = PreorderStr (Y .snd)
    _≤X_ = X._≤_
    _≤Y_ = Y._≤_

    monotone : (⟨ X ⟩ -> ⟨ Y ⟩) -> Type (ℓ-max ℓ ℓ')
    monotone f = {x y : ⟨ X ⟩} -> x ≤X y → f x ≤Y f y

  -- Monotone functions from X to Y
  module _ (X Y : Preorder ℓ ℓ') where
    record MonFun : Type ((ℓ-max ℓ ℓ')) where
      field
        f : (X .fst) → (Y .fst)
        isMon : monotone {X} {Y} f

    -- Sigma type for easy reflection proofs of prop/isset
    -- Because of a bug with Cubical Agda's reflection, we need to declare
    -- an explicit Sigma type construction and declare the type signature
    -- to be able to get the definition for free
    -- See https://github.com/agda/cubical/issues/995.
    Sigma : Type (ℓ-max ℓ ℓ')
    Sigma = (Σ (X .fst → Y .fst)
      (λ z → {x y : ⟨ X ⟩} → _≤X_ {X} {Y} x y → _≤Y_ {X} {Y} (z x) (z y)))

    MonFunIsoΣ : Iso (MonFun) (Sigma)
    unquoteDef MonFunIsoΣ = defineRecordIsoΣ MonFunIsoΣ (quote (MonFun))

  open MonFun
  open IsPreorder
  open PreorderStr


  isPropIsMon : {X Y : Preorder ℓ ℓ'} -> (f : ⟨ X ⟩ →  ⟨ Y ⟩) ->
    isProp (monotone {X} {Y} f)
  isPropIsMon {X} {Y} f =
    isPropImplicitΠ2 (λ x y ->
      isPropΠ (λ x≤y -> is-prop-valued (isPreorder (str Y))
        (f x) (f y)))


  -- Equality of monotone functions is equivalent to equality of the
  -- underlying functions.
  eqMon : {X Y : Preorder ℓ ℓ'} -> (f g : MonFun X Y) ->
    MonFun.f f ≡ MonFun.f g -> f ≡ g
  eqMon {X} {Y} f g p = isoFunInjective (MonFunIsoΣ X Y) f g
    (Σ≡Prop (isPropIsMon {X} {Y}) p)


  -- isSet for monotone functions
  MonFunIsSet : {X Y : Preorder ℓ ℓ'} → isSet ⟨ Y ⟩ → isSet (MonFun X Y)
  MonFunIsSet {X} {Y} issetY =
    let the-iso = MonFunIsoΣ X Y in
    isSetRetract
      (Iso.fun the-iso) (Iso.inv the-iso) (Iso.leftInv the-iso)
      (isSetΣSndProp
        (isSet→ issetY)
        (isPropIsMon {X} {Y}))


  -- Ordering on monotone functions
  module _ {X Y : Preorder ℓ ℓ'} where

    _≤mon_ :
      MonFun X Y → MonFun X Y → Type (ℓ-max ℓ ℓ')
    _≤mon_ f g = ∀ x -> (PreorderStr._≤_ (Y .snd)) (MonFun.f f x) (MonFun.f g x)

    ≤mon-prop : isPropValued _≤mon_
    ≤mon-prop f g =
      isPropΠ (λ x -> (is-prop-valued (isPreorder (str Y)))
        (MonFun.f f x) (MonFun.f g x))

    ≤mon-refl : isRefl _≤mon_
    ≤mon-refl = λ f x → (is-refl (isPreorder (str Y))) (MonFun.f f x)

    ≤mon-trans : isTrans _≤mon_
    ≤mon-trans = λ f g h f≤g g≤h x →
      (is-trans (isPreorder (str Y)))
        (MonFun.f f x) (MonFun.f g x) (MonFun.f h x)
        (f≤g x) (g≤h x)


    -- Alternate definition of ordering on monotone functions, where we allow
    -- for the arguments to be distinct
    _≤mon-het_ : MonFun X Y -> MonFun X Y -> Type (ℓ-max ℓ ℓ')
    _≤mon-het_ f f' = ∀ x x' ->
                      (PreorderStr._≤_ (X .snd)) x x' ->
                      (PreorderStr._≤_ (Y .snd)) (MonFun.f f x) (MonFun.f f' x')

    ≤mon→≤mon-het : (f f' : MonFun X Y) -> f ≤mon f' -> f ≤mon-het f'
    ≤mon→≤mon-het f f' f≤f' = λ x x' x≤x' →
      MonFun.f f x    ≤⟨ MonFun.isMon f x≤x' ⟩
      MonFun.f f x'   ≤⟨ f≤f' x' ⟩
      MonFun.f f' x'  ◾
      where
        open PreorderReasoning Y


  -- Some basic combinators/utility functions on monotone functions

  MonId : {X : Preorder ℓ ℓ'} -> MonFun X X
  MonId = record { f = λ x -> x ; isMon = λ x≤y → x≤y }

  _$_ : {X Y : Preorder ℓ ℓ'} -> MonFun X Y -> ⟨ X ⟩ -> ⟨ Y ⟩
  f $ x = MonFun.f f x

  MonComp : {X Y Z : Preorder ℓ ℓ'} ->
    MonFun X Y -> MonFun Y Z -> MonFun X Z
  MonComp f g = record {
    f = λ x -> g $ (f $ x) ;
    isMon = λ {x1} {x2} x1≤x2 → isMon g (isMon f x1≤x2) }
