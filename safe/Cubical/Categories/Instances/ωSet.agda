{- Category of ωSets.

  Defined explicitly, but equivalent to presheaves on the ordinal category ω.

  TODO: compare with using presheaves

-}
module Cubical.Categories.Instances.ωSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat as Nat hiding (elim)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)
import Cubical.HITs.SetTruncation as Trunc

open import Cubical.Categories.Category.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq


private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open PshIso
open UniversalElement

ωType ωSet : (ℓ : Level) → Type _
ωType ℓ = Σ[ Xi ∈ (ℕ → Type ℓ) ] (∀ i → Xi (suc i) → Xi i)
ωSet ℓ = Σ[ X ∈ ωType ℓ ] ∀ i → isSet (X .fst i)

ωHom : (X : ωType ℓ)(Y : ωType ℓ') → Type (ℓ-max ℓ ℓ')
ωHom X Y = Σ[ f ∈ (∀ n → X .fst n → Y .fst n) ]
  ∀ n x x'
    → X .snd n x ≡ x'
    → Y .snd n (f (suc n) x) ≡ f n x'

ωId : (X : ωType ℓ) → ωHom X X
ωId X .fst = λ n z → z
ωId X .snd = λ n x y z → z

ω⋆ : {X : ωType ℓ}{Y : ωType ℓ'}{Z : ωType ℓ''}
  → ωHom X Y
  → ωHom Y Z
  → ωHom X Z
ω⋆ f g .fst = λ n z → g .fst n (f .fst n z)
ω⋆ {X = X}{Y = Y}{Z = Z} f g .snd n x z Zπgf≡z = g .snd n (f .fst (suc n) x) (f .fst n z) (f .snd n x z Zπgf≡z)

ωSET : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
ωSET ℓ .ob = ωSet ℓ
ωSET ℓ .Hom[_,_] X Y = ωHom (X .fst) (Y .fst)
ωSET ℓ .id = ωId _
ωSET ℓ ._⋆_ {z = Z} f g = ω⋆ {Z = Z .fst} f g
ωSET ℓ .⋆IdL = λ _ → refl
ωSET ℓ .⋆IdR = λ _ → refl
ωSET ℓ .⋆Assoc = λ _ _ _ → refl
ωSET ℓ .isSetHom {y = Y} = isSetΣ (isSetΠ2 (λ _ _ → Y .snd _))
  λ _ → isSetΠ3 (λ _ _ _ → isSetΠ λ _ → isProp→isSet (Y .snd _ _ _))

▷ : ωType ℓ → ωType ℓ
▷ X .fst zero = Unit*
▷ X .fst (suc n) = X .fst n
▷ X .snd zero x = tt*
▷ X .snd (suc i) x = X .snd i x

▷ωSet : ωSet ℓ → ωSet ℓ
▷ωSet X .fst = ▷ (X .fst)
▷ωSet X .snd zero = isSetUnit*
▷ωSet X .snd (suc n) = X .snd n

▷Hom : {X : ωType ℓ}{Y : ωType ℓ'} → ωHom X Y → ωHom (▷ X) (▷ Y)
▷Hom f .fst zero x = tt*
▷Hom f .fst (suc n) x = f .fst n x
▷Hom f .snd zero = λ _ _ _ → refl
▷Hom f .snd (suc n) = f .snd n

▷F : Functor (ωSET ℓ) (ωSET ℓ)
▷F .F-ob X = ▷ωSet X
▷F .F-hom = ▷Hom
▷F .F-id = ΣPathP
  ( (funExt λ { zero → refl ; (suc n) → refl })
  , (funExt λ { zero → refl ; (suc n) → refl }))
▷F .F-seq f g = ΣPathP
  ( (funExt λ { zero → refl ; (suc n) → refl })
  , (funExt λ { zero → refl ; (suc n) → refl }))

Δ : (X : Type ℓ) → ωType ℓ
Δ X .fst _ = X
Δ X .snd _ pf = pf

ωUnit* : ∀ {ℓ} → ωType ℓ
ωUnit* = Δ Unit*

ωUnit*-Terminal : Terminal' (ωSET ℓ)
ωUnit*-Terminal .vertex = ωUnit* , λ _ → isSetUnit*
ωUnit*-Terminal .element = tt
ωUnit*-Terminal .universal A .equiv-proof _ .fst .fst .fst n a = tt*
ωUnit*-Terminal .universal A .equiv-proof _ .fst .fst .snd n x x' pf = refl
ωUnit*-Terminal .universal A .equiv-proof _ .fst .snd = refl
ωUnit*-Terminal .universal A .equiv-proof _ .snd _ = refl

module _ {X : ωType ℓ} where
  next : ωHom X (▷ X)
  next .fst = (▷ X) .snd
  next .snd zero _ _ _ i = tt*
  next .snd (suc n) x x' pf i = X .snd n (pf i)

  module _ (f : ωHom (▷ X) X) where
    |gfix| : ∀ n → X .fst n
    |gfix| zero = f .fst zero tt*
    |gfix| (suc n) = f .fst (suc n) (|gfix| n)

    |gfix|-nat : ∀ n → X .snd n (f .fst (suc n) (|gfix| n)) ≡ |gfix| n
    |gfix|-nat zero = f .snd zero (|gfix| zero) tt* refl
    |gfix|-nat (suc n) = f .snd (suc n) (|gfix| (suc n)) (|gfix| n) (|gfix|-nat n)

    gfix : ωHom (ωUnit* {ℓ = ℓ'}) X
    gfix .fst n _ = |gfix| n
    gfix .snd n _ _ pf = |gfix|-nat n

    gfix-fixed-fst : ∀ n → f .fst n (next .fst n (|gfix| n)) ≡ |gfix| n
    gfix-fixed-fst zero = refl
    gfix-fixed-fst (suc n) = cong (f .fst (suc n))
      (f .snd n (|gfix| n) (next .fst n (|gfix| n)) refl ∙ gfix-fixed-fst n)

nextNT : NatTrans Id (▷F {ℓ = ℓ})
nextNT .NatTrans.N-ob x = next
nextNT {ℓ} .NatTrans.N-hom {X} {Y} f = ΣPathPProp
  (λ _ → isPropΠ4 (λ n _ _ _ → ▷ωSet Y .snd n _ _))
  (funExt (λ { zero → refl ; (suc n) → funExt λ x →
    f .snd n x _ refl }))

guarded-fixed-points :
  ∀ {X : ωSet ℓ}
  → (f : ωSET ℓ [ ▷ωSet X , X ])
  → fixed-point (ωSET ℓ) (ωUnit* , (λ _ → isSetUnit*)) {x = X} (ω⋆ {Z = X .fst} next f)
guarded-fixed-points f .fst = gfix f
guarded-fixed-points {X = X} f .snd = ΣPathPProp (λ _ → isPropΠ4 λ _ _ _ _ → X .snd _ _ _)
    (funExt (λ n → funExt λ { _ → gfix-fixed-fst f n }))
