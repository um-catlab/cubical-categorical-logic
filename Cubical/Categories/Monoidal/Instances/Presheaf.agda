{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Monoidal.Instances.Presheaf where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open Bifunctor
open BinProduct
open Category
open Functor
open MonoidalCategory renaming (C to Cat)
open MonoidalStr
open NatIso
open NatTrans
open TensorStr

private
  variable
    ℓ ℓ' : Level

module PshMon (C : Category ℓ ℓ')(ℓS : Level) where
  ℓm = ℓ-max ℓ' (ℓ-max ℓ ℓS)
  𝓟 = PresheafCategory C (ℓm)

  ⨂' : Bifunctor 𝓟 𝓟 𝓟
  ⨂' = PshProd {ℓ}{ℓ'}{C}{ℓm}{ℓm}

  -- Agda chokes without explicit args
  ⨂ : Functor (𝓟 ×C 𝓟) 𝓟
  ⨂ = BifunctorToParFunctor
    {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
    {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
    {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}⨂'

  𝟙 : ob 𝓟
  𝟙 = LiftPsh UnitPsh ℓm

  𝓟Ten :  TensorStr 𝓟
  𝓟Ten . ─⊗─ = ⨂
  𝓟Ten .unit = 𝟙

  _^_ : ob 𝓟 → ob 𝓟 → ob 𝓟
  _^_ B A = A ⇒PshLarge B

  eval : {P Q : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh P , Q ]
  eval {P}{Q} = PshHom→NatTrans (appPshHom P Q)

  π₁p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , P ]
  π₁p {P}{Q} = PshHom→NatTrans (π₁ P Q)

  π₂p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ]
  π₂p {P}{Q} = PshHom→NatTrans (π₂ P Q)

  idl : ⨂ ∘F rinj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
  idl .trans = natTrans (λ P → π₂p) λ _ → makeNatTransPath refl
  idl .nIso P =
    isiso
      (natTrans (λ x Px → tt* , Px) λ _ → refl)
      (makeNatTransPath refl)
      (makeNatTransPath refl)

  idr : ⨂ ∘F linj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
  idr .trans = natTrans (λ P → π₁p) λ _ → makeNatTransPath refl
  idr .nIso P =
    isiso
      (natTrans (λ x Px → Px , tt*) λ _ → refl)
      (makeNatTransPath refl)
      (makeNatTransPath refl)

  assoc : {P Q R : ob 𝓟} → 𝓟 [ P ×Psh (Q ×Psh R) , (P ×Psh Q ) ×Psh R ]
  assoc .N-ob c (p , (q , r)) = (p , q) , r
  assoc .N-hom f = refl

  𝓟Mon' : MonoidalStr 𝓟
  𝓟Mon' .tenstr = 𝓟Ten
  𝓟Mon' .α =
    record {
      trans =
        natTrans
          (λ {(P , (Q , R)) → assoc})
          λ _ → makeNatTransPath refl ;
      nIso = λ{ (P , Q , R) →
        isiso
          (natTrans (λ{ c ((p , q) , r ) → p , (q , r)}) λ _ → refl)
          (makeNatTransPath refl)
          (makeNatTransPath refl) }}
  𝓟Mon' .η = idl
  𝓟Mon' .ρ = idr
  𝓟Mon' .pentagon P Q R S = makeNatTransPath refl
  𝓟Mon' .triangle P Q = makeNatTransPath refl

  𝓟Mon : MonoidalCategory (ℓ-suc ℓm) (ℓm)
  𝓟Mon .Cat = 𝓟
  𝓟Mon .monstr = 𝓟Mon'
