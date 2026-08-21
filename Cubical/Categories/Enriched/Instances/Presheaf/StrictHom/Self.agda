{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Instances.Presheaf.StrictHom.Self where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁;π₂)
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Morphism.Alt

open Category
open Bifunctor
open BinProduct
open EnrichedCategory
open Functor
open MonoidalCategory
open MonoidalStr
open NatIso
open NatTrans
open TensorStr

private
  variable
    ℓ ℓ' ℓS : Level

module _ (C : Category ℓ ℓ')(ℓS : Level) where
  open PshMon C ℓS

  adjL : {P Q R : ob 𝓟} → 𝓟 [ P ×Psh Q , R ] → 𝓟 [ P , R ^ Q ]
  adjL {P}{Q}{R} f = λPshHomStrict Q R f

  dup : {P : ob 𝓟} → 𝓟 [ P , P ×Psh P ]
  dup = pshhom (λ x x₁ → x₁ , x₁) λ _  _ _ _ _ x → cong₂ _,_ x x

  swap : {P Q : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ×Psh P ]
  swap = dup ⋆⟨ 𝓟 ⟩  ⨂' .Bif-hom× π₂p π₁p

  selfid : {P : ob 𝓟} → 𝓟 [ 𝟙 , (P ^ P) ]
  selfid .PshHomStrict.N-ob Γ tt = π₂ _ _
  selfid .PshHomStrict.N-hom γ = λ _ _ _ _ _ → refl

  expseq : {P Q R : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh (R ^ Q) ,  (R ^ P) ]
  expseq {P}{Q}{R} =
    adjL (
      swap ⋆⟨ 𝓟 ⟩
      assoc ⋆⟨ 𝓟 ⟩
      ⨂' .Bif-hom× swap idPshHomStrict ⋆⟨ 𝓟 ⟩
      ⨂' .Bif-hom× eval idPshHomStrict ⋆⟨ 𝓟 ⟩
      swap ⋆⟨ 𝓟 ⟩
      eval )

  self : EnrichedCategory 𝓟Mon (ℓ-suc ℓm)
  self .ob = ob 𝓟
  self .Hom[_,_] P Q = Q ^ P
  self .id = selfid
  self .seq P Q R = expseq
  self .⋆IdL P Q =
    makePshHomStrictPath (funExt λ c → funExt λ{(tt* , f) →
      makePshHomStrictPath (funExt λ c' → funExt λ {(g , Pc') →
        cong (λ h → f .PshHomStrict.N-ob c' (h , Pc')) (sym (C .⋆IdL _ ))})})
  self .⋆IdR P Q =
    makePshHomStrictPath (funExt λ c → funExt λ{(f , tt*) →
      makePshHomStrictPath (funExt λ c' → funExt λ {(g , Pc') →
        cong (λ h → f .PshHomStrict.N-ob c' (h , Pc')) (sym (C .⋆IdL _ ))})})
  self .⋆Assoc P Q R S =
    makePshHomStrictPath (funExt λ c → funExt λ{ (f , g , h) →
      makePshHomStrictPath (funExt λ c' → funExt λ{ (j , Pc') →
        cong (h .PshHomStrict.N-ob c') ((cong₂ _,_ (sym (C .⋆IdL _)) refl))
        ∙ cong (λ e →
          h .PshHomStrict.N-ob c' ((C ⋆ id C) ((C ⋆ id C) j),
          g .PshHomStrict.N-ob c' ((C ⋆ id C) ((C ⋆ id C) j) ,
          f .PshHomStrict.N-ob c' (e , Pc'))))
        (cong (C ⋆ id C)  (C .⋆IdL _))})})
