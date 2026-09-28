module Cubical.Categories.Enriched.Instances.Presheaf.Self where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.BinProduct
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
  adjL {P}{Q}{R} f = PshHom→NatTrans (λPshHom Q R (NatTrans→PshHom f))

  dup : {P : ob 𝓟} → 𝓟 [ P , P ×Psh P ]
  dup = natTrans (λ x x₁ → x₁ , x₁) λ _ → refl

  swap : {P Q : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ×Psh P ]
  swap = dup ⋆⟨ 𝓟 ⟩  ⨂' .Bif-hom× π₂p π₁p

  selfid : {P : ob 𝓟} → NatTrans 𝟙 (P ^ P)
  selfid {P} .N-ob Γ tt* = π₂ _ _
  selfid {P} .N-hom γ = funExt λ tt* → makePshHomPath refl

  expseq : {P Q R : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh (R ^ Q) ,  (R ^ P) ]
  expseq {P}{Q}{R} =
    adjL (
      swap ⋆⟨ 𝓟 ⟩
      assoc ⋆⟨ 𝓟 ⟩
      ⨂' .Bif-hom× swap (idTrans _) ⋆⟨ 𝓟 ⟩
      ⨂' .Bif-hom× eval (idTrans _) ⋆⟨ 𝓟 ⟩
      swap ⋆⟨ 𝓟 ⟩
      eval )

  self : EnrichedCategory 𝓟Mon (ℓ-suc ℓm)
  self .ob = ob 𝓟
  self .Hom[_,_] P Q = Q ^ P
  self .id = selfid
  self .seq P Q R = expseq
  self .⋆IdL P Q =
    makeNatTransPath (funExt λ c → funExt λ{(tt* , f) →
      makePshHomPath  (funExt λ c' → funExt λ {(g , Pc') →
        cong (λ h → f .PshHom.N-ob c' (h , Pc')) (sym (C .⋆IdL _ ))})})
  self .⋆IdR P Q =
    makeNatTransPath (funExt λ c → funExt λ{(f , tt*) →
      makePshHomPath  (funExt λ c' → funExt λ {(g , Pc') →
        cong (λ h → f .PshHom.N-ob c' (h , Pc')) (sym (C .⋆IdL _ ))})})
  self .⋆Assoc P Q R S =
    makeNatTransPath (funExt λ c → funExt λ{ (f , g , h) →
      makePshHomPath (funExt λ c' → funExt λ{ (j , Pc') →
        cong (h .PshHom.N-ob c') ((cong₂ _,_ (sym (C .⋆IdL _)) refl))
        ∙ cong (λ e →
          h .PshHom.N-ob c' ((C ⋆ id C) ((C ⋆ id C) j),
          g .PshHom.N-ob c' ((C ⋆ id C) ((C ⋆ id C) j) ,
          f .PshHom.N-ob c' (e , Pc'))))
        (cong (C ⋆ id C)  (C .⋆IdL _))})})
