{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning

open Category
open Functor
open Categoryᴰ
open Contravariant
open NatTrans

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓSET : Level

-- TODO: move to Functor/
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
  (F : Functor C D)(G : Functor D E) where
  ∘F^opF : (G ∘F F) ^opF ≡ (G ^opF) ∘F (F ^opF)
  ∘F^opF = Functor≡ (λ _ → refl) (λ _ → refl)

module _ (C : Category ℓC ℓC') ℓSET ℓSETᴰ where
  module _ (P : Presheaf C ℓSET) where
    -- TODO: this is a name clash with the other Presheafᴰ, which is different
    -- (and not a displayed presheaf in the strictest sense of "displayed X")
    Presheafᴰ : Type _
    Presheafᴰ = Presheaf (∫ᴾ P) ℓSETᴰ
  module _ {P Q : Presheaf C ℓSET} (α : P ⇒ Q) where
    ∫ᴾ⇒ : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾ⇒ .F-ob (Γ , ϕ) = Γ , (α ⟦ Γ ⟧) ϕ
    -- the paths don't matter-- we're in a hSet (but it can make goals look crazy)
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = f , funExt⁻ (sym (α .N-hom f)) ψ ∙ congS (α ⟦ Γ ⟧) p
    ∫ᴾ⇒ .F-id {x = Γ , ϕ} = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    ∫ᴾ⇒ .F-seq {x = Γ , ϕ} (f , p) (g , q) = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    module _ (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
      -- TODO: pretty sure this is right, but we should check on paper
      NatTransᴰ : Type _
      NatTransᴰ = Pᴰ ⇒ (Qᴰ ∘F (∫ᴾ⇒ ^opF))
      module _ (αᴰ : NatTransᴰ) where
        _ : ((Γ , ϕ) : Σ (C .ob) λ Γ → ⟨ P ⟅ Γ ⟆ ⟩) →
          ⟨ Pᴰ  ⟅ Γ , ϕ ⟆ ⟩ → ⟨ Qᴰ ⟅ (Γ , (α ⟦ Γ ⟧) ϕ) ⟆ ⟩
        _ = αᴰ .N-ob

        _ : {(Γ , ϕ) (Δ , ψ) : (∫ᴾ P) .ob} ((f , p) : (∫ᴾ P) [ (Γ , ϕ) , (Δ , ψ) ]) →
          αᴰ ⟦ Γ , ϕ ⟧ ∘S Pᴰ ⟪ f , p ⟫
          ≡
          Qᴰ ⟪ f , _ ⟫ ∘S αᴰ ⟦ Δ , ψ ⟧
        _ = αᴰ .N-hom
  idTransᴰ : {P : Presheaf C ℓSET}{Pᴰ : Presheafᴰ P} →
    NatTransᴰ (idTrans P) Pᴰ Pᴰ
  idTransᴰ .N-ob (Γ , ϕ) = λ x → x
  idTransᴰ {P} {Pᴰ} .N-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = funExt (λ ϕᴰ →
    congS (λ x → Pᴰ .F-hom (f , x) ϕᴰ) ((P ⟅ Δ ⟆) .snd _ _ _ _))
  module _ {P Q R : Presheaf C ℓSET}(α : P ⇒ Q)(β : Q ⇒ R) where
    ∫ᴾ⇒∘ : ∫ᴾ⇒ (seqTrans α β) ≡ ∫ᴾ⇒ β ∘F ∫ᴾ⇒ α
    ∫ᴾ⇒∘ = Functor≡ (λ _ → refl) (λ _ → ΣPathP (refl , (R ⟅ _ ⟆) .snd _ _ _ _))
  --PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  --PRESHEAFᴰ .ob[_] P = Presheafᴰ P
  --PRESHEAFᴰ .Hom[_][_,_] α Pᴰ Qᴰ = NatTransᴰ α Pᴰ Qᴰ
  --PRESHEAFᴰ .idᴰ {x = P} {p = Pᴰ} .fst Γ ϕ ϕᴰ = ϕᴰ
  --PRESHEAFᴰ .idᴰ {x = P} {p = Pᴰ} .snd {Γ = Γ} {Δ = Δ} f ϕ ϕᴰ =
  --  subst (λ x →
  --    PathP (λ i → ⟨ Pᴰ.⟅ _ , x i ϕ ⟆ ⟩)
  --    (Pᴰ.actionᴰ f _ ϕᴰ) (Pᴰ.actionᴰ f _ ϕᴰ))
  --  triv refl
  --  where
  --    module Pᴰ = PresheafᴰNotation P Pᴰ
  --    triv : refl ≡ PresheafCategory C ℓSET .id {x = P} .NatTrans.N-hom f
  --    triv = compPathRefl ∙ congS (λ x → refl ∙ x) compPathRefl
  --PRESHEAFᴰ ._⋆ᴰ_ αᴰ βᴰ = {!!}
  --PRESHEAFᴰ .⋆IdLᴰ = {!!}
  --PRESHEAFᴰ .⋆IdRᴰ = {!!}
  --PRESHEAFᴰ .⋆Assocᴰ = {!!}
  --PRESHEAFᴰ .isSetHomᴰ = {!!}

  PRESHEAFᴰ' : Categoryᴰ (PresheafCategory C ℓSET) _ _
  PRESHEAFᴰ' .ob[_] = Presheafᴰ
  PRESHEAFᴰ' .Hom[_][_,_] = NatTransᴰ
  PRESHEAFᴰ' .idᴰ = idTransᴰ
  PRESHEAFᴰ' ._⋆ᴰ_  {f = α} {g = β} {xᴰ = Pᴰ} {yᴰ = Qᴰ} {zᴰ = Rᴰ} αᴰ βᴰ =
    seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) (pathToNatTrans
      (sym (congS (λ x → Rᴰ ∘F x)
        (congS _^opF (∫ᴾ⇒∘ α β) ∙ ∘F^opF _ _) ∙ F-assoc))))
  PRESHEAFᴰ' .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ = makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
    (funExt (λ (Γ , ϕ) → funExt λ ϕᴰ → {!αᴰ .N-ob (Γ , ϕ) ϕᴰ!}))
  PRESHEAFᴰ' .⋆IdRᴰ = {!!}
  PRESHEAFᴰ' .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makeNatTransPathP refl
    (congS (λ x → Sᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆Assoc _ _ _))
    (funExt (λ (Γ , ϕ) → funExt (λ ϕᴰ → {!!})))
  PRESHEAFᴰ' .isSetHomᴰ = isSetNatTrans
