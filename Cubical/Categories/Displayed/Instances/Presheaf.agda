{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
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

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}(F : Functor C D)(G : Functor D E) where
  ∘F^opF : (G ∘F F) ^opF ≡ (G ^opF) ∘F (F ^opF)
  ∘F^opF = Functor≡ (λ _ → refl) (λ _ → refl)

module _ (C : Category ℓC ℓC') ℓSET ℓSETᴰ where

  module _ (P : Presheaf C ℓSET) where
    ---- Displayed Sets
    --Presheafᴰ-ob : Type _
    --Presheafᴰ-ob = (Γ : C .ob) → ⟨ P ⟅ Γ ⟆ ⟩ → hSet ℓSETᴰ
    --module _ (Pᴰ-ob : Presheafᴰ-ob) where
    --  Presheafᴰ-hom : Type _
    --  Presheafᴰ-hom = ∀{Γ Δ}(f : C [ Γ , Δ ]) →
    --    (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
    --    ⟨ Pᴰ-ob Δ ϕ ⟩ →
    --    ⟨ Pᴰ-ob Γ (ϕ ∘ᴾ⟨ C , P ⟩ f) ⟩

    --Presheafᴰ : Type _
    --Presheafᴰ = Σ[ Pᴰ-ob ∈ Presheafᴰ-ob ] Presheafᴰ-hom Pᴰ-ob

    ---- TODO: use implicit args instead of private modules
    ---- This is so gross...
    --module PresheafᴰNotation (Pᴰ : Presheafᴰ) where
    --  ⟅_,_⟆ : (Γ : C .ob) → ⟨ P ⟅ Γ ⟆ ⟩ → hSet ℓSETᴰ
    --  ⟅ Γ , ϕ ⟆ = Pᴰ .fst Γ ϕ
    --  actionᴰ : {Γ Δ : C .ob} (f : C [ Γ , Δ ]) →
    --    (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
    --    ⟨ ⟅ Δ , ϕ ⟆ ⟩ →
    --    ⟨ ⟅ Γ , ϕ ∘ᴾ⟨ C , P ⟩ f ⟆ ⟩
    --  actionᴰ = Pᴰ .snd
    --  syntax actionᴰ f ϕ ϕᴰ = ϕᴰ ∘ᴾ⟨ ϕ ⟩ f

    --open Contravariant
    Presheafᴰ' : Type _
    Presheafᴰ' = Presheaf (∫ᴾ P) ℓSETᴰ

    --module _ (Pᴰ : Presheafᴰ) where
    --  private module Pᴰ = PresheafᴰNotation Pᴰ
    --  open Contravariant
    --  open import Cubical.Foundations.Transport
    --  --Presheafᴰ→Presheafᴰ' : Presheafᴰ → Presheafᴰ'
    --  --Presheafᴰ→Presheafᴰ' Pᴰ .F-ob (Γ , ϕ) = Pᴰ.⟅ Γ , ϕ ⟆
    --  --Presheafᴰ→Presheafᴰ' Pᴰ .F-hom {x = (Δ , ϕ')} {y = (Γ , ϕ)} (f , p) ϕᴰ =
    --  --  subst (λ x → ⟨ Pᴰ.⟅ Γ , x ⟆ ⟩) p (ϕᴰ Pᴰ.∘ᴾ⟨ ϕ' ⟩ f)
    --  --  --subst (λ x → ⟨ Pᴰ.⟅ Δ , x ⟆ ⟩) p (ϕᴰ Pᴰ.∘ᴾ⟨ ϕ ⟩ f)
    --  --Presheafᴰ→Presheafᴰ' Pᴰ .F-id {x = (Γ , ϕ)} = funExt (λ ϕᴰ → {!(∫ᴾ P) .id {x = Γ , ϕ} .snd!})
    --  --  --funExt (λ ϕᴰ → {!!} ) --(isSet-subst (Pᴰ.⟅ Γ , ϕ ⟆ .snd) {!(∫ᴾ P) .id {x = (Γ , ϕ)} .snd!} {!!}) ∙ {!!}) --substRefl {B = λ x → ⟨ Pᴰ.⟅ Γ , x ⟆ ⟩} ϕᴰ)
    --  --  -- funExt λ ϕᴰ →
    --  --  --isSet-subst {!!} {!!} {!!}
    --  --Presheafᴰ→Presheafᴰ' Pᴰ .F-seq = {!!}

    --Presheafᴰ'→Presheafᴰ : Presheafᴰ' → Presheafᴰ
    --Presheafᴰ'→Presheafᴰ Pᴰ' .fst Γ ϕ = Pᴰ' ⟅ Γ , ϕ ⟆
    --Presheafᴰ'→Presheafᴰ Pᴰ' .snd f ϕ = Pᴰ' ⟪ f , refl ⟫

  ---- Displayed Natural Transformation-- of presheaves specifically
  ---- (left Categoryᴰ is trivial, compared to general NatTransᴰ)
  --module _ {P Q : Presheaf C ℓSET}(α : P ⇒ Q)
  --  (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
  --  private
  --    module Pᴰ = PresheafᴰNotation P Pᴰ
  --    module Qᴰ = PresheafᴰNotation Q Qᴰ
  --  NatTransᴰ-ob : Type _
  --  NatTransᴰ-ob = (Γ : C .ob) →
  --    (ϕ : ⟨ P ⟅ Γ ⟆ ⟩) →
  --    ⟨ Pᴰ.⟅ Γ , ϕ ⟆ ⟩ →
  --     ⟨ Qᴰ.⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆ ⟩
  --  module _ (αᴰ-ob : NatTransᴰ-ob) where
  --    open NatTrans
  --    NatTransᴰ-hom : Type _
  --    NatTransᴰ-hom = ∀{Γ Δ}(f : C [ Γ , Δ ]) →
  --      (ϕ : ⟨ P ⟅ Δ ⟆ ⟩) →
  --      (ϕᴰ : ⟨ Pᴰ.⟅ Δ , ϕ ⟆ ⟩) →
  --      PathP (λ i → congS (λ x → ⟨ Qᴰ.⟅ Γ , x ϕ ⟆ ⟩) (α .N-hom f) i)
  --        (αᴰ-ob Γ (ϕ ∘ᴾ⟨ C , P ⟩ f) (ϕᴰ Pᴰ.∘ᴾ⟨ _ ⟩ f))
  --        ((αᴰ-ob Δ ϕ ϕᴰ) Qᴰ.∘ᴾ⟨ _ ⟩ f)
  --  NatTransᴰ = Σ[ αᴰ-ob ∈ NatTransᴰ-ob ] NatTransᴰ-hom αᴰ-ob

  module _ {P Q : Presheaf C ℓSET}(α : P ⇒ Q) where
    ∫ᴾ⇒ : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾ⇒ .F-ob (Γ , ϕ) = Γ , (α ⟦ Γ ⟧) ϕ
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = f , funExt⁻ (sym (α .N-hom f)) ψ ∙ congS (α ⟦ Γ ⟧) p
    ∫ᴾ⇒ .F-id {x = Γ , ϕ} = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    ∫ᴾ⇒ .F-seq {x = Γ , ϕ} (f , p) (g , q) = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    module _ (Pᴰ : Presheafᴰ' P)(Qᴰ : Presheafᴰ' Q) where
      -- TODO: pretty sure this is right, but we should check on paper
      NatTransᴰ' : Type _
      NatTransᴰ' = Pᴰ ⇒ Qᴰ ∘F (∫ᴾ⇒ ^opF)
  idTransᴰ' : {P : Presheaf C ℓSET}{Pᴰ : Presheafᴰ' P} →
    NatTransᴰ' (idTrans P) Pᴰ Pᴰ
  idTransᴰ' .N-ob (Γ , ϕ) = λ x → x
  idTransᴰ' {P} {Pᴰ} .N-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = funExt (λ ϕᴰ →
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
  PRESHEAFᴰ' .ob[_] = Presheafᴰ'
  PRESHEAFᴰ' .Hom[_][_,_] = NatTransᴰ'
  PRESHEAFᴰ' .idᴰ = idTransᴰ'
  PRESHEAFᴰ' ._⋆ᴰ_  {f = α} {g = β} {xᴰ = Pᴰ} {yᴰ = Qᴰ} {zᴰ = Rᴰ} αᴰ βᴰ =
    seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) (pathToNatTrans
      (sym (congS (λ x → Rᴰ ∘F x)
        (congS _^opF (∫ᴾ⇒∘ α β) ∙ ∘F^opF _ _) ∙ F-assoc))))
  PRESHEAFᴰ' .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ = makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
    (funExt (λ (Γ , ϕ) → {!!}))
  PRESHEAFᴰ' .⋆IdRᴰ = {!!}
  PRESHEAFᴰ' .⋆Assocᴰ = {!!}
  PRESHEAFᴰ' .isSetHomᴰ = {!!}
