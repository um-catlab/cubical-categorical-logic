{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements

open import Cubical.Categories.Displayed.Base

open Category
open Functor
open NatTrans
open Categoryᴰ
open Contravariant

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (ℓSET ℓSETᴰ : Level) where
  module _ (P : Presheaf C ℓSET) where
    -- TODO: this is a name clash with the other Presheafᴰ, which is different
    -- (and not a displayed presheaf in the strictest sense of "displayed X")
    Presheafᴰ : Type _
    Presheafᴰ = Presheaf (∫ᴾ P) ℓSETᴰ

  module _ {P Q : Presheaf C ℓSET} (α : P ⇒ Q) where
    ∫ᴾ⇒ : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾ⇒ .F-ob (Γ , ϕ) = Γ , (α ⟦ Γ ⟧) ϕ
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) .fst = f
    -- the paths don't matter-- we're in a hSet
    -- (but it can make goals look crazy)
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) .snd = funExt⁻ (sym (α .N-hom f)) ψ ∙ congS (α ⟦ Γ ⟧) p
    ∫ᴾ⇒ .F-id {x = Γ , ϕ} = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    ∫ᴾ⇒ .F-seq {x = Γ , ϕ} (f , p) (g , q) = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)

    module _ (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
      -- data of (α-displayed natural transformations) of displayed presheaves
      NatTransᴰ : Type _
      NatTransᴰ = Pᴰ ⇒ (Qᴰ ∘F (∫ᴾ⇒ ^opF))
      -- "tests", to verify this encoding is exactly the data we want
      module _ (αᴰ : NatTransᴰ) where
        _ : ((Γ , ϕ) : Σ[ Γ ∈ C .ob ] ⟨ P ⟅ Γ ⟆ ⟩) →
          ⟨ Pᴰ  ⟅ Γ , ϕ ⟆ ⟩ → ⟨ Qᴰ ⟅ (Γ , (α ⟦ Γ ⟧) ϕ) ⟆ ⟩
        _ = αᴰ .N-ob

        _ : {(Γ , ϕ) (Δ , ψ) : (∫ᴾ P) .ob} ((f , p) : (∫ᴾ P) [ (Γ , ϕ) , (Δ , ψ) ]) →
          αᴰ ⟦ Γ , ϕ ⟧ ∘S Pᴰ ⟪ f , p ⟫
          ≡
          Qᴰ ⟪ f , _ ⟫ ∘S αᴰ ⟦ Δ , ψ ⟧
        _ = αᴰ .N-hom

  idTransᴰ : {P : Presheaf C ℓSET}{Pᴰ : Presheafᴰ P} →
    NatTransᴰ (idTrans P) Pᴰ Pᴰ
  idTransᴰ .N-ob (Γ , ϕ) = idfun _
  idTransᴰ {P} {Pᴰ} .N-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = funExt (λ ϕᴰ →
    congS (λ x → (Pᴰ ⟪ f , x ⟫) ϕᴰ) ((P ⟅ Δ ⟆) .snd _ _ _ _))
  module _ {P}{Q}{R}{α}{β}{Pᴰ : Presheafᴰ P}{Qᴰ : Presheafᴰ Q}{Rᴰ : Presheafᴰ R}
    (αᴰ : NatTransᴰ α Pᴰ Qᴰ)(βᴰ : NatTransᴰ β Qᴰ Rᴰ) where
    -- definition by pasting, st .N-ob has desirable definitional behavior
    seqTransᴰ : NatTransᴰ (seqTrans α β) Pᴰ Rᴰ
    seqTransᴰ = seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) fixup)
      where
      -- `((Rᴰ ∘F (∫ᴾ⇒ β ^opF)) ∘F (∫ᴾ⇒ α ^opF)) ≡
      -- (Rᴰ ∘F (∫ᴾ⇒ (seqTrans α β) ^opF))` holds, but pathToNatTrans gives
      -- .N-ob bad definitional behavior
      fixup : NatTrans
        ((Rᴰ ∘F (∫ᴾ⇒ β ^opF)) ∘F (∫ᴾ⇒ α ^opF))
        (Rᴰ ∘F (∫ᴾ⇒ (seqTrans α β) ^opF))
      fixup = natTrans (λ (Γ , ϕ) → idfun _)
        (λ (f , p) → funExt (λ βαϕᴰ →
          congS (λ x → (Rᴰ ⟪ f , x ⟫) βαϕᴰ) ((R ⟅ _ ⟆) .snd _ _ _ _)))
    -- "test"
    _ : seqTransᴰ .N-ob ≡ λ (Γ , ϕ) → βᴰ ⟦ Γ , (α ⟦ Γ ⟧) ϕ ⟧ ∘S αᴰ ⟦ Γ , ϕ ⟧
    _ = refl

  PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  PRESHEAFᴰ .ob[_] = Presheafᴰ
  PRESHEAFᴰ .Hom[_][_,_] = NatTransᴰ
  PRESHEAFᴰ .idᴰ = idTransᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = seqTransᴰ
  PRESHEAFᴰ .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
    refl
  PRESHEAFᴰ .⋆IdRᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdR _))
    refl
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makeNatTransPathP refl
    (congS (λ x → Sᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆Assoc _ _ _))
    refl
  PRESHEAFᴰ .isSetHomᴰ = isSetNatTrans
