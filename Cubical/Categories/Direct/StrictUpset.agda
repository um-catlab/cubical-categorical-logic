{-# OPTIONS --lossy-unification #-}
-- The strict-upset coend ◁ of a direct category — the Earlier modality,
-- dual to the Later modality ▷ of Cubical.Categories.Direct.StrictDownset.
module Cubical.Categories.Direct.StrictUpset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset using (▷Psh ; next)

private
  variable
    ℓ ℓ' ℓD : Level

module _ {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr C Wo) where
  open Category C
  open Functor
  open NatTrans
  open PshHomStrict
  open DirectNotation dir

  ↟Fun : (x : ob) → Functor C (SET ℓ')
  ↟Fun x .F-ob y =
    (Σ[ f ∈ C [ x , y ] ] (x ≺ y))
    , isSetΣ isSetHom (λ _ → isProp→isSet (isProp≺ x y))
  ↟Fun x .F-hom g (f , p) = (f ⋆ g) , ≺-postcomp p g
  ↟Fun x .F-id     = funExt λ (f , p) → Σ≡Prop (λ _ → isProp≺ _ _) (⋆IdR f)
  ↟Fun x .F-seq g h = funExt λ (f , p) → Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc f g h))

  ↟reindex : ∀ {x x'} (a : C [ x , x' ]) → NatTrans (↟Fun x') (↟Fun x)
  ↟reindex a .N-ob y (f , p) = (a ⋆ f) , ≺-precomp a p
  ↟reindex a .N-hom {y} {y'} g = funExt λ (f , p) →
    Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc a f g))

  module _ {ℓP} (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
      module ⊗x {x} = Tensor (↟Fun x) P

    ◁Psh : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ') ℓP)
    ◁Psh .F-ob x = (↟Fun x ⊗ P) , isSet⊗
    ◁Psh .F-hom a = ↟reindex a ⊗NT idTrans P
    ◁Psh .F-id {x} = funExt (⊗x.ind (λ _ → isSet⊗ _ _)
      λ (f , p) q → cong (⊗x._,⊗ q) (Σ≡Prop (λ _ → isProp≺ _ _) (⋆IdL f)))
    ◁Psh .F-seq a b = funExt (⊗x.ind (λ _ → isSet⊗ _ _)
      λ (f , p) q → cong (⊗x._,⊗ q) (Σ≡Prop (λ _ → isProp≺ _ _) (⋆Assoc b a f)))

    prev : PshHomStrict ◁Psh P
    prev .N-ob x = ⊗x.rec P.isSetPsh
      (λ (f , p) q → f P.⋆ q)
      (λ (f , p) g q → sym (P.⋆Assoc f g q))
    prev .N-hom x x' a t' t e =
      prevNat t' ∙ cong (prev .N-ob x) e
      where
        prevNat : (u : ↟Fun x' ⊗ P)
          → a P.⋆ prev .N-ob x' u ≡ prev .N-ob x (◁Psh .F-hom a u)
        prevNat = ⊗x.ind (λ _ → P.isSetPsh _ _)
          (λ (f , p) q → sym (P.⋆Assoc a f q))

  -- ◁ ⊣ ▷
  module _ {ℓP ℓQ} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module ⊗P {x} = Tensor (↟Fun x) P

      ◁transpose : (β : PshHomStrict P (▷Psh dir Q)) (z : ob)
                  → (↟Fun z ⊗ P) → ⟨ Q .F-ob z ⟩
      ◁transpose β z = ⊗P.rec Q.isSetPsh
        (λ (g , q₀) u → β .N-ob _ u .N-ob z (g , q₀))
        (λ (g , q₀) f u →
          sym (λ i → β .N-hom _ _ f u _ refl i .N-ob z (g , q₀)))

      ◁transposeNat : ∀ β z' z (h : C [ z' , z ]) (t' : ↟Fun z ⊗ P)
        → h Q.⋆ ◁transpose β z t'
          ≡ ◁transpose β z' (◁Psh P .F-hom h t')
      ◁transposeNat β z' z h = ⊗P.ind (λ _ → Q.isSetPsh _ _)
        λ (g , q₀) u → β .N-ob _ u .N-hom z' z h (g , q₀) _ refl

    ◁UMP : Iso (PshHomStrict (◁Psh P) Q) (PshHomStrict P (▷Psh dir Q))
    ◁UMP .Iso.fun α .N-ob y u = pshhom
      (λ z (g , q) → α .N-ob z ((g , q) ⊗P.,⊗ u))
      (λ z' z h (g , q) w hyp →
        α .N-hom z' z h ((g , q) ⊗P.,⊗ u) _ refl
        ∙ cong (λ v → α .N-ob z' (v ⊗P.,⊗ u)) hyp)
    ◁UMP .Iso.fun α .N-hom y' y k u' u hyp =
      makePshHomStrictPath (funExt λ z → funExt λ (g , q) →
        cong (α .N-ob z)
          (sym (⊗P.swap (g , q) k u') ∙ cong ((g , q) ⊗P.,⊗_) hyp))
    ◁UMP .Iso.inv β .N-ob = ◁transpose β
    ◁UMP .Iso.inv β .N-hom z' z h t' t hyp =
      ◁transposeNat β z' z h t' ∙ cong (◁transpose β z') hyp
    ◁UMP .Iso.sec β =
      makePshHomStrictPath (funExt λ y → funExt λ u →
        makePshHomStrictPath refl)
    ◁UMP .Iso.ret α =
      makePshHomStrictPath (funExt λ z →
        funExt (⊗P.ind (λ _ → Q.isSetPsh _ _) λ (g , q₀) u → refl))

  -- prev is the transpose of next
  module _ {ℓP} (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
      module ⊗P {x} = Tensor (↟Fun x) P

    transposeNext≡prev : ◁UMP P P .Iso.inv (next dir P) ≡ prev P
    transposeNext≡prev =
      makePshHomStrictPath (funExt λ z →
        funExt (⊗P.ind (λ _ → P.isSetPsh _ _) λ (g , q₀) u → refl))
