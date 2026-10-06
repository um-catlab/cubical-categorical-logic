{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)

module Cubical.Categories.Direct.Guarded.Monoid.Free (Alph : hSet ℓ-zero) where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; isProp≤)
open import Cubical.Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList ; cons-inj₁ ; cons-inj₂ ; ¬cons≡nil)

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Instances.Monoid.Instances using (StringGM ; String-conical)

private
  GM = StringGM Alph

open import Cubical.Categories.Direct.Guarded.Monoid GM
  using (Fam ; _⊗_ ; N ; √ ; ▷ ; √⊗ ; √-cong ; 𝟏 ; √𝟏≅Id×▷)

private
  module Fam = Category Fam
  isSetWord : isSet (List ⟨ Alph ⟩)
  isSetWord = isOfHLevelList 0 (Alph .snd)

L : Fam.ob
L (_ , w) = (Σ[ c ∈ ⟨ Alph ⟩ ] (w ≡ c ∷ [])) , isSetΣ (Alph .snd) λ _ → isProp→isSet (isSetWord _ _)

isPropL⊗𝟏 : ∀ w → isProp ⟨ (L ⊗ 𝟏) (tt , w) ⟩
isPropL⊗𝟏 w (u , v , p , (c , q) , _) (u' , v' , p' , (c' , q') , _) =
  ΣPathP (uu , ΣPathP (vv , ΣPathP (isProp→PathP (λ i → isSetWord (uu i ++ vv i) w) p p'
    , ΣPathP (ΣPathP (cc , isProp→PathP (λ i → isSetWord (uu i) (cc i ∷ [])) q q') , refl))))
  where
  e : c ∷ v ≡ c' ∷ v'
  e = cong (_++ v) (sym q) ∙ p ∙ sym p' ∙ cong (_++ v') q'
  cc : c ≡ c'
  cc = cons-inj₁ e
  vv : v ≡ v'
  vv = cons-inj₂ e
  uu : u ≡ u'
  uu = q ∙ cong (_∷ []) cc ∙ sym q'

N≅L⊗𝟏 : ∀ w → Iso ⟨ N (tt , w) ⟩ ⟨ (L ⊗ 𝟏) (tt , w) ⟩
N≅L⊗𝟏 [] = iso ⊥.rec (λ x → ⊥.rec (absurd x)) (λ x → ⊥.rec (absurd x)) λ ()
  where
  absurd : ⟨ (L ⊗ 𝟏) (tt , []) ⟩ → ⊥
  absurd (u , v , p , (c , q) , _) = ¬cons≡nil (cong (_++ v) (sym q) ∙ p)
N≅L⊗𝟏 (c ∷ v) = iso (λ _ → c ∷ [] , v , refl , (c , refl) , tt) (λ _ → tt)
  (λ x → isPropL⊗𝟏 (c ∷ v) _ x) (λ _ → refl)

▷≅√L√𝟏 : ∀ C w → Iso ⟨ ▷ C (tt , w) ⟩ ⟨ √ L (√ 𝟏 C) (tt , w) ⟩
▷≅√L√𝟏 C w = compIso (√-cong C w N≅L⊗𝟏) (√⊗ L 𝟏 C w)

String-√𝟏≅Id×▷ : ∀ C w → Iso ⟨ √ 𝟏 C (tt , w) ⟩ (⟨ C (tt , w) ⟩ × ⟨ ▷ C (tt , w) ⟩)
String-√𝟏≅Id×▷ = √𝟏≅Id×▷ (String-conical Alph)
