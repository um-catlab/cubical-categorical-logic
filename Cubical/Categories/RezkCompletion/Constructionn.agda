{-

The Construction of Rezk Completion

-}
{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.RezkCompletion.Constructionn where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Constructions.EssentialImage
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.RezkCompletion.Base

private
  variable
    ℓ ℓ' : Level

open isWeakEquivalence


-- There are two different ways to construct the Rezk completion,
-- one is using the essential image of the Yoneda embbeding,
-- another one is using a higher inductive type
-- (c.f. HoTT Book Chaper 9.9).

-- Yoneda embbeding can give a very simple and quick construction.
-- Unfortunately, this construction increases the universe level.

-- The HIT construction, on the other hand, keeps the universe level,
-- but its proof is a bit long and tedious, still easy though.


{- The Construction by Yoneda Embedding -}

module RezkByYoneda (C : Category ℓ ℓ) where

  YonedaImage : Category (ℓ-suc ℓ) ℓ
  YonedaImage = EssentialImage (YO {C = C})

  isUnivalentYonedaImage : isUnivalent YonedaImage
  isUnivalentYonedaImage = isUnivalentEssentialImage _ isUnivalentPresheafCategory

  ToYonedaImage : Functor C YonedaImage
  ToYonedaImage = ToEssentialImage _

  isWeakEquivalenceToYonedaImage : isWeakEquivalence ToYonedaImage
  isWeakEquivalenceToYonedaImage .fullfaith = isFullyFaithfulToEssentialImage _ isFullyFaithfulYO
  isWeakEquivalenceToYonedaImage .esssurj   = isEssentiallySurjToEssentialImage YO

  isRezkCompletionToYonedaImage : isRezkCompletion ToYonedaImage
  isRezkCompletionToYonedaImage = makeIsRezkCompletion isUnivalentYonedaImage isWeakEquivalenceToYonedaImage


{- The Construction by Higher Inductive Type -}

module RezkByHIT (C : Category ℓ ℓ') where
  open import Cubical.Categories.Category
  open Cubical.Categories.Category.Category
  open import Cubical.Categories.Isomorphism
  -- TODO: Write the HIT construction of Rezk completion here.
  data Ĉ₀ : Type (ℓ-max ℓ ℓ') where -- TODO: is this the best we can do w/ the levels?
    i : (C .ob) → Ĉ₀
    j : {a b : C .ob}(e : CatIso C a b) → i a ≡ i b
    jid : {a : C .ob} → j {a} idCatIso ≡ refl
    jcomp : {a b c : C .ob}(f : CatIso C a b)(g : CatIso C b c) → j (⋆Iso f g) ≡ j f ∙ j g
    1-truncation : (x y : Ĉ₀)(p q : x ≡ y)(r s : p ≡ q) → r ≡ s

  -- the paragraph directly following the HIT definition, below theorem 9.9.5 of the HOTT book
  notethatfor : (a b : C .ob)(p : a ≡ b) → j (pathToIso p) ≡ congS i p
  notethatfor a b p = J (λ y → λ eq → j (pathToIso eq) ≡ congS i eq) (j (pathToIso refl) ≡⟨ congS j pathToIso-refl ⟩ j idCatIso ≡⟨ jid ⟩ congS i refl ∎) p -- TODO: I don't really get this proof and why we want this theorem

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Category.Base
  open Cubical.Categories.Category.isIso
  Ĉ₁ : Ĉ₀ → Ĉ₀ → Type _
  Ĉ₁ (i a) (i b) = (C [ a , b ])
  Ĉ₁ (i a) (j {b} {b'} e i') = isoToPath (iso iso→ iso⁻¹← (λ g → g ⋆⟨ C ⟩ e⁻¹← ⋆⟨ C ⟩ e→ ≡⟨ C .⋆Assoc g e⁻¹← e→ ⟩ g ⋆⟨ C ⟩ (e⁻¹← ⋆⟨ C ⟩ e→)  ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (e .snd .sec) ⟩ g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩ g ∎) (λ f → f ⋆⟨ C ⟩ e→ ⋆⟨ C ⟩ e⁻¹← ≡⟨ C .⋆Assoc f e→ e⁻¹← ⟩ f ⋆⟨ C ⟩ (e→ ⋆⟨ C ⟩ e⁻¹←) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (e .snd .ret) ⟩ f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩ f ∎ )) i'
    where
    e→ = e .fst
    e⁻¹← = e .snd .inv
    -- let f ∈ C [ a , b ], g ∈ C [ a , b' ]
    -- explicit types to manually supply contraints
    iso→ : C [ a , b ] → C [ a , b' ]
    iso→ f = f ⋆⟨ C ⟩ e→
    iso⁻¹← : C [ a , b' ] → C [ a , b ]
    iso⁻¹← g = g ⋆⟨ C ⟩ e⁻¹←
