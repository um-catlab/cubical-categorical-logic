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
  data Ĉ₀ : Type (ℓ-max ℓ ℓ') where
    i : (C .ob) → Ĉ₀
    j : {a b : C .ob}(e : CatIso C a b) → i a ≡ i b
    jid : {a : C .ob} → j {a} idCatIso ≡ refl
    jcomp : {a b c : C .ob}(f : CatIso C a b)(g : CatIso C b c) → j (⋆Iso f g) ≡ j f ∙ j g
    1-truncation : (x y : Ĉ₀)(p q : x ≡ y)(r s : p ≡ q) → r ≡ s

  -- the paragraph directly following the HIT definition, below theorem 9.9.5 of the HOTT book
  -- TODO: I don't really get why we want this theorem
  _ : (a b : C .ob)(p : a ≡ b) → j (pathToIso p) ≡ congS i p
  _ = λ a b p → J
    (λ y → λ eq → j (pathToIso eq) ≡ congS i eq)
    (j (pathToIso refl) ≡⟨ congS j pathToIso-refl ⟩ j idCatIso ≡⟨ jid ⟩ congS i refl ∎)
    p

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Category.Base
  open Cubical.Categories.Category.isIso
  open import Cubical.Foundations.Univalence
  open import Cubical.Foundations.Equiv
  -- Step 1: We define a family by double induction on Ĉ₀
  Ĉ₁ : Ĉ₀ → Ĉ₀ → Type _
  Ĉ₁ (i a) (i b) = (C [ a , b ])
  -- Let us keep x = i a fixed at first
  Ĉ₁ (i a) (j {b} {b'} e i') = ua (isoToEquiv
    (iso iso→ iso⁻¹←
      (λ g →
        iso→ (iso⁻¹← g) ≡⟨ refl ⟩
        g ⋆⟨ C ⟩ e⁻¹← ⋆⟨ C ⟩ e→ ≡⟨ C .⋆Assoc g e⁻¹← e→ ⟩
        g ⋆⟨ C ⟩ (e⁻¹← ⋆⟨ C ⟩ e→) ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (e .snd .sec) ⟩
        g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩
        g ∎)
      (λ f →
        iso⁻¹← (iso→ f) ≡⟨ refl ⟩
        f ⋆⟨ C ⟩ e→ ⋆⟨ C ⟩ e⁻¹← ≡⟨ C .⋆Assoc f e→ e⁻¹← ⟩
        f ⋆⟨ C ⟩ (e→ ⋆⟨ C ⟩ e⁻¹←) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (e .snd .ret) ⟩
        f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩
        f ∎ ))) i'
    where
    e→ = e .fst
    e⁻¹← = e .snd .inv
    -- let f ∈ C [ a , b ], g ∈ C [ a , b' ]
    -- explicit types to manually supply contraints
    iso→ : C [ a , b ] → C [ a , b' ]
    iso→ f = f ⋆⟨ C ⟩ e→
    iso⁻¹← : C [ a , b' ] → C [ a , b ]
    iso⁻¹← g = g ⋆⟨ C ⟩ e⁻¹←
  -- As y varies along the identity j 1\_b = reflᵢ\_b
  Ĉ₁ (i a) (jid {b} i' i'') = (proof⋆id ≡⟨ congS ua (equivEq (funExt λ f → C .⋆IdR f)) ⟩
    ua (idEquiv (C [ a , b ])) ≡⟨ uaIdEquiv ⟩
    refl ∎) i' i''
    where
    iso→ : C [ a , b ] → C [ a , b ]
    iso→ f = f ⋆⟨ C ⟩ (C .id)
    iso⁻¹← : C [ a , b ] → C [ a , b ]
    iso⁻¹← g = g ⋆⟨ C ⟩ (C .id)
    proof⋆id : C [ a , b ] ≡ C [ a , b ]
    proof⋆id = ua (isoToEquiv
      (iso iso→ iso⁻¹←
        (λ g →
          iso→ (iso⁻¹← g) ≡⟨ refl ⟩
          g ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ C .id ≡⟨ C .⋆Assoc g (C .id) (C .id) ⟩
          g ⋆⟨ C ⟩ (C .id ⋆⟨ C ⟩ C .id) ≡⟨ congS (λ eq → g ⋆⟨ C ⟩ eq) (C .⋆IdL (C .id)) ⟩
          g ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR g ⟩ g ∎)
        (λ f →
          iso⁻¹← (iso→ f) ≡⟨ refl ⟩
          f ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ C .id ≡⟨ C .⋆Assoc f (C .id) (C .id) ⟩
          f ⋆⟨ C ⟩ (C .id ⋆⟨ C ⟩ C .id) ≡⟨ congS (λ eq → f ⋆⟨ C ⟩ eq) (C .⋆IdL (C .id)) ⟩
          f ⋆⟨ C ⟩ C .id ≡⟨ C .⋆IdR f ⟩
          f ∎)))
  -- Similarly, as y varies along the identity j (g ∘ f) = j f ∘ j g
  Ĉ₁ (i a) (jcomp {b} {c} {d} f g i' i'') = (({!!} ∙ {!!})) i' i''
  --Ĉ₁ (j {a} {a'} e i') (i b) = {!!}
