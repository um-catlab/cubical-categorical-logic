{-

  Two generic pieces of displayed-presheaf machinery, used by every
  gluing argument over a category of renamings.

    makePshMHomPath   a multimorphism of presheaves is determined by
                      its N-ob, since forded naturality is a prop
    Predᴾᴰ            predicates on a presheaf closed under
                      restriction — the displayed presheaf category,
                      as a displayed cartesian multicategory.  Every
                      fibre is prop-valued, so all three displayed
                      laws are automatic.

  They live here rather than in a normalization file because they
  mention no syntax at all.

-}
module Multicategory.PresheafPred where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Presheaf

open Category
open PshMHom

-- a multimorphism of presheaves is determined by its N-ob, since
-- naturality is a prop
makePshMHomPath : {ℓc ℓc' ℓI ℓp : Level} {C : Category ℓc ℓc'} {I : Type ℓI}
  {Γ : I → Presheaf C ℓp} {A : Presheaf C ℓp}
  {M N : PshMHom Γ A} → M .N-ob ≡ N .N-ob → M ≡ N
makePshMHomPath {Γ = Γ} {A = A} p =
  isoFunInjective (PshMHomΣIso Γ A) _ _
    (ΣPathPProp (isPropN-hom Γ A) p)


-- predicates on a presheaf, closed under restriction: the displayed
-- presheaf category, as a displayed cartesian multicategory.  Every
-- fibre is prop-valued, so all three displayed laws are automatic.
module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  private
    module C = Category C

  PredOb : Presheaf C ℓp → Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp)))
  PredOb P =
    Σ[ S ∈ ((c : C.ob) → PresheafNotation.p[_] P c → hProp ℓp) ]
      ((c c' : C.ob) (f : C [ c , c' ]) (p : PresheafNotation.p[_] P c')
        → ⟨ S c' p ⟩ → ⟨ S c (PresheafNotation._⋆_ P f p) ⟩)

  open CartesianMulticategoryᴰ

  Predᴾᴰ : CartesianMulticategoryᴰ (PSHₘ C ℓI ℓp)
    (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp))) (ℓ-max ℓc (ℓ-max ℓI ℓp))
  Predᴾᴰ .obᴰ = PredOb
  Predᴾᴰ .MHomᴰ[_][_,_] {I} {Γ} {A} M Γᴰ Aᴰ =
    (c : C.ob) (γ : (i : I) → PresheafNotation.p[_] (Γ i) c)
    → ((i : I) → ⟨ Γᴰ i .fst c (γ i) ⟩)
    → ⟨ Aᴰ .fst c (M .N-ob c γ) ⟩
  Predᴾᴰ .varᴰ i c γ γᴰ = γᴰ i
  Predᴾᴰ ._⋆ᴰ_ Mᴰ gᴰ c δ δᴰ = Mᴰ c _ (λ i → gᴰ i c δ δᴰ)
  Predᴾᴰ .⋆Varᴰ {Γᴰ = Γᴰ} i gᴰ =
    isProp→PathP (λ k → isPropΠ3 (λ c γ _ → str (Γᴰ i .fst c _))) _ _
  Predᴾᴰ .⋆Idᴰ {Aᴰ = Aᴰ} Mᴰ =
    isProp→PathP (λ k → isPropΠ3 (λ c γ _ → str (Aᴰ .fst c _))) _ _
  Predᴾᴰ .⋆Assocᴰ {Aᴰ = Aᴰ} Mᴰ gᴰ hᴰ =
    isProp→PathP (λ k → isPropΠ3 (λ c γ _ → str (Aᴰ .fst c _))) _ _
  Predᴾᴰ .isSetMHomᴰ {Aᴰ = Aᴰ} =
    isProp→isSet (isPropΠ3 (λ c γ _ → str (Aᴰ .fst c _)))


-- ==================================================================
-- THE PROOF-RELEVANT VERSION.  Identical, except the fibres are SETS
-- rather than propositions — so a witness carries data, e.g. a normal
-- form rather than the assertion that one exists.
--
-- The displayed laws are then refl, not isProp→PathP.  Nothing about
-- prop-valuedness was making them cheap: the FORDED SHAPE was.  A
-- displayed hom is a function from hypotheses on the inputs to a
-- conclusion on the output, so composing them is composing functions,
-- and the laws are the η-computations that make PSHₘ strict.
module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  private
    module C = Category C

  FamOb : Presheaf C ℓp → Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp)))
  FamOb P =
    Σ[ S ∈ ((c : C.ob) → PresheafNotation.p[_] P c → hSet ℓp) ]
      ((c c' : C.ob) (f : C [ c , c' ]) (p : PresheafNotation.p[_] P c')
        → ⟨ S c' p ⟩ → ⟨ S c (PresheafNotation._⋆_ P f p) ⟩)

  open CartesianMulticategoryᴰ

  Famᴾᴰ : CartesianMulticategoryᴰ (PSHₘ C ℓI ℓp)
    (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp))) (ℓ-max ℓc (ℓ-max ℓI ℓp))
  Famᴾᴰ .obᴰ = FamOb
  Famᴾᴰ .MHomᴰ[_][_,_] {I} {Γ} {A} M Γᴰ Aᴰ =
    (c : C.ob) (γ : (i : I) → PresheafNotation.p[_] (Γ i) c)
    → ((i : I) → ⟨ Γᴰ i .fst c (γ i) ⟩)
    → ⟨ Aᴰ .fst c (M .N-ob c γ) ⟩
  Famᴾᴰ .varᴰ i c γ γᴰ = γᴰ i
  Famᴾᴰ ._⋆ᴰ_ Mᴰ gᴰ c δ δᴰ = Mᴰ c _ (λ i → gᴰ i c δ δᴰ)
  -- ALL THREE refl, with data-valued fibres
  Famᴾᴰ .⋆Varᴰ i gᴰ = refl
  Famᴾᴰ .⋆Idᴰ Mᴰ = refl
  Famᴾᴰ .⋆Assocᴰ Mᴰ gᴰ hᴰ = refl
  Famᴾᴰ .isSetMHomᴰ {Aᴰ = Aᴰ} =
    isSetΠ3 (λ c γ _ → str (Aᴰ .fst c _))
