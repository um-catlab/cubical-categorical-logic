{-

  The family construction, displayed over SET.

  Cubical.Categories.Displayed.Instances.Family.Base takes a CATEGORY C
  and builds Fam C : Categoryᴰ (SET ℓ) with

    Hom[ f ][ xᴰ , yᴰ ] = ∀ x → C [ xᴰ x , yᴰ (f x) ]

  Here the input must be a MULTIcategory, and for a structural reason:
  the base morphism is I-ary, so the fibre data over it is the
  I-indexed family (Γᴰ i (γ i)), and the displayed hom has to be an
  I-ary thing in V.  A mere category could only relate ONE source to
  the target, so we would first have to combine the family into a
  single object — i.e. demand I-indexed products in V, and with them
  all the coherence that cartesian multicategories exist to avoid.
  With V a multicategory nothing has to be assumed.

  (The library's Fam is the unary shadow of this: a category is a
  multicategory whose arities are all singletons.)

-}
module Multicategory.Family where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Examples

private
  variable
    ℓI ℓ ℓV ℓV' : Level

open CartesianMulticategoryᴰ

module _ {ℓI ℓ : Level} (V : CartesianMulticategory ℓI ℓV ℓV') where
  private
    module V = CartesianMulticategory V

  Famᴰ : CartesianMulticategoryᴰ (SETₘ {ℓI} {ℓ}) (ℓ-max ℓ ℓV)
           (ℓ-max ℓI (ℓ-max ℓ ℓV'))
  Famᴰ .obᴰ X = ⟨ X ⟩ → V.ob
  Famᴰ .MHomᴰ[_][_,_] {I = I} {Γ = Γ} f Γᴰ Aᴰ =
    (γ : (i : I) → ⟨ Γ i ⟩) → V.MHom⟨ I ⟩[ (λ i → Γᴰ i (γ i)) , Aᴰ (f γ) ]
  Famᴰ .varᴰ i γ = V.var i
  Famᴰ ._⋆ᴰ_ {g = g} fᴰ gᴰ δ = fᴰ (λ i → g i δ) V.⋆ (λ i → gᴰ i δ)
  -- the base laws are refl, so ≡[ ] has already degenerated to ≡ and
  -- these are the laws of V, pointwise in the environment
  Famᴰ .⋆Varᴰ i gᴰ = funExt λ δ → V.⋆Var i _
  Famᴰ .⋆Idᴰ fᴰ = funExt λ γ → V.⋆Id _
  Famᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = funExt λ δ → V.⋆Assoc _ _ _
  Famᴰ .isSetMHomᴰ = isSetΠ λ _ → V.isSetMHom

-- logical predicates over SET are families of propositions …
Predᴰ : ∀ {ℓI ℓ} → CartesianMulticategoryᴰ (SETₘ {ℓI} {ℓ}) (ℓ-suc ℓ)
          (ℓ-max ℓI ℓ)
Predᴰ {ℓI} {ℓ} = Famᴰ (PROPₘ {ℓI} {ℓ})

-- … and proof-relevant ones are families of sets
Setᴰ : ∀ {ℓI ℓ} → CartesianMulticategoryᴰ (SETₘ {ℓI} {ℓ}) (ℓ-suc ℓ)
         (ℓ-max ℓI ℓ)
Setᴰ {ℓI} {ℓ} = Famᴰ (SETₘ {ℓI} {ℓ})

-- the predicate reading is definitional, not just an equivalence
module _ {ℓI ℓ} where
  open CartesianMulticategory (SETₘ {ℓI} {ℓ})

  _ : {I : Type ℓI} {Γ : Ctx I} {A : ob}
      {Γᴰ : (i : I) → Predᴰ {ℓI} {ℓ} .obᴰ (Γ i)} {Aᴰ : Predᴰ {ℓI} {ℓ} .obᴰ A}
      (f : MHom⟨ I ⟩[ Γ , A ])
    → Predᴰ {ℓI} {ℓ} .MHomᴰ[_][_,_] {I = I} {Γ = Γ} {A = A} f Γᴰ Aᴰ
      ≡ ((γ : (i : I) → ⟨ Γ i ⟩)
        → ((i : I) → ⟨ Γᴰ i (γ i) ⟩) → ⟨ Aᴰ (f γ) ⟩)
  _ = λ f → refl
