{-

  Reindexing a displayed cartesian multicategory along a multifunctor.

  Over a strict base this would be transport-free, but the base we care
  about is the SYNTAX, whose laws are path constructors, so F-var and
  F-⋆ are genuine paths and the operations must be reindexed along
  them.  The displayed laws then need to compare two base paths with
  the same endpoints — and that is free, because hom-sets are sets:
  hSetReasoning.Prectify rectifies, and the steps compose in the total
  space (∫≡) rather than through compPathP.

-}
module Multicategory.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
open import Cubical.Data.Sigma

open import Multicategory.Cartesian
open import Multicategory.Multifunctor
open import Multicategory.Displayed

module _ {ℓI ℓM ℓM' ℓN ℓN' ℓNᴰ ℓNᴰ' : Level}
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  (F : Multifunctor M N)
  (Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ')
  where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N
    module F = Multifunctor F
    module Nᴰ = CartesianMulticategoryᴰ Nᴰ

    -- the displayed homs of Nᴰ, as a family over a hom-SET: this is
    -- what makes the base path irrelevant
    module R {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
      {Γᴰ : (i : I) → Nᴰ.obᴰ (F.F-ob (Γ i))} {Aᴰ : Nᴰ.obᴰ (F.F-ob A)} =
      hSetReasoning
        (N.MHom⟨ I ⟩[ (λ i → F.F-ob (Γ i)) , F.F-ob A ] , N.isSetMHom)
        (λ h → Nᴰ.MHomᴰ[ h ][ Γᴰ , Aᴰ ])

    -- a family of total-space paths gives a total-space path of
    -- families, which is what the ⋆-congruences need
    pointwise : {ℓx ℓy : Level} {I : Type ℓI}
      {X : I → Type ℓx} {Y : (i : I) → X i → Type ℓy}
      {h h' : (i : I) → X i}
      {hᴰ : (i : I) → Y i (h i)} {hᴰ' : (i : I) → Y i (h' i)}
      → ((i : I) → Path (Σ (X i) (Y i)) (h i , hᴰ i) (h' i , hᴰ' i))
      → Path (Σ ((i : I) → X i) (λ k → (i : I) → Y i (k i)))
             (h , hᴰ) (h' , hᴰ')
    pointwise ps =
      ΣPathP (funExt (λ i → cong fst (ps i)) , λ k i → PathPΣ (ps i) .snd k)

  open CartesianMulticategoryᴰ

  reindexᴰ : CartesianMulticategoryᴰ M ℓNᴰ ℓNᴰ'
  reindexᴰ .obᴰ A = Nᴰ.obᴰ (F.F-ob A)
  reindexᴰ .MHomᴰ[_][_,_] t Γᴰ Aᴰ = Nᴰ.MHomᴰ[ F.F-hom t ][ Γᴰ , Aᴰ ]
  reindexᴰ .varᴰ i = R.reind (sym (F.F-var i)) (Nᴰ.varᴰ i)
  reindexᴰ ._⋆ᴰ_ {f = t} {g = g} tᴰ gᴰ =
    R.reind (sym (F.F-⋆ t g)) (tᴰ Nᴰ.⋆ᴰ gᴰ)
  reindexᴰ .⋆Varᴰ {Γᴰ = Γᴰ} {Δᴰ = Δᴰ} {g = g} i gᴰ =
    R.Prectify (R.≡out
      (R.reind-filler⁻ (sym (F.F-⋆ (M.var i) g))
       ∙ R.cong₂ᴰ (λ h hᴰ → hᴰ Nᴰ.⋆ᴰ gᴰ)
           (R.reind-filler⁻ (sym (F.F-var i)))
       ∙ R.≡in (Nᴰ.⋆Varᴰ i gᴰ)))
  reindexᴰ .⋆Idᴰ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} {f = t} tᴰ =
    R.Prectify (R.≡out
      (R.reind-filler⁻ (sym (F.F-⋆ t M.var))
       ∙ R.cong₂ᴰ (λ h hᴰ → tᴰ Nᴰ.⋆ᴰ hᴰ)
           (pointwise (λ i → R.reind-filler⁻ (sym (F.F-var i))))
       ∙ R.≡in (Nᴰ.⋆Idᴰ tᴰ)))
  reindexᴰ .⋆Assocᴰ {f = t} {g = g} {h = h} tᴰ gᴰ hᴰ =
    R.Prectify (R.≡out
      (R.reind-filler⁻ (sym (F.F-⋆ (t M.⋆ g) h))
       ∙ R.cong₂ᴰ (λ e eᴰ → eᴰ Nᴰ.⋆ᴰ hᴰ)
           (R.reind-filler⁻ (sym (F.F-⋆ t g)))
       ∙ R.≡in (Nᴰ.⋆Assocᴰ tᴰ gᴰ hᴰ)
       ∙ sym (R.cong₂ᴰ (λ e eᴰ → tᴰ Nᴰ.⋆ᴰ eᴰ)
           (pointwise (λ i → R.reind-filler⁻ (sym (F.F-⋆ (g i) h)))))
       ∙ sym (R.reind-filler⁻ (sym (F.F-⋆ t (λ i → g i M.⋆ h))))))
  reindexᴰ .isSetMHomᴰ = Nᴰ.isSetMHomᴰ
