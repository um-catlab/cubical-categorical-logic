{-

  Displayed cartesian multicategories.

  Same intervention as displayed categories: the displayed laws are
  dependent paths over the laws of the base.  Over a STRICT base the
  base laws are refl, so ≡[ ] degenerates to ≡ and the displayed
  structure is as strict as the base — which is the point of having
  made SET strict.  The instances live in Multicategory.Family:
  displayed over SET, a family of propositions is a logical predicate,
  and every one of its laws is refl.

  A Sectionᴰ of a displayed multicategory is the shape of the
  fundamental theorem: an interpretation of every multimorphism by a
  displayed one over it.

-}
module Multicategory.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Multicategory.Cartesian

record CartesianMulticategoryᴰ
    {ℓI ℓM ℓM' : Level} (M : CartesianMulticategory ℓI ℓM ℓM')
    (ℓMᴰ ℓMᴰ' : Level)
    : Type (ℓ-suc (ℓ-max (ℓ-max ℓI ℓM) (ℓ-max ℓM' (ℓ-max ℓMᴰ ℓMᴰ')))) where
  open CartesianMulticategory M
  field
    obᴰ : ob → Type ℓMᴰ
    MHomᴰ[_][_,_] : {I : Type ℓI} {Γ : Ctx I} {A : ob}
      → MHom⟨ I ⟩[ Γ , A ]
      → ((i : I) → obᴰ (Γ i)) → obᴰ A → Type ℓMᴰ'

  infix 10 _≡[_]_

  _≡[_]_ : {I : Type ℓI} {Γ : Ctx I} {A : ob}
    {Γᴰ : (i : I) → obᴰ (Γ i)} {Aᴰ : obᴰ A} {f g : MHom⟨ I ⟩[ Γ , A ]}
    → MHomᴰ[ f ][ Γᴰ , Aᴰ ] → f ≡ g → MHomᴰ[ g ][ Γᴰ , Aᴰ ]
    → Type ℓMᴰ'
  _≡[_]_ {Γᴰ = Γᴰ} {Aᴰ = Aᴰ} fᴰ p gᴰ =
    PathP (λ k → MHomᴰ[ p k ][ Γᴰ , Aᴰ ]) fᴰ gᴰ

  field
    varᴰ : {I : Type ℓI} {Γ : Ctx I} {Γᴰ : (i : I) → obᴰ (Γ i)}
      (i : I) → MHomᴰ[ var i ][ Γᴰ , Γᴰ i ]

    _⋆ᴰ_ : {I J : Type ℓI} {Γ : Ctx I} {Δ : Ctx J} {A : ob}
      {Γᴰ : (i : I) → obᴰ (Γ i)} {Δᴰ : (j : J) → obᴰ (Δ j)} {Aᴰ : obᴰ A}
      {f : MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → MHom⟨ J ⟩[ Δ , Γ i ]}
      → MHomᴰ[ f ][ Γᴰ , Aᴰ ]
      → ((i : I) → MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
      → MHomᴰ[ f ⋆ g ][ Δᴰ , Aᴰ ]

    ⋆Varᴰ : {I J : Type ℓI} {Γ : Ctx I} {Δ : Ctx J}
      {Γᴰ : (i : I) → obᴰ (Γ i)} {Δᴰ : (j : J) → obᴰ (Δ j)}
      {g : (i : I) → MHom⟨ J ⟩[ Δ , Γ i ]}
      (i : I) (gᴰ : (i : I) → MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
      → varᴰ i ⋆ᴰ gᴰ ≡[ ⋆Var i g ] gᴰ i

    ⋆Idᴰ : {I : Type ℓI} {Γ : Ctx I} {A : ob}
      {Γᴰ : (i : I) → obᴰ (Γ i)} {Aᴰ : obᴰ A}
      {f : MHom⟨ I ⟩[ Γ , A ]} (fᴰ : MHomᴰ[ f ][ Γᴰ , Aᴰ ])
      → fᴰ ⋆ᴰ varᴰ ≡[ ⋆Id f ] fᴰ

    ⋆Assocᴰ : {I J K : Type ℓI}
      {Γ : Ctx I} {Δ : Ctx J} {Θ : Ctx K} {A : ob}
      {Γᴰ : (i : I) → obᴰ (Γ i)} {Δᴰ : (j : J) → obᴰ (Δ j)}
      {Θᴰ : (k : K) → obᴰ (Θ k)} {Aᴰ : obᴰ A}
      {f : MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → MHom⟨ J ⟩[ Δ , Γ i ]}
      {h : (j : J) → MHom⟨ K ⟩[ Θ , Δ j ]}
      (fᴰ : MHomᴰ[ f ][ Γᴰ , Aᴰ ])
      (gᴰ : (i : I) → MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
      (hᴰ : (j : J) → MHomᴰ[ h j ][ Θᴰ , Δᴰ j ])
      → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ ⋆Assoc f g h ] (fᴰ ⋆ᴰ λ i → gᴰ i ⋆ᴰ hᴰ)

    isSetMHomᴰ : {I : Type ℓI} {Γ : Ctx I} {A : ob}
      {Γᴰ : (i : I) → obᴰ (Γ i)} {Aᴰ : obᴰ A} {f : MHom⟨ I ⟩[ Γ , A ]}
      → isSet (MHomᴰ[ f ][ Γᴰ , Aᴰ ])

-- a section: an interpretation of every multimorphism by a displayed
-- one lying over it.  This is the shape of the fundamental theorem of
-- logical relations.
record Sectionᴰ
    {ℓI ℓM ℓM' ℓMᴰ ℓMᴰ' : Level} {M : CartesianMulticategory ℓI ℓM ℓM'}
    (Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ')
    : Type (ℓ-suc (ℓ-max (ℓ-max ℓI ℓM) (ℓ-max ℓM' (ℓ-max ℓMᴰ ℓMᴰ')))) where
  private
    module M = CartesianMulticategory M
    module Mᴰ = CartesianMulticategoryᴰ Mᴰ
  field
    S-ob : (A : M.ob) → Mᴰ.obᴰ A
    S-hom : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
      (f : M.MHom⟨ I ⟩[ Γ , A ])
      → Mᴰ.MHomᴰ[ f ][ (λ i → S-ob (Γ i)) , S-ob A ]
    S-var : {I : Type ℓI} {Γ : M.Ctx I} (i : I)
      → S-hom (M.var {Γ = Γ} i) ≡ Mᴰ.varᴰ i
    S-⋆ : {I J : Type ℓI} {Γ : M.Ctx I} {Δ : M.Ctx J} {A : M.ob}
      (f : M.MHom⟨ I ⟩[ Γ , A ]) (g : (i : I) → M.MHom⟨ J ⟩[ Δ , Γ i ])
      → S-hom (f M.⋆ g) ≡ S-hom f Mᴰ.⋆ᴰ (λ i → S-hom (g i))

-- THE CONSTANT displayed multicategory: another multicategory M,
-- weakened over a base C.  Its total multicategory is the product, and
-- a section of it is a multifunctor C → M.  Every displayed law is the
-- corresponding law of M, since the displayed homs do not mention the
-- base morphism at all — which is exactly why a displayed-model
-- eliminator subsumes recursion into models.
weakenᴰ : {ℓI ℓC ℓC' ℓM ℓM' : Level}
  (C : CartesianMulticategory ℓI ℓC ℓC')
  (M : CartesianMulticategory ℓI ℓM ℓM')
  → CartesianMulticategoryᴰ C ℓM ℓM'
weakenᴰ C M = W where
  module M = CartesianMulticategory M
  open CartesianMulticategoryᴰ
  W : CartesianMulticategoryᴰ C _ _
  W .obᴰ _ = M.ob
  W .MHomᴰ[_][_,_] {I} _ Γᴰ Aᴰ = M.MHom⟨ I ⟩[ Γᴰ , Aᴰ ]
  W .varᴰ i = M.var i
  W ._⋆ᴰ_ fᴰ gᴰ = fᴰ M.⋆ gᴰ
  W .⋆Varᴰ i gᴰ = M.⋆Var i gᴰ
  W .⋆Idᴰ fᴰ = M.⋆Id fᴰ
  W .⋆Assocᴰ fᴰ gᴰ hᴰ = M.⋆Assoc fᴰ gᴰ hᴰ
  W .isSetMHomᴰ = M.isSetMHom

-- The instance that matters, logical predicates over SET, is not
-- here: it is Famᴰ PROPₘ, in Multicategory.Family — a displayed
-- multicategory of families, exactly as the library's Fam builds a
-- displayed category of families over SET.
