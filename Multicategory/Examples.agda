{-

  Examples of cartesian multicategories, and of displayed ones.

  Every instance here is strict, and for the same reason as SET: the
  multimorphisms are functions of an environment, so the three laws are
  η for functions.

-}
module Multicategory.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Multifunctor

private
  variable
    ℓI ℓM ℓM' ℓN ℓN' ℓW ℓ : Level

open CartesianMulticategory
open CartesianMulticategoryᴰ

-- entailment: objects are propositions, a multimorphism is a proof of
-- the conclusion from the hypotheses.  The hom-props being props, this
-- is the poset-like example — a "cartesian multicategory" here is
-- exactly a finitary (indeed infinitary) inference system closed under
-- identity and cut.
PROPₘ : ∀ {ℓI ℓ} → CartesianMulticategory ℓI (ℓ-suc ℓ) (ℓ-max ℓI ℓ)
PROPₘ .ob = hProp _
PROPₘ .MHom⟨_⟩[_,_] I Γ A = ((i : I) → ⟨ Γ i ⟩) → ⟨ A ⟩
PROPₘ .var i γ = γ i
PROPₘ ._⋆_ f g δ = f (λ i → g i δ)
PROPₘ .⋆Var i g = refl
PROPₘ .⋆Id f = refl
PROPₘ .⋆Assoc f g h = refl
PROPₘ .isSetMHom {A = A} = isSet→ (isProp→isSet (str A))

-- W-indexed families of sets, with everything pointwise: the shape of
-- a Kripke or possible-worlds model.  (A genuine presheaf model adds
-- functoriality in W; the point here is that indexing costs no
-- strictness.)
module _ {ℓI ℓW ℓ : Level} (W : Type ℓW) where
  FAMₘ : CartesianMulticategory ℓI (ℓ-max ℓW (ℓ-suc ℓ))
           (ℓ-max ℓI (ℓ-max ℓW ℓ))
  FAMₘ .ob = W → hSet ℓ
  FAMₘ .MHom⟨_⟩[_,_] I Γ A = (w : W) → ((i : I) → ⟨ Γ i w ⟩) → ⟨ A w ⟩
  FAMₘ .var i w γ = γ i
  FAMₘ ._⋆_ f g w δ = f w (λ i → g i w δ)
  FAMₘ .⋆Var i g = refl
  FAMₘ .⋆Id f = refl
  FAMₘ .⋆Assoc f g h = refl
  FAMₘ .isSetMHom {A = A} = isSetΠ λ w → isSet→ (str (A w))

-- products of cartesian multicategories.  Not strict for a general
-- pair, of course: the laws are the componentwise ones.
module _
  (M : CartesianMulticategory ℓI ℓM ℓM')
  (N : CartesianMulticategory ℓI ℓN ℓN')
  where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N

  _×ₘ_ : CartesianMulticategory ℓI (ℓ-max ℓM ℓN) (ℓ-max ℓM' ℓN')
  _×ₘ_ .ob = M.ob × N.ob
  _×ₘ_ .MHom⟨_⟩[_,_] I Γ A =
    M.MHom⟨ I ⟩[ (λ i → Γ i .fst) , A .fst ]
    × N.MHom⟨ I ⟩[ (λ i → Γ i .snd) , A .snd ]
  _×ₘ_ .var i = M.var i , N.var i
  _×ₘ_ ._⋆_ f g =
    (f .fst M.⋆ λ i → g i .fst) , (f .snd N.⋆ λ i → g i .snd)
  _×ₘ_ .⋆Var i g = ΣPathP (M.⋆Var i _ , N.⋆Var i _)
  _×ₘ_ .⋆Id f = ΣPathP (M.⋆Id _ , N.⋆Id _)
  _×ₘ_ .⋆Assoc f g h =
    ΣPathP (M.⋆Assoc _ _ _ , N.⋆Assoc _ _ _)
  _×ₘ_ .isSetMHom = isSet× M.isSetMHom N.isSetMHom

-- the multifunctor along which binary relations are predicates: it
-- takes a pair of sets to their product.  It is STRICT — both laws are
-- refl — which is what makes reindexing along it transport-free.
open Multifunctor

×F : ∀ {ℓI ℓ} → Multifunctor (SETₘ {ℓI} {ℓ} ×ₘ SETₘ {ℓI} {ℓ}) (SETₘ {ℓI} {ℓ})
×F .F-ob (A , B) = (⟨ A ⟩ × ⟨ B ⟩) , isSet× (str A) (str B)
×F .F-hom (f , g) γ = f (λ i → γ i .fst) , g (λ i → γ i .snd)
×F .F-var i = refl
×F .F-⋆ f g = refl

-- binary logical relations: displayed over SET × SET, and strict,
-- because the base is.  This is the gluing situation — a relation is
-- closed under substitution on the nose.
Relᴰ : ∀ {ℓI ℓ} → CartesianMulticategoryᴰ (SETₘ {ℓI} {ℓ} ×ₘ SETₘ {ℓI} {ℓ})
         (ℓ-suc ℓ) (ℓ-max ℓI ℓ)
Relᴰ .obᴰ (A , B) = ⟨ A ⟩ → ⟨ B ⟩ → hProp _
Relᴰ .MHomᴰ[_][_,_] {I = I} {Γ = Γ} (f , g) Γᴰ Aᴰ =
  (γ : (i : I) → ⟨ Γ i .fst ⟩) (δ : (i : I) → ⟨ Γ i .snd ⟩)
  → ((i : I) → ⟨ Γᴰ i (γ i) (δ i) ⟩)
  → ⟨ Aᴰ (f γ) (g δ) ⟩
Relᴰ .varᴰ i γ δ γᴰ = γᴰ i
Relᴰ ._⋆ᴰ_ {g = g} fᴰ gᴰ γ δ γᴰ =
  fᴰ (λ i → g i .fst γ) (λ i → g i .snd δ) (λ i → gᴰ i γ δ γᴰ)
Relᴰ .⋆Varᴰ i gᴰ = refl
Relᴰ .⋆Idᴰ fᴰ = refl
Relᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
Relᴰ .isSetMHomᴰ {Aᴰ = Aᴰ} =
  isSetΠ λ γ → isSetΠ λ δ → isSetΠ λ γᴰ → isProp→isSet (str (Aᴰ _ _))
