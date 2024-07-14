{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.General where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Data.Sigma

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open UniversalElement
open Bifunctor
open NatTrans

-- A profunctor, also called a distributor is a generalization of a
-- functor where the values are not objects of the codomain, but
-- instead presheaves
Profunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') → ∀ ℓS → Type _
Profunctor C D ℓS = Functor C (PresheafCategory D ℓS)

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') ℓS where
  PROFUNCTOR : Category _ _
  PROFUNCTOR = FUNCTOR C (PresheafCategory D ℓS) -- ChangeOfObjects 
    -- (BifunctorToParFunctor {C = C ^op}{D = D}{E = SET ℓS})
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  _[_,_]P : (P : Profunctor C D ℓR) → D .ob → C .ob → Type ℓR
  P [ d , c ]P = ⟨ (P ⟅ c ⟆) ⟅ d ⟆ ⟩

  isSetHet : (P : Profunctor C D ℓR) → ∀ d c → isSet (P [ d , c ]P)
  isSetHet P d c = ((P ⟅ c ⟆) ⟅ d ⟆) .snd

  profSeqL' : ∀ (R : Profunctor C D ℓR) {d' d c}
            (f : D [ d' , d ]) (r : R [ d , c ]P)
          → R [ d' , c ]P
  profSeqL' R f r = ((R ⟅ _ ⟆) ⟪ f ⟫) r

  infixr 15 profSeqL'
  syntax profSeqL' R f r = f ⋆l⟨ R ⟩ r

  profAssocL : ∀ (R : Profunctor C D ℓR) {d'' d' d c}
    (f' : D [ d'' , d' ])
    (f : D [ d' , d ])
    (r : R [ d , c ]P)
    → ((f' ⋆⟨ D ⟩ f) ⋆l⟨ R ⟩ r) ≡ f' ⋆l⟨ R ⟩ f ⋆l⟨ R ⟩ r
  profAssocL R f' f = funExt⁻ ((R ⟅ _ ⟆) .F-seq f f')

  profSeqR' : ∀ (R : Profunctor C D ℓR) {d c c'}
            (r : R [ d , c ]P) (g : C [ c , c' ])
          → R [ d , c' ]P
  profSeqR' R r g = ((R ⟪ g ⟫) ⟦ _ ⟧) r

  infixl 15 profSeqR'
  syntax profSeqR' R r g = r ⋆r⟨ R ⟩ g

  profAssocR : ∀ (R : Profunctor C D ℓR) {d c c' c''}
    (r : R [ d , c ]P)
    (g : C [ c , c' ])
    (g' : C [ c' , c'' ])
    → (r ⋆r⟨ R ⟩ (g ⋆⟨ C ⟩ g')) ≡ r ⋆r⟨ R ⟩ g ⋆r⟨ R ⟩ g'
  profAssocR R r g g' =
    funExt⁻ (funExt⁻ (cong N-ob (R .F-seq g g')) _) r

  profAssocLR : ∀ (R : Profunctor C D ℓR) {d' d c c'}
    → (f : D [ d' , d ]) (r : R [ d , c ]P) (g : C [ c , c' ])
    → (f ⋆l⟨ R ⟩ (r ⋆r⟨ R ⟩ g)) ≡ (f ⋆l⟨ R ⟩ r) ⋆r⟨ R ⟩ g
  profAssocLR R f r g = sym (funExt⁻ ((R ⟪ g ⟫) .N-hom f) r)

  module _ {P Q : Profunctor C D ℓS}
    (ϕ : PROFUNCTOR C D ℓS [ P , Q ])
    where
    prof-act : ∀ {x y} → P [ y , x ]P → Q [ y , x ]P
    prof-act {x}{y} = (ϕ ⟦ x ⟧) ⟦ y ⟧

    ϕ-homoL : ∀ {d' d c} (f : D [ d' , d ])(p : P [ d , c ]P)
      → prof-act (f ⋆l⟨ P ⟩ p) ≡ f ⋆l⟨ Q ⟩ (prof-act p) 
    ϕ-homoL {c = c} f p = funExt⁻ ((ϕ ⟦ c ⟧) .N-hom f) p

    ϕ-homoR : ∀ {d c c'}(p : P [ d , c ]P) (g : C [ c , c' ])
      → prof-act (p ⋆r⟨ P ⟩ g) ≡ (prof-act p) ⋆r⟨ Q ⟩ g
    ϕ-homoR {d = d} p g = funExt⁻ (funExt⁻ (cong N-ob (ϕ .N-hom g)) _) _

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (R : Profunctor C D ℓS) where

  open NatTrans
  open NatIso
  open isIsoC
  open isEquiv

  UniversalElements : Type _
  UniversalElements =
    ∀ (c : C .ob)
    → UniversalElement D (R ⟅ c ⟆)
