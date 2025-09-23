module Cubical.Categories.Profunctor.Homomorphism.Unary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR ℓQ : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  -- this is "just" a natural transformation, should we take advantage of that?
  -- TODO rename to ProfHom to align with PshHom?
  record Homomorphism (R : C o-[ ℓR ]-* D)
                      (S : C o-[ ℓS ]-* D)
         : Type (ℓ-max (ℓ-max ℓC ℓC')
                (ℓ-max (ℓ-max ℓD ℓD')
                (ℓ-max ℓR ℓS))) where
    field
      hom : ∀ {c d} → R [ c , d ]R → S [ c , d ]R
      natL : ∀ {c' c d} (f : C [ c , c' ]) (r : R [ c' , d ]R)
           → hom (f ⋆l⟨ R ⟩ r ) ≡ f ⋆l⟨ S ⟩ hom r
      natR : ∀ {c d d'} (r : R [ c , d ]R) (h : D [ d , d' ])
           → hom (r ⋆r⟨ R ⟩ h) ≡ hom r ⋆r⟨ S ⟩ h

    PshHomFamily : ∀ d → PshHom (appR R d) (appR S d)
    PshHomFamily d .PshHom.N-ob c x = hom x
    PshHomFamily d .PshHom.N-hom c c' f p = natL f p

  open Homomorphism

  isIsoH : ∀ {R : C o-[ ℓR ]-* D} {S : C o-[ ℓS ]-* D}
        → Homomorphism R S → Type _
  isIsoH h = ∀ {c d} → isEquiv (h .hom {c}{d})


module _
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  where

  module _
    (F : Functor B D)
    (G : Functor C E)
    (R : B o-[ ℓR ]-* C)
    (S : D o-[ ℓS ]-* E)
    where
    Heteromorphism : Type _
    Heteromorphism = Homomorphism R (S ∘Flr (F ^opF , G))

  module _
    (F : Functor B D)
    (R : B o-[ ℓR ]-* C)
    (S : D o-[ ℓS ]-* C)
    where
    HeteromorphismL : Type _
    HeteromorphismL = Homomorphism R (S ∘Fl (F ^opF))

  module _
    (F : Functor C D)
    (R : B o-[ ℓR ]-* C)
    (S : B o-[ ℓS ]-* D)
    where
    HeteromorphismR : Type _
    HeteromorphismR = Homomorphism R (S ∘Fr F)
