module Cubical.Categories.Profunctor.Homomorphism.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR ℓQ : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where

  record ProfHom
    (R : Profunctor C D ℓR)
    (S : Profunctor C D ℓS)
         : Type (ℓ-max (ℓ-max ℓC ℓC')
                (ℓ-max (ℓ-max ℓD ℓD')
                (ℓ-max ℓR ℓS))) where
    field
      hom : ∀ c → PshHom (R ⟅ c ⟆) (S ⟅ c ⟆)
      nat : ∀ c c' (f : C [ c , c' ]) →
        NatTrans→PshHom (R ⟪ f ⟫) ⋆PshHom hom c' ≡
          hom c ⋆PshHom NatTrans→PshHom (S ⟪ f ⟫)

  open ProfHom

  isProfIso : ∀ {R : Profunctor C D ℓR} {S : Profunctor C D ℓS}
        → ProfHom R S → Type _
  isProfIso h = ∀ c → isPshIso (h .hom c)

module _
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  where

  module _
    (F : Functor B D)
    (G : Functor C E)
    (R : Profunctor B C ℓR)
    (S : Profunctor D E ℓS)
    where
    ProfHet : Type _
    ProfHet = ProfHom R (precomposeF _ (G ^opF) ∘F S ∘F F )

  module _
    (F : Functor B D)
    (R : Profunctor B C ℓR)
    (S : Profunctor D C ℓS)
    where
    ProfHetL : Type _
    ProfHetL = ProfHom R (S ∘F F)

  module _
    (F : Functor C D)
    (R : Profunctor B C ℓR)
    (S : Profunctor B D ℓS)
    where
    ProfHetR : Type _
    ProfHetR = ProfHom R (precomposeF _ (F ^opF) ∘F S)
