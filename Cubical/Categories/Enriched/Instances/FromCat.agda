module Cubical.Categories.Enriched.Instances.FromCat where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.NaturalTransformation

open Category
open EnrichedCategory
open EnrichedFunctor
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  private
    module PM  = PshMon (SET ℓ') ℓ'
    module M = MonoidalCategory PM.𝓟Mon

  -- set indexed hom
  iHom : (c c' : ob C) → ob PM.𝓟
  iHom c c' = LiftF (ℓ-suc ℓ') ∘F ((SET _) [-, (C [ c , c' ]) , C .isSetHom ])

  id' : {c : ob C} → PM.𝓟 [ PM.𝟙 , iHom c c ]
  id' {c} .N-ob _ tt* = lift (λ _ → C .id)
  id' {c} .N-hom _ = refl

  seqE : (c₁ c₂ c₃ : ob C) → PM.𝓟 [ iHom c₁ c₂ M.⊗ iHom c₂ c₃ , iHom c₁ c₃ ]
  seqE c₁ c₂ c₃ .N-ob A (f , g) = lift λ a → f .lower a ⋆⟨ C ⟩ g .lower a
  seqE c₁ c₂ c₃ .N-hom _ = refl

  Cat→Enriched : EnrichedCategory PM.𝓟Mon ℓ
  Cat→Enriched .ob = ob C
  Cat→Enriched .Hom[_,_] = iHom
  Cat→Enriched .id = id'
  Cat→Enriched .seq = seqE
  Cat→Enriched .⋆IdL _ _ =
    makeNatTransPath (funExt λ A → funExt λ {(tt* , f) →
      cong lift (funExt λ a → sym (C .⋆IdL _))})
  Cat→Enriched .⋆IdR _ _ =
    makeNatTransPath (funExt λ A → funExt λ {(f , tt*) →
      cong lift (funExt λ a → sym (C .⋆IdR _))})
  Cat→Enriched .⋆Assoc _ _ _ _ =
    makeNatTransPath (funExt λ A → funExt λ (f , (g , h)) →
      cong lift (funExt λ a → C .⋆Assoc _ _ _))

module _ {ℓ ℓ' : Level}(C D : Category ℓ ℓ')(F : Functor C D) where
  private
    module PM  = PshMon (SET ℓ') ℓ'
    module M = MonoidalCategory PM.𝓟Mon

  enrich-fmap : {c c' : ob (Cat→Enriched  C)} →
    PM.𝓟 [ (Cat→Enriched  C) .Hom[_,_] c c' ,
      (Cat→Enriched  D) .Hom[_,_] (F .F-ob c) (F .F-ob c') ]
  enrich-fmap =
    natTrans
      (λ A P → lift (λ a → F .F-hom (P .lower a)))
      λ f → refl

  Functor→Enriched : EnrichedFunctor PM.𝓟Mon (Cat→Enriched C) (Cat→Enriched D)
  Functor→Enriched .F-ob = F .F-ob
  Functor→Enriched .F-hom = enrich-fmap
  Functor→Enriched .F-id =
    makeNatTransPath (funExt λ A → funExt λ {tt* →
      cong lift (funExt λ a → F .F-id)})
  Functor→Enriched .F-seq =
    makeNatTransPath (funExt λ A → funExt λ {(f , g) →
      cong lift (funExt λ a → sym (F .F-seq (f .lower a) (g .lower a) ))})
