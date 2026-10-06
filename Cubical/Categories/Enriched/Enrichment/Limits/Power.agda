{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Limits.Power where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Closed
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.UniversalElement

private
  variable
    ℓV ℓV' ℓC ℓC' : Level

open Functor

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
  open import Cubical.Categories.Monoidal.Reasoning V

  module _ (v : V.ob) (X : C.ob) where
    PowerCones : Presheaf C ℓV'
    PowerCones = (V.C [ v ,-]) ∘F Hom[-,_] ℰ X

    preservesPowerCones : ∀ W
      → PshHet (Hom[_,-] ℰ W) PowerCones (reindPsh (-⊗_ V v) (V.C [-, ℰ.VE[ W , X ] ]))
    preservesPowerCones W .PshHom.N-ob U e = (V.id V.⊗ₕ e) V.⋆ ℰ.seq W U X
    preservesPowerCones W .PshHom.N-hom U' U f e =
        cong (V._⋆ ℰ.seq W U' X) split₂ʳ
      ∙ V.⋆Assoc _ _ _
      ∙ cong ((V.id V.⊗ₕ e) V.⋆_) (seq-extranatural ℰ f)
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ℰ.seq W U X) (sym serialize₂₁ ∙ serialize₁₂)
      ∙ V.⋆Assoc _ _ _

    EnrichedPower : Type _
    EnrichedPower = EnrichedUniversalElement ℰ
      (λ W → reindPsh (-⊗_ V v) (V.C [-, ℰ.VE[ W , X ] ]))
      preservesPowerCones

  PowerProf : Profunctor (V.C ^op ×C C) C ℓV'
  PowerProf .F-ob (v , X) = PowerCones v X
  PowerProf .F-hom (u , f) .NatTrans.N-ob W e = u V.⋆ (e V.⋆ Hom[_,-] ℰ W ⟪ f ⟫)
  PowerProf .F-hom (u , f) .NatTrans.N-hom g = funExt λ e →
      cong (u V.⋆_) (V.⋆Assoc _ _ _ ∙ cong (e V.⋆_) (pre-post ℰ g f) ∙ sym (V.⋆Assoc _ _ _))
    ∙ sym (V.⋆Assoc _ _ _)
  PowerProf .F-id = makeNatTransPath (funExt λ W → funExt λ e →
    V.⋆IdL _ ∙ cong (e V.⋆_) (Hom[_,-] ℰ W .F-id) ∙ V.⋆IdR _)
  PowerProf .F-seq (u , f) (u' , g) = makeNatTransPath (funExt λ W → funExt λ e →
      V.⋆Assoc _ _ _
    ∙ cong (u' V.⋆_)
        (cong (u V.⋆_) (cong (e V.⋆_) (Hom[_,-] ℰ W .F-seq f g) ∙ sym (V.⋆Assoc _ _ _))
        ∙ sym (V.⋆Assoc _ _ _)))

  module _ (pws : ∀ v X → EnrichedPower v X) where
    PowerF : Functor (V.C ^op ×C C) C
    PowerF = FunctorComprehension PowerProf (λ (v , X) → pws v X .fst)
