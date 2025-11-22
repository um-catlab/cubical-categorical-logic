module Cubical.Categories.Instances.FromEnriched where 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.NaturalTransformation

open Category
open EnrichedCategory
open NatTrans

module _ 
  {ℓ ℓ' ℓS : Level}
  {C : Category ℓ ℓ'} 
  (E : EnrichedCategory (PshMon.𝓟Mon {ℓS = ℓS} C) ℓS) where 

  module E = EnrichedCategory E
  module PMC = PshMon {ℓS = ℓS} C
  module M = MonoidalCategory PMC.𝓟Mon


  Enriched→Cat : Category _ _ 
  Enriched→Cat .ob = ob E
  Enriched→Cat .Hom[_,_] e₁ e₂ = PMC.𝓟 [ PMC.𝟙 , E.Hom[ e₁ , e₂ ] ]
  Enriched→Cat .id = E.id
  Enriched→Cat ._⋆_ {e₁}{e₂}{e₃} 
    f g =  dup {ℓS = ℓS} C ⋆⟨ PMC.𝓟 ⟩ f M.⊗ₕ g ⋆⟨ PMC.𝓟 ⟩ E.seq e₁ e₂ e₃  
  Enriched→Cat .⋆IdL {e₁}{e₂} f =
      makeNatTransPath (funExt λ c → funExt λ {tt* →
      λ i → sym (E.⋆IdL e₁ e₂) i .N-ob c (tt* , f .N-ob c tt*)})
  Enriched→Cat .⋆IdR {e₁}{e₂} f =
      makeNatTransPath (funExt λ c → funExt λ {tt* →
        λ i → sym (E.⋆IdR e₁ e₂) i .N-ob c (f .N-ob c tt* ,  tt*)})
  Enriched→Cat .⋆Assoc f g h =
      makeNatTransPath (funExt λ c → funExt λ{ tt* →
        λ i → E.⋆Assoc _ _ _ _ i .N-ob c
          (f .N-ob c tt* , (g .N-ob c tt* , h .N-ob c tt*))})
  Enriched→Cat .isSetHom = PMC.𝓟 .isSetHom

