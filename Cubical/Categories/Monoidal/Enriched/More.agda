module Cubical.Categories.Monoidal.Enriched.More where 

open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor

-- NOTE: The following should be added to 
-- Cubical.Categories.Monoidal.Enriched                        
module _ {ℓV ℓV'  : Level} (V : MonoidalCategory ℓV ℓV') where 
  open MonoidalCategory V
    renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_; ⋆Assoc to VAssoc)

  record EnrichedFunctor {ℓE ℓD : Level}(E : EnrichedCategory V ℓE)(D : EnrichedCategory V ℓD) : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD)) where 
    private module E = EnrichedCategory E 
    private module D = EnrichedCategory D 
    field 
      F₀ : E.ob → D.ob
      F₁ : {X Y : E.ob} → V[ E.Hom[ X , Y ] , D.Hom[ F₀ X , F₀ Y ] ]
      Fid : {X : E.ob} → (E.id {X} ⋆V F₁ {X} {X}) ≡ D.id {F₀ X}
      Fseq : {X Y Z : E.ob} → (F₁ {X} {Y} ⊗ₕ F₁ {Y} {Z}) ⋆V D.seq (F₀ X) (F₀ Y) (F₀ Z) ≡ E.seq X Y Z ⋆V F₁ {X} {Z} 


  open EnrichedFunctor
  open EnrichedCategory
  open Functor
  ecomp : {ℓ : Level}{C D E : EnrichedCategory V ℓ} → EnrichedFunctor C D → EnrichedFunctor D E → EnrichedFunctor C E 
  ecomp  F G .F₀ c = F₀ G (F₀ F c)
  ecomp  F G .F₁ = F₁ F ⋆V F₁ G
  ecomp  {C} F G .Fid = (sym (VAssoc _ _ _) ∙ cong (λ h → h ⋆V F₁ G) (F .Fid) ) ∙ G .Fid
  ecomp  {C} F G .Fseq = 
    ((((cong₂ _⋆V_ (─⊗─ .F-seq _ _) refl ∙ VAssoc _ _ _ ) 
    ∙ cong (λ h → (F₁ F ⊗ₕ F₁ F) ⋆V h ) (G .Fseq)) 
    ∙ sym (VAssoc _ _ _)) 
    ∙ cong (λ h → h ⋆V F₁ G) (F .Fseq)) 
    ∙ VAssoc _ _ _  


module _ 
    {ℓV ℓV'  : Level} 
    {V : MonoidalCategory ℓV ℓV'}
    {ℓE : Level} 
    {ℓD : Level}
    {𝓒 : EnrichedCategory V ℓE}
    {𝓓 : EnrichedCategory V ℓD}
    (F G : EnrichedFunctor V  𝓒 𝓓 ) where 
    
    open EnrichedCategory 𝓒 
      renaming (ob to 𝓒ob ; Hom[_,_] to 𝓒[_,_])
    open EnrichedCategory 𝓓 
      renaming (Hom[_,_] to 𝓓[_,_] ; seq to 𝓓seq)
    open MonoidalCategory V
      renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_ ; unit to Vunit)
    open EnrichedFunctor F 
    open EnrichedFunctor G 
      renaming (F₀ to G₀ ; F₁ to G₁)

    record EnrichedNatTrans : Type ((ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD))) where 
      field 
        E-N-ob : ∀ (c : 𝓒ob) → V[ Vunit , 𝓓[ F₀ c , G₀ c ] ]
        E-N-hom : 
          ∀ (c c' : 𝓒ob) → 
            (ρ⁻¹⟨ 𝓒[ c , c' ] ⟩ ⋆V ((F₁ ⊗ₕ E-N-ob c') ⋆V 𝓓seq _ _ _)) 
              ≡ 
            (η⁻¹⟨ 𝓒[ c , c' ] ⟩ ⋆V (E-N-ob c ⊗ₕ G₁ ⋆V 𝓓seq _ _ _))

  