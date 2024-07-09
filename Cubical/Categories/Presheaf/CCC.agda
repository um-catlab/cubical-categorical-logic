{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.CCC where

open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Functors.Constant
open import Cubical.Data.Unit
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions 
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Data.Sigma
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.CartesianClosed.Base

private
    variable
        ℓ ℓ' ℓS : Level
    
module _ {C : Category ℓ ℓ'} {ℓS : Level} where
    private
        ℓm = ℓ-max ℓ' (ℓ-max ℓ ℓS)
        𝓟 = PresheafCategory C (ℓm)

    open Category
    open Functor
    open BinProduct
    open NatTrans
    open UniversalElement

    -- use definitions from Cubical.Categories.Limits.Terminal.More ?
    ⊤𝓟 : Terminal 𝓟 
    ⊤𝓟 = Constant _ _ (Unit* , isSetUnit*) , 
        λ _ → natTrans (λ _ _  → tt*) (λ _  → refl) , 
             λ _  → makeNatTransPath (funExt λ _ →  funExt λ _  → isPropUnit* _ _)
        
    ×𝓟 : BinProducts 𝓟
    ×𝓟 A B .binProdOb = PshProd ⟅ A , B ⟆b
    ×𝓟 A B .binProdPr₁ = natTrans (λ _ (a , _) → a) λ _ → funExt λ{_ → refl}
    ×𝓟 A B .binProdPr₂ = natTrans (λ _ (_ , b) → b) λ _ → funExt λ{_ → refl}
    ×𝓟 A B .univProp f g = 
        uniqueExists 
            ((natTrans (λ x z → f .N-ob x z , g .N-ob x z) (λ h  → funExt λ z → ≡-× (funExt⁻ (f .N-hom h) z) (funExt⁻ (g .N-hom h) z) ))) 
            ((makeNatTransPath refl) , (makeNatTransPath refl)) 
            (λ a → isProp× (isSetNatTrans _ _) (isSetNatTrans _ _))
            λ _ (prf₁ , prf₂) → makeNatTransPath λ i x x₁ → sym (prf₁) i .N-ob x x₁ , sym (prf₂) i .N-ob x x₁
    
{-
  isUniversal : (vertex : C .ob) (element : (P ⟅ vertex ⟆) .fst)
              → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  isUniversal vertex element =
    ∀ A → isEquiv λ (f : C [ A , vertex ]) → element ∘ᴾ⟨ C , P ⟩ f

  isPropIsUniversal : ∀ vertex element → isProp (isUniversal vertex element)
  isPropIsUniversal vertex element = isPropΠ (λ _ → isPropIsEquiv _)

  record UniversalElement : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp) where
    field
      vertex : C .ob
      element : (P ⟅ vertex ⟆) .fst
      universal : isUniversal vertex element 
-}
    open import Cubical.Categories.Yoneda.More
    --C [-, ? ] : Functor C^op SET ℓ'
    -- LiftF : Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
    -- LiftF  ∘F (C [-, c ])
    --  LiftF {ℓ'}{ℓm} ∘F (YONEDA .F-ob c )
    L : Functor (C ^op) (SET ℓ') → Functor (C ^op) (SET ℓm)
    L F = LiftF {ℓ'}{ℓm} ∘F F


    open import Cubical.Categories.Bifunctor.Redundant
    open Bifunctor

    {- something like this could work for the proofs of F-id and F-seq below
    .. but manually unpacking is much simpler
        funExt λ M → 
            cong₂ seqTrans (cong₂ (PshProd .Bif-hom×) {!   !} refl 
            ∙ PshProd .Bif-×-id) {M}{M} refl 
            ∙ (𝓟 .⋆IdL M)

    -}

    ExpOb : ob 𝓟 → ob 𝓟 → ob 𝓟 
    ExpOb A B .F-ob c = (𝓟 [ PshProd ⟅ L (YONEDA {C = C}.F-ob c) , A ⟆b , B ]) , 𝓟 .isSetHom  
    ExpOb A B .F-hom {X}{Y} Y→X M = 
        (PshProd .Bif-hom× ((LiftF {ℓ'}{ℓm}) ∘ʳ (YONEDA {C = C} .F-hom Y→X)) (𝓟 .id)) ⋆⟨ 𝓟 ⟩ M 
    ExpOb A B .F-id =        
        funExt λ M → 
            makeNatTransPath (
                funExt λ Z → 
                    funExt λ{ _ → 
                        cong (M .N-ob Z) (≡-× (cong lift (C .⋆IdR _)) refl)})
    ExpOb A B .F-seq f g = 
        funExt λ M → 
            makeNatTransPath (
                funExt λ Z → 
                    funExt λ{ _ → 
                        cong (M .N-ob Z) (≡-× (cong lift (sym (C .⋆Assoc _ _ _ ))) refl)})

{-     
    open import Cubical.Foundations.Equiv

    
        type checking time explodes
    ⇒𝓟 : Exponentials 𝓟 ×𝓟
    ⇒𝓟 (A , B) .vertex = ExpOb B A
    ⇒𝓟 (A , B) .element = natTrans (λ{c (nt , Bc) → nt .N-ob c ((lift (C .id)) , Bc)}) {!   !}
    ⇒𝓟 (A , B) .universal C .equiv-proof f = 
        uniqueExists 
        (natTrans (λ x Cx → natTrans (λ{y (y→x , By) → f .N-ob y (C .F-hom (y→x .lower) Cx , By)}) {!   !}) {!   !}) 
        (makeNatTransPath (funExt λ x → funExt λ{ (Cx , Bx) → congS (f .N-ob x) ? }))
        {!   !} 
        {!   !}
    -}
    
    𝓟-CCC : CartesianClosedCategory _ _ 
    𝓟-CCC = 𝓟 , ⊤𝓟 , (×𝓟 , {!   !} )--⇒𝓟 )

  
   