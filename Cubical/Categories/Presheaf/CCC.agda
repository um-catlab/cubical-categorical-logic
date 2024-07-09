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
        𝓟 = PresheafCategory C ℓm

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
    ExpOb : ob 𝓟 → ob 𝓟 → ob 𝓟 
    ExpOb A B .F-ob c = NatTrans (PshProd ⟅ LiftF {ℓ'}{ℓm} ∘F (C [-, c ]) , A ⟆b) B , {!   !}
    ExpOb A B .F-hom {X}{Y} Y→X M = natTrans η {!   !} where 
        η : N-ob-Type (PshProd ⟅ LiftF ∘F (C [-, Y ]) , A ⟆b) B
        η c (c→Y , Ac) = M .N-ob c {! YONEDA {C = C} .F-hom   !}
    ExpOb A B .F-id = {!   !}
    ExpOb A B .F-seq = {!   !}
    open import Cubical.Foundations.Equiv

    ⇒𝓟 : Exponentials 𝓟 ×𝓟
    ⇒𝓟 (A , B) .vertex = ExpOb B A
    ⇒𝓟 (A , B) .element = natTrans (λ{c (fst₁ , snd₁) → fst₁ .N-ob c ((lift (C .id)) , snd₁)}) {!   !}
    ⇒𝓟 (A , B) .universal Z .equiv-proof f = 
        uniqueExists 
        (natTrans (λ c Zc → natTrans (λ{c' (fst₁ , snd₁) → {! f .N-ob c Zc  !}}) {!   !}) {!   !}) 
        {!   !} 
        {!   !} 
        {!   !}
    
    𝓟-CCC : CartesianClosedCategory _ _ 
    𝓟-CCC = 𝓟 , ⊤𝓟 , (×𝓟 , ⇒𝓟 )

  
