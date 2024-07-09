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
open import Cubical.Categories.Yoneda.More
open import Cubical.Foundations.Equiv

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

    {- something like this could work for the proofs of F-id and F-seq below
    .. but manually unpacking is much simpler
        funExt λ M → 
            cong₂ seqTrans (cong₂ (PshProd .Bif-hom×) {!   !} refl 
            ∙ PshProd .Bif-×-id) {M}{M} refl 
            ∙ (𝓟 .⋆IdL M)

    -}
    L : Functor (C ^op) (SET ℓ') → Functor (C ^op) (SET ℓm)
    L F = LiftF {ℓ'}{ℓm} ∘F F

    open Bifunctor

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

    ⇒𝓟 : Exponentials 𝓟 ×𝓟
    ⇒𝓟 (A , B) .vertex = ExpOb B A
    ⇒𝓟 (A , B) .element = 
        natTrans 
            (λ{x (B→A , B) → B→A .N-ob x (lift (C .id) , B)}) 
            (λ f → funExt λ{(B→A , B) → 
                    cong₂ (B→A .N-ob) refl (≡-× (cong lift ((C .⋆IdL f) ∙(sym (C .⋆IdR f)))) refl) 
                    ∙ funExt⁻ (B→A .N-hom f) (lift (C .id) , B)})
    ⇒𝓟 (A , B) .universal Z .equiv-proof f = 
        uniqueExists 
            (natTrans 
                (λ x Zx → 
                    natTrans (λ{y (y→x , By) → f .N-ob y (Z .F-hom (y→x .lower) Zx , By)}) 
                    λ {y}{z} g → funExt λ {(y→x , By) → {!   !}}) 
                {!   !}) 
            (makeNatTransPath (funExt λ x → funExt λ{(p , q) → cong (λ y → f .N-ob x ( y , q)) (funExt⁻ (Z .F-id) p) })) 
            (λ a' x y  → 𝓟 .isSetHom _ _  x y) 
            λ Z→A^B prf  → 
                makeNatTransPath 
                (funExt λ x → 
                    funExt λ Zx → 
                        makeNatTransPath (
                            funExt λ y → 
                                funExt λ{(y→x , By) → {!   !}}))

    𝓟-CCC : CartesianClosedCategory _ _ 
    𝓟-CCC = 𝓟 , ⊤𝓟 , (×𝓟 , ⇒𝓟 )

   