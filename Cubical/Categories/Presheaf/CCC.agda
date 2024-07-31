{-# OPTIONS --safe --lossy-unification #-}
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
    open Bifunctor
    open NatTrans
    open UniversalElement

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

    ExpOb : ob 𝓟 → ob 𝓟 → ob 𝓟 
    ExpOb A B .F-ob c = (𝓟 [ PshProd ⟅ LiftF {ℓ'}{ℓm} ∘F (YONEDA {C = C}.F-ob c) , A ⟆b , B ]) , 𝓟 .isSetHom
    ExpOb A B .F-hom {X}{Y} Y→X M = (PshProd .Bif-hom× ((LiftF {ℓ'}{ℓm}) ∘ʳ (YONEDA {C = C} .F-hom Y→X)) (𝓟 .id)) ⋆⟨ 𝓟 ⟩ M 
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

    private 
        -- inlining this definition results in termination issues.. 
        eval : (A B : ob 𝓟) → PshProd ⟅ ExpOb B A , B ⟆b ⇒ A
        eval A B = natTrans
                (λ{x (B→A , Bx) → B→A .N-ob x (lift (C .id) , Bx)}) 
                (λ f → funExt λ{(B→A , Bx) → 
                        cong₂ (B→A .N-ob) refl (≡-× (cong lift ((C .⋆IdL f) ∙(sym (C .⋆IdR f)))) refl) 
                        ∙ funExt⁻ (B→A .N-hom f) (lift (C .id) , Bx)})
                    
    ⇒𝓟 : Exponentials 𝓟 ×𝓟
    ⇒𝓟 (A , B) .vertex = ExpOb B A
    ⇒𝓟 (A , B) .element = eval A B
    ⇒𝓟 (A , B) .universal Z .equiv-proof Z×B→A = 
        uniqueExists 
            ((natTrans (λ x Zx → natTrans (λ{y (y→x , By) → Z×B→A .N-ob y (Z .F-hom (y→x .lower) Zx , By)}) 
                λ{y}{z}z→y → funExt λ{ (y→x , By) → 
                    cong (λ h → Z×B→A .N-ob z (h , B .F-hom z→y By )) (funExt⁻ (Z .F-seq _ _ ) Zx) 
                    ∙ funExt⁻ (Z×B→A .N-hom z→y) (Z .F-hom (y→x .lower) Zx , By)  }) 
                λ{x}{y}f → funExt λ Zx → makeNatTransPath (funExt λ z → funExt λ{(y→z , Bz)→ 
                    cong (λ h → Z×B→A .N-ob z (h , Bz)) (funExt⁻ (sym (Z .F-seq f (y→z .lower))) Zx)}))) 
            ((makeNatTransPath (funExt λ x → funExt λ{(Zx , Bx) → cong (λ arg → Z×B→A .N-ob x (arg , Bx)) (funExt⁻ (Z .F-id) Zx) })))
            ((λ a' x y  → 𝓟 .isSetHom _ _  x y))
            λ Z→A^B prf → 
                makeNatTransPath (
                    funExt λ x → funExt λ Zx → 
                        makeNatTransPath (
                            funExt λ y → funExt λ {(y→x , By) → 
                                (λ i → (sym prf) i .N-ob y (Z .F-hom (y→x .lower) Zx , By)) 
                                ∙ cong (λ h → h .N-ob y (lift (C .id) , By)) (funExt⁻ (Z→A^B .N-hom (y→x .lower)) Zx ) 
                                ∙ cong (λ h → Z→A^B .N-ob x Zx .N-ob y h) (≡-×  (cong lift (C .⋆IdL _)) refl)}))

    𝓟-CCC : CartesianClosedCategory _ _ 
    𝓟-CCC = 𝓟 , ⊤𝓟 , (×𝓟 , ⇒𝓟 )
