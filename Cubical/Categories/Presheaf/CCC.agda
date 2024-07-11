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

    Exp₀ : ob 𝓟 → ob 𝓟 → ob C → hSet ℓm
    Exp₀ A B c = (𝓟 [ PshProd ⟅ L (YONEDA {C = C}.F-ob c) , A ⟆b , B ]) , 𝓟 .isSetHom
    
    Yo₁ : {B : ob 𝓟}{x y : ob C}(f : C [ y , x ]) → 
        𝓟 [ PshProd .Bif-ob (LiftF ∘F (C [-, y ])) B , PshProd .Bif-ob (LiftF ∘F (C [-, x ])) B ]
    Yo₁ f = (PshProd .Bif-hom× ((LiftF {ℓ'}{ℓm}) ∘ʳ (YONEDA {C = C} .F-hom f)) (𝓟 .id))

    ExpOb : ob 𝓟 → ob 𝓟 → ob 𝓟 
    ExpOb A B .F-ob c = Exp₀ A B c 
    ExpOb A B .F-hom {X}{Y} Y→X M = Yo₁ Y→X ⋆⟨ 𝓟 ⟩ M 
        --(PshProd .Bif-hom× ((LiftF {ℓ'}{ℓm}) ∘ʳ (YONEDA {C = C} .F-hom Y→X)) (𝓟 .id)) ⋆⟨ 𝓟 ⟩ M 
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

    open import Cubical.Categories.Adjoint.2Var

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
                    cong (λ foo → Z×B→A .N-ob z (foo , B .F-hom z→y By )) (funExt⁻ (Z .F-seq _ _ ) Zx) 
                    ∙ funExt⁻ (Z×B→A .N-hom z→y) (Z .F-hom (y→x .lower) Zx , By)  }) 
                λ{x}{y}f → funExt λ Zx → makeNatTransPath (funExt λ z → funExt λ{(y→z , Bz)→ 
                    cong (λ foo → Z×B→A .N-ob z (foo , Bz)) (funExt⁻ (sym (Z .F-seq f (y→z .lower))) Zx)}))) 
            ((makeNatTransPath (funExt λ x → funExt λ{(Zx , Bx) → cong (λ arg → Z×B→A .N-ob x (arg , Bx)) (funExt⁻ (Z .F-id) Zx) })))
            ((λ a' x y  → 𝓟 .isSetHom _ _  x y))
            λ Z→A^B prf → 
                makeNatTransPath (
                    funExt λ x → funExt λ Zx → 
                        makeNatTransPath (
                            funExt λ y → funExt λ {(y→x , By) → 
                                (λ i → (sym prf) i .N-ob y (Z .F-hom (y→x .lower) Zx , By)) 
                                ∙ cong (λ foo → foo .N-ob y (lift (C .id) , By)) (funExt⁻ (Z→A^B .N-hom (y→x .lower)) Zx ) 
                                ∙ cong (λ foo → Z→A^B .N-ob x Zx .N-ob y foo) (≡-×  (cong lift (C .⋆IdL _)) refl)}))
        
        {-} uniqueExists N prf₁ ((λ a' x y  → 𝓟 .isSetHom _ _  x y)) prf₂ where 
        N : Z ⇒ (ExpOb B A) 
        N = (natTrans (λ x Zx → natTrans (λ{y (y→x , By) → Z×B→A .N-ob y (Z .F-hom (y→x .lower) Zx , By)}) 
                λ{y}{z}z→y → funExt λ{ (y→x , By) → 
                    cong (λ foo → Z×B→A .N-ob z (foo , B .F-hom z→y By )) (funExt⁻ (Z .F-seq _ _ ) Zx) 
                    ∙ funExt⁻ (Z×B→A .N-hom z→y) (Z .F-hom (y→x .lower) Zx , By)  }) 
                λ{x}{y}f → funExt λ Zx → makeNatTransPath (funExt λ z → funExt λ{(y→z , Bz)→ 
                    cong (λ foo → Z×B→A .N-ob z (foo , Bz)) (funExt⁻ (sym (Z .F-seq f (y→z .lower))) Zx)}))

        prf₁ : action 𝓟 (RightAdjointLProf (Notation.×Bif 𝓟 ×𝓟) ⟅ A , B ⟆) N (eval A B) ≡ Z×B→A
        prf₁ = (makeNatTransPath (funExt λ x → funExt λ{(Zx , Bx) → cong (λ arg → Z×B→A .N-ob x (arg , Bx)) (funExt⁻ (Z .F-id) Zx) }))


        prf₂ : (a' : Z ⇒ (ExpOb B A)) → 
                action 𝓟 (RightAdjointLProf (Notation.×Bif 𝓟 ×𝓟) ⟅ A , B ⟆) a' (eval A B) ≡ Z×B→A → 
                N ≡ a'
        prf₂ Z→B^A prf = makeNatTransPath (funExt λ x → funExt λ Zx → sub x Zx) where 
            sub : (x : ob C)(Zx : Z .F-ob x .fst) → N .N-ob x Zx ≡ Z→B^A .N-ob x Zx
            sub x Zx = makeNatTransPath (funExt λ y → funExt λ {(y→x , By) → subsub y y→x By}) where 
                subsub : (y : ob C)(y→x : Lift (C [ y , x ]))(By : B .F-ob y .fst) → 
                    Z×B→A .N-ob y (Z .F-hom (y→x .lower) Zx , By) ≡ Z→B^A .N-ob x Zx .N-ob y (y→x , By)
                subsub y y→x By = goal where 

                    Zy : Z .F-ob y .fst 
                    Zy = Z .F-hom (y→x .lower) Zx

                    expy : SET ℓm [ Z .F-ob y , Exp₀ B A y ]
                    expy = Z→B^A .N-ob y

                    expx : SET ℓm [ Z .F-ob x , Exp₀ B A x ]
                    expx = Z→B^A .N-ob x
                    
                    example : expy Zy .N-ob y (lift (C .id) , By) ≡ expx Zx .N-ob y  (lift ((C .id) ⋆⟨ C ⟩ (y→x .lower)) , By)
                    example = cong (λ foo → foo .N-ob y (lift (C .id) , By)) (funExt⁻ (Z→B^A .N-hom (y→x .lower)) Zx )
                    
                    fact : Z×B→A .N-ob y (Zy , By)
                         ≡ expy Zy .N-ob y (lift (C .id) , By) 
                    fact i = (sym prf) i .N-ob y (Zy , By)
                    
                    goal : Z×B→A .N-ob y (Zy , By) 
                         ≡ expx Zx .N-ob y (y→x , By)
                    goal  = fact ∙ example ∙ cong (λ foo → Z→B^A .N-ob x Zx .N-ob y foo) (≡-×  (cong lift (C .⋆IdL _)) refl) -}

    𝓟-CCC : CartesianClosedCategory _ _ 
    𝓟-CCC = 𝓟 , ⊤𝓟 , (×𝓟 , ⇒𝓟 )

       