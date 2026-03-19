
  {-# OPTIONS --type-in-type #-}
  -- fix level issues
  -- reorder imports, etc

  module HyperDoc.Examples.UF1+derived where 
    open import Agda.Builtin.Cubical.Equiv

    open import Cubical.Data.Bool
    open import Cubical.Data.Empty.Base renaming (elim to elim⊥)
    open import Cubical.Data.FinData
    open import Cubical.Data.Nat hiding (_+_)
    open import Cubical.Data.Sigma
    open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎)
    open import Cubical.Functions.Embedding
    open import Cubical.Functions.Surjection
    open import Cubical.Relation.Nullary.Base

    open import Cubical.Foundations.Equiv
    open import Cubical.Foundations.HLevels
    open import Cubical.Foundations.Isomorphism hiding (section ; retract)
    open import Cubical.Foundations.Powerset
    open import Cubical.Foundations.Prelude hiding (_∧_)
    open import Cubical.Foundations.Structure
    open import Cubical.HITs.PropositionalTruncation.Base
    open import Cubical.HITs.PropositionalTruncation.Properties
      renaming (rec to hrec ; map to hmap ; map2 to hmap2 ; elim to helim)

    open import Cubical.Categories.Category
    open import Cubical.Categories.Displayed.Section.Base
    open import Cubical.Categories.Functor
    open import Cubical.Categories.NaturalTransformation

    open import HyperDoc.Algebra.Algebra hiding (Model)
    open import HyperDoc.CBPV.Model.Algebra
    open import HyperDoc.CBPV.Model.Base
    open import HyperDoc.CBPV.Syntax.UF1+derived
    open import HyperDoc.CBPV.TypeStructure
    open import HyperDoc.Connectives.Connectives
    open import HyperDoc.Lib
    open import HyperDoc.Logic.Base
    open import HyperDoc.Logic.UF1+derived
    open import HyperDoc.Logics.Algebra
    open import HyperDoc.Logics.SetPred

    open Alg
    open AlgHom
    open AlgHomᴰ
    open Algᴰ
    open Category
    open Functor
    open Iso renaming (ret to retract)
    open NatTrans
    open Signature
    open Theory

    module foo (Σ' : Signature) where 


      open Syntax Σ'
      open SyntacticModel Σ' using (SynModel ; FreeCompAlg)
      module Syn = CBPVModel SynModel
      open AlgLog Σ'
      open UF1+
      open Model Σ'
      open import HyperDoc.Logic.Structure 
      open VPush AlgLogic

      open import Cubical.Functions.Logic hiding(inl ; inr)
      open import Cubical.Categories.Instances.Preorders.Monotone
      open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
      open import Cubical.Relation.Binary.Preorder
      open PreorderStr

      hasVPush : HasVPush
      hasVPush {A}{A'} f .fst .MonFun.f P a' = ∥ (Σ[ a ∈ ⟨ A ⟩  ]  (f a ≡ a') × ⟨ P a ⟩) ∥ₚ
      hasVPush {A}{A'} f .fst .MonFun.isMon x≤y a' = hmap λ z → z .fst , z .snd .fst , x≤y (z .fst) (z .snd .snd)
      hasVPush f .snd ._⊣_.adjIff {P}{Q} .fun prf a Pa = prf (f a) ∣ (a , (refl , Pa)) ∣₁
      hasVPush f .snd ._⊣_.adjIff {P}{Q} .inv prf a' = hrec (Q a' .snd) λ {(a , eqn , Pa) → subst (λ h → h ∈ Q) eqn (prf a  Pa)}
      hasVPush {A}{A'} f .snd ._⊣_.adjIff {P}{Q} .sec b = pred  A .fst .snd .is-prop-valued P (Pred .F-hom {A'}{A} f $ Q)  _ _ 
      hasVPush {A}{A'} f .snd ._⊣_.adjIff {P}{Q} .retract a = pred  A' .fst .snd .is-prop-valued (λ x → _ , squash₁) Q   _ _

      open LocalElim Σ' AlgModel AlgLogic has⊤ has∨ hasV𝟙 hasPush hasVPush 
      open ModelSection CL AlgLogic using (CBPVSection)  
      open Section
      open CBPVMorphism CL

      LR : CBPVSection
      LR  = M-elim-local CL

      open Recursor AlgModel using (M-rec) 

      module F = CBPVMorphism (M-rec hasV𝟙 hasUTy hasFTy hasO+)

      toFree : ALG Σ' [ FreeCompAlg 𝟙 (F(𝟙 + 𝟙)) , FreeAlg Σ' Bool ]
      toFree = 
        F.FO .N-ob (𝟙 , F(𝟙 + 𝟙)) 
        ⋆⟨ ALG Σ' ⟩ record { carmap = λ f → f tt ; pres = λ op args → refl } 
        ⋆⟨ ALG Σ' ⟩ FreeAlgMorphism λ { (inl x) → inc true ; (inr x) → inc false}

      toTerm : ALG Σ' [ FreeAlg Σ' Bool , FreeCompAlg 𝟙 (F (𝟙 + 𝟙)) ]
      toTerm = FreeAlgMorphism λ { false → subC σ₂ ret
                                  ; true → subC σ₁ ret}

      property : 𝟙 ⊢v (𝟙 + 𝟙) → hProp  _ 
      property V =   
            ∥ 
              ∥ Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₁ ≡ V) × Lift Unit ∥₁ 
                ⊎ 
              ∥ Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₂ ≡ V) × Lift Unit ∥₁ 
            ∥₁ , squash₁

      -- ret*property
      DI :  𝟙 ⊢c F (𝟙 + 𝟙) → Type 
      DI = 
        UF1+.DirectImageCong' 
          ((𝟙 ⊢v (𝟙 + 𝟙)) , isSet⊢v) 
          (FreeCompAlg 𝟙 (F (𝟙 + 𝟙))) 
          (λ V → subC V ret)  
          property

      boolToTerm : Bool → 𝟙 ⊢c F (𝟙 + 𝟙)
      boolToTerm false = subC σ₂ ret
      boolToTerm true = subC σ₁ ret

      σ₁≠σ₂ : σ₁ {𝟙}{𝟙} ≡ σ₂ {𝟙}{𝟙} → Cubical.Data.Empty.Base.⊥
      σ₁≠σ₂ p = inl≠inr (cong have p) where 
        have : 𝟙 ⊢v (𝟙 + 𝟙) → Unit ⊎ Unit
        have V = F.FV .F-hom V tt 

        inl≠inr : {A : Type}{a : A} → inl a ≡ inr a → Cubical.Data.Empty.Base.⊥ 
        inl≠inr {A} p with ⊎Path.encode _ _ p 
        ... | ()

      ClosedVal : ∀ (V : 𝟙 ⊢v (𝟙 + 𝟙)) → (V ≡ σ₁) ⊎ (V ≡ σ₂) 
      ClosedVal V = 
        hrec 
          (isProp⊎ 
            (isSet⊢v _ _) 
            (isSet⊢v _ _) 
            λ p q → σ₁≠σ₂ (sym p ∙ q)) 
          (λ z → z) 
          goal' where

        conv : (Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₁ ≡ subV var V) × Lift Unit) → (V ≡ σ₁)
        conv (a , prf , tt*) = (sym (subVIdl _) ∙ sym prf ∙ cong₂ subV (sym (η𝟙 a) ∙ η𝟙 (var)) refl) ∙ subVIdl _ 

        conv' : (Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₂ ≡ subV var V) × Lift Unit) → (V ≡ σ₂)
        conv' (a , prf , tt*) = (sym (subVIdl _) ∙ sym prf ∙ cong₂ subV (sym (η𝟙 a) ∙ η𝟙 (var)) refl) ∙ subVIdl _ 

        goal' : ∥ (V ≡ σ₁) ⊎ (V ≡ σ₂) ∥₁
        goal' = hmap (map⊎ conv conv') (merge (LR .fst .F-homᴰ V var tt*))

      FreeCompAlgMorphism! : {M : Alg Σ'}{f g : (ALG Σ')[ FreeCompAlg 𝟙 (F (𝟙 + 𝟙)) , M ]} → 
        (∀ x → f .carmap (boolToTerm x) ≡ g .carmap (boolToTerm x)) → f ≡ g 
      FreeCompAlgMorphism! {M}{f}{g} prf = AlgHom≡ (funExt goal) where 

        sub : (M : 𝟙 ⊢c F( 𝟙 + 𝟙))(V : 𝟙 ⊢v (𝟙 + 𝟙))(eq' : subC V ret ≡ M)(prf : V ∈ property) → 
          f .carmap M ≡ g .carmap M 
        sub M V eq' _ with (ClosedVal V)
        ... | inl x = subst (λ h → f .carmap h ≡ g .carmap h) (cong₂ subC (sym x) refl ∙ eq') (prf true)
        ... | inr x = subst (λ h → f .carmap h ≡ g .carmap h) (cong₂ subC (sym x) refl ∙ eq') (prf false) 
        
        goal : (M : 𝟙 ⊢c F( 𝟙 + 𝟙)) → f .carmap M ≡ g .carmap M 
        goal M' = hrec (M .Carrier .snd _ _)  (
          DICong-elim _ _ _ _ 
            (λ M _ →  f .carmap M ≡ g .carmap M) 
            sub
            (λ op args dargs mot → f .pres op args ∙ (λ i → interp M op λ x → mot x i) ∙ sym (g .pres op args)) 
            M') 
          ((subst (λ h → ∥ DI h ∥₁) subCId (LR .snd .snd M' var tt*)))


      Theorem : CatIso (ALG Σ')(FreeAlg Σ' Bool) (FreeCompAlg 𝟙 (F (𝟙 + 𝟙)))  
      Theorem .fst = toTerm
      Theorem .snd .isIso.inv = toFree
      Theorem .snd .isIso.sec = FreeCompAlgMorphism! λ {false → refl
                                                  ; true → refl}
      Theorem .snd .isIso.ret = FreeAlgMorphism! λ {false → refl
                                              ; true → refl} 

{-                                     

      toTerm' : FreeOn Σ' Bool → 𝟙 ⊢c F(𝟙 + 𝟙) 
      toTerm' = toTerm .carmap

      toTermIsSurjection : isSurjection toTerm' 
      toTermIsSurjection M = hrec squash₁ (λ d → 
        DICong-elim _ _ _ _ 
          (λ M _ → ∃[ x ∈ FreeOn Σ' Bool ] toTerm' x ≡ M ) 
          (λ M V eq' p → hmap (λ { (inl (_ , prf , _)) → (inc true) , (cong₂ subC ((sym (subVIdl _) ∙ cong₂ subV (sym (η𝟙 _) ∙ η𝟙 _) refl) ∙ prf) refl ∙ eq')
                                  ; (inr (_ , prf , _)) → (inc false) , ((cong₂ subC ((sym (subVIdl _) ∙ cong₂ subV (sym (η𝟙 _) ∙ η𝟙 _) refl) ∙ prf) refl ∙ eq'))}) (merge p) )
          (λ op args dargs mots → recFin squash₁ (λ ih → ∣ ((ops op (λ x → ih x .fst)) , (cong (λ h → ops 𝟙 (F (𝟙 + 𝟙)) op h) (funExt (λ x → ih x .snd)))) ∣₁) mots) 
          M 
          d) 
          (subst (λ h → ∥ DI h ∥₁) subCId (LR .snd .snd M var tt*))
      
      lem : {x : FreeOn Σ' Bool} → toFree .carmap (toTerm' x) ≡ x
      lem {inc false} = refl
      lem {inc true} = refl
      lem {ops op args} i = ops op λ x → lem {args x} i

      toTermIsEmbedding : isEmbedding toTerm' 
      toTermIsEmbedding  = injEmbedding isSet⊢c goal where 
        goal : {w x : FreeOn Σ' Bool} → toTerm' w ≡ toTerm' x → w ≡ x 
        goal {w}{x} prf = sym (lem{w}) ∙ cong (λ h → toFree .carmap h) prf  ∙ lem{x}

      Theorem' : Iso (FreeOn Σ' Bool) (𝟙 ⊢c F (𝟙 + 𝟙)) 
      Theorem' = 
        equivToIso (
          toTerm' , 
          isEmbedding×isSurjection→isEquiv 
            (toTermIsEmbedding  , toTermIsSurjection))

-}