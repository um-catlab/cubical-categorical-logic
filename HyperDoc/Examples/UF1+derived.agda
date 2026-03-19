
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

      -- move this
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

      vrec : {A : VTy} → 𝟙 ⊢v A → ⟨ F.FV .F-ob A ⟩ 
      vrec {A} V = F.FV .F-hom V tt

      Generators : VTy → Type
      Generators A = Cubical.Foundations.Isomorphism.isIso (vrec {A})
   
      module _ {A : VTy}(gen : Generators A) where 

        semA : Type 
        semA = ⟨ F.FV .F-ob A ⟩

        return : {A : VTy} → 𝟙 ⊢v A → 𝟙 ⊢c F A 
        return V = subC V ret

        toTerm : ALG Σ' [ FreeAlg Σ' semA , FreeCompAlg 𝟙 (F A) ]
        toTerm = FreeAlgMorphism λ a → return (gen .fst a) 

        toFree : ALG Σ' [ FreeCompAlg 𝟙 (F A) , FreeAlg Σ' semA ]
        toFree = 
          F.FO .N-ob (𝟙 , F A) 
          ⋆⟨ ALG Σ' ⟩ record { carmap = λ f → f tt ; pres = λ op args → refl } 
          ⋆⟨ ALG Σ' ⟩ FreeAlgMorphism inc

        FreeCompAlgMorphism! : {M : Alg Σ'}{f g : (ALG Σ')[ FreeCompAlg 𝟙 (F A) , M ]} → 
          (∀ a → f .carmap (return (gen .fst a)) ≡ g .carmap (return (gen .fst a))) → f ≡ g 
        FreeCompAlgMorphism! {M}{f}{g} prf = AlgHom≡ (funExt goal) where 

          -- ret*property
          DI : 𝟙 ⊢c F A → Type 
          DI = 
            UF1+.DirectImageCong' 
              ((𝟙 ⊢v A) , isSet⊢v) 
              (FreeCompAlg 𝟙 (F A)) 
              return
              (LR .fst .F-obᴰ A)

          sub : (M : 𝟙 ⊢c F A)(V : 𝟙 ⊢v A)(eq' : subC V ret ≡ M)(prf : V ∈ LR .fst .F-obᴰ A) → 
            f .carmap M ≡ g .carmap M 
          sub M V eq' _ = subst (λ h → f .carmap h ≡ g .carmap h) (cong₂ subC (gen .snd .snd V) refl ∙ eq') (prf (vrec V))

          goal : (M : 𝟙 ⊢c F A) → f .carmap M ≡ g .carmap M 
          goal M' = 
            hrec 
              (M .Carrier .snd _ _)  
              (DICong-elim _ _ _ _ 
                (λ M _ →  f .carmap M ≡ g .carmap M) 
                sub 
                (λ op args dargs mot → f .pres op args ∙ (λ i → interp M op λ x → mot x i) ∙ sym (g .pres op args)) 
                M')  
              (subst (λ h → ∥ DI h ∥₁) subCId (LR .snd .snd M' var tt*))

        Theorem : CatIso (ALG Σ')(FreeAlg Σ' semA) (FreeCompAlg 𝟙 (F A))  
        Theorem .fst = toTerm
        Theorem .snd .isIso.inv = toFree
        Theorem .snd .isIso.sec = FreeCompAlgMorphism! λ a → cong₂ subC (cong (λ h → gen .fst h) (gen .snd .fst a)) refl
        Theorem .snd .isIso.ret = FreeAlgMorphism! λ x → cong inc (gen .snd .fst x)

      finType : ℕ → VTy 
      finType zero = 𝟙
      finType (suc n) = 𝟙 + finType n

      semFinType : ℕ → Type 
      semFinType zero = Unit
      semFinType (suc n) = Unit ⊎ semFinType n

      fromFin : (n : ℕ) → ⟨ F.FV .F-ob (finType n) ⟩ → 𝟙 ⊢v finType n
      fromFin zero tt = var
      fromFin (suc n) (inl tt) = σ₁
      fromFin (suc n) (inr x) = subV (fromFin n x) σ₂

      foo : (n : ℕ) → Cubical.Foundations.Isomorphism.section vrec (fromFin n) 
      foo zero tt = refl
      foo (suc n) (inl tt) = refl
      foo (suc n) (inr x) = cong inr (foo n x)

      ClassifyFin : (n : ℕ)(V : 𝟙 ⊢v (𝟙 + (finType n))) → (V ≡ σ₁) ⊎ (Σ[ V' ∈ 𝟙 ⊢v (finType n) ] V ≡ subV V' σ₂)
      ClassifyFin n V = {!   !}

      finIso : (n : ℕ) → Generators (finType n) 
      finIso n .fst = fromFin n
      finIso n .snd .fst = foo n
      finIso zero .snd .snd V = sym (η𝟙 _) ∙ η𝟙 V
      finIso (suc n) .snd .snd V with (ClassifyFin n V)
      ... | inl x = subst (λ h → fromFin (suc n) (vrec h) ≡ h ) (sym x) refl
      ... | inr (V' , prf) = subst (λ h → fromFin (suc n) (vrec h) ≡ h ) {!   !} {! prf  !} ∙ {!   !}

      -- example for Bool (Unit ⊎ Unit)
      ClassifyBool : ∀ (V : 𝟙 ⊢v (𝟙 + 𝟙)) → (V ≡ σ₁) ⊎ (V ≡ σ₂) 
      ClassifyBool V = 
        hrec 
          (isProp⊎ 
            (isSet⊢v _ _) 
            (isSet⊢v _ _) 
            λ p q → σ₁≠σ₂ (sym p ∙ q)) 
          (λ z → z) 
          goal' where

        σ₁≠σ₂ : σ₁ {𝟙}{𝟙} ≡ σ₂ {𝟙}{𝟙} → Cubical.Data.Empty.Base.⊥
        σ₁≠σ₂ p = inl≠inr (cong have p) where 
          have : 𝟙 ⊢v (𝟙 + 𝟙) → Unit ⊎ Unit
          have V = F.FV .F-hom V tt 

          inl≠inr : {A : Type}{a : A} → inl a ≡ inr a → Cubical.Data.Empty.Base.⊥ 
          inl≠inr {A} p with ⊎Path.encode _ _ p 
          ... | ()

        conv : (Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₁ ≡ subV var V) × Lift Unit) → (V ≡ σ₁)
        conv (a , prf , tt*) = (sym (subVIdl _) ∙ sym prf ∙ cong₂ subV (sym (η𝟙 a) ∙ η𝟙 (var)) refl) ∙ subVIdl _ 

        conv' : (Σ[ a ∈ (𝟙 ⊢v 𝟙) ] (subV a σ₂ ≡ subV var V) × Lift Unit) → (V ≡ σ₂)
        conv' (a , prf , tt*) = (sym (subVIdl _) ∙ sym prf ∙ cong₂ subV (sym (η𝟙 a) ∙ η𝟙 (var)) refl) ∙ subVIdl _ 

        goal' : ∥ (V ≡ σ₁) ⊎ (V ≡ σ₂) ∥₁
        goal' = hmap (map⊎ conv conv') (merge (LR .fst .F-homᴰ V var tt*))
      
      fromBool : Unit ⊎ Unit → 𝟙 ⊢v (𝟙 + 𝟙) 
      fromBool (inl _) = σ₁
      fromBool (inr _) = σ₂ 

      boolIso : Generators (𝟙 + 𝟙) 
      boolIso .fst = fromBool
      boolIso .snd .fst (inl x) = refl
      boolIso .snd .fst (inr x) = refl
      boolIso .snd .snd V with (ClassifyBool V)
      ... | inl x = subst (λ h → fromBool (vrec h) ≡ h ) (sym x) refl
      ... | inr x = subst (λ h → fromBool (vrec h) ≡ h ) (sym x) refl

      Corollary : CatIso (ALG Σ')(FreeAlg Σ' (Unit ⊎ Unit)) (FreeCompAlg 𝟙 (F (𝟙 + 𝟙))) 
      Corollary = Theorem boolIso