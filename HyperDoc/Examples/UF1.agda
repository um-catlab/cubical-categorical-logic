
{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Examples.UF1 where 

  open import Cubical.Data.Nat
  open import Cubical.Data.Sum
  open import Cubical.Data.FinData

  open import Cubical.Foundations.Prelude hiding (_∧_)
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure
  open import Cubical.Foundations.Powerset
  open import Cubical.HITs.PropositionalTruncation.Base
  open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to hrec ; map to hmap ; map2 to hmap2)
  open import Cubical.Categories.Displayed.Section.Base

  open import HyperDoc.Connectives.Connectives
  open import HyperDoc.Algebra.Algebra
  open import HyperDoc.CBPV.Model.Algebra using (AlgModel)
  open import HyperDoc.CBPV.Model.Base
  open import HyperDoc.CBPV.Syntax.UF1
  open import HyperDoc.CBPV.TypeStructure
  open import HyperDoc.Logic.Base
  open import HyperDoc.Logic.UF1 
  open import HyperDoc.Logics.SetPred
  open import HyperDoc.Logics.Algebra 

  open Alg
  open AlgHom
  open AlgHomᴰ
  open Algᴰ
  open Signature
  open Theory
  open Equation
  open Model

  module BoopExample where 

    data Boop : Type where 
      boop : Boop

    Σb : Signature
    Σb .Op = Boop
    Σb .arity boop = 1

    open Syntax Σb
    open SyntacticModel Σb using (SynModel ; FreeCompAlg)
    module Syn = CBPVModel SynModel
    open AlgLog Σb 
    open UF1
    open LocalElim Σb (AlgModel Σb) AlgLogic has⊤ unit hasPush using (M-elim-local ; LM ; pres⊤)
    open ModelSection CL AlgLogic using (CBPVSection)  
    open Section

    boop' : 𝟙 ⊢c F Ans → 𝟙 ⊢c F Ans 
    boop' M = ops 𝟙 (F Ans) boop λ {zero  → M}

    boopⁿ : ℕ → 𝟙 ⊢c F Ans → 𝟙 ⊢c F Ans 
    boopⁿ zero M = M
    boopⁿ (suc n) M = boop' (boopⁿ n M)

    property' : 𝟙  ⊢v Ans → Type 
    property' V = (V ≡ yes) ⊎ (V ≡ no)

    property : ℙ (𝟙  ⊢v Ans)
    property V = ∥ property' V ∥₁ , squash₁

    int : InterpGen (LM CL) (pres⊤ CL)
    int .InterpGen.interpAns = property
    int .InterpGen.interpYes V tt* = ∣ (inl (cong₂ subV (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subVIdl yes)) ∣₁
    int .InterpGen.interpNo V tt* = ∣ (inr (cong₂ subV (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subVIdl no)) ∣₁

    BoopLR : CBPVSection
    BoopLR  = M-elim-local CL int

    lemmaV  : ∀ (V : 𝟙 ⊢v Ans) → ∥ (V ≡ yes) ⊎ (V ≡ no) ∥₁
    lemmaV  V = subst2 (λ h h' → ∥  (h ≡ yes) ⊎ (h' ≡ no) ∥₁ ) (subVIdl _) (subVIdl _) (BoopLR .fst .F-homᴰ V var tt*)

    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Bool
    theoremV : ∥ Iso (𝟙 ⊢v Ans) Bool ∥₁
    theoremV = ∣ (
      iso 
        (λ x → {!   !}) 
        {!   !} 
        {!   !} 
        {!   !}) ∣₁
      

    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Constructions.BinProduct
    open Functor
    open Category
    open NatTrans
    open CBPVMorphism CL
    
    FV-Ans :  FV .F-ob Ans ≡ ((𝟙 ⊢v Ans) , isSet⊢v)
    FV-Ans = refl

    FC-FAns : (FC .F-ob (F Ans)) ≡ FreeCompAlg 𝟙 (F Ans)
    FC=FAns = refl

    FO-ret : FO .N-ob (Ans , F Ans) .carmap ret  ≡ λ V → subC V ret
    FO-ret = refl

    lemma : ∀ (M : 𝟙 ⊢c F Ans) → ∥  UF1.Congruence' ((𝟙 ⊢v Ans) , isSet⊢v) (FreeCompAlg 𝟙 (F Ans)) (λ V → subC V ret)  property M ∥₁
    lemma  M = 
      subst (λ h → ∥  
        UF1.Congruence' 
          (FV .F-ob Ans) 
          (FC .F-ob (F Ans)) 
          (FO .N-ob (Ans , F Ans) .carmap ret)  property h ∥₁) 
        subCId 
        (BoopLR .snd .snd M var tt*)

    theorem : ∀ (M : 𝟙 ⊢c F Ans) → Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n (subC yes ret)) ⊎ (M ≡ boopⁿ n ((subC no ret))))
    theorem = {!   !}
{-
  -- for this signature..
    data Congruence' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ B .Carrier ⟩ → Type where 
      base : (b : ⟨ B .Carrier ⟩ )(a : ⟨ A ⟩ ) → M a ≡ b → a ∈ P → Congruence' A B M P b
      step : (b : ⟨ B .Carrier ⟩ )
            (op : Op)
            (M : ⟨ B .Carrier ⟩ )
            (Congruence' A B M P M) → 
            Congruence' A B M P (boop' M)
-}

