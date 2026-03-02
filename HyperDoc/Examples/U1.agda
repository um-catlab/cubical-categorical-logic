{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Examples.U1 where 

  open import Cubical.Data.Nat
  open import Cubical.Data.Sum
  open import Cubical.Data.FinData

  open import Cubical.Foundations.Prelude hiding (_∧_)
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure
  open import Cubical.Foundations.Powerset
  open import Cubical.HITs.PropositionalTruncation.Base
  open import Cubical.HITs.PropositionalTruncation.Properties renaming (rec to hrec ; map to hmap ; map2 to hmap2)

  open import HyperDoc.Connectives.Connectives
  open import HyperDoc.Algebra.Algebra
  open import HyperDoc.CBPV.Model.Algebra using (AlgModel)
  open import HyperDoc.CBPV.Model.Base
  open import HyperDoc.CBPV.Syntax.U1
  open import HyperDoc.CBPV.TypeStructure
  open import HyperDoc.Logic.Base
  open import HyperDoc.Logic.U1 
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
    open SyntacticModel Σb using (SynModel)
    module Syn = CBPVModel SynModel
    open AlgLog Σb 
    open U1
    open LocalElim Σb (AlgModel Σb) AlgLogic has⊤ unit using (M-elim-local ; LM ; pres⊤)
    open ModelSection CL AlgLogic using (CBPVSection)  

    boop' : 𝟙 ⊢c Ans → 𝟙 ⊢c Ans 
    boop' M = ops 𝟙 Ans boop λ {zero  → M}

    boopⁿ : ℕ → 𝟙 ⊢c Ans → 𝟙 ⊢c Ans 
    boopⁿ zero M = M
    boopⁿ (suc n) M = boop' (boopⁿ n M)

    property' : 𝟙  ⊢c Ans → Type 
    property' M = Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n yes) ⊎ (M ≡ boopⁿ n no))

    property : ℙ (𝟙  ⊢c Ans)
    property M = ∥ property' M ∥₁ , squash₁

    closed' : (M : 𝟙 ⊢c Ans ) → M ∈ property → boop' M ∈ property 
    closed' M = hmap goal where 
      goal : property' M → property' (boop' M)
      goal (n , inl x) = (suc n) , (inl (cong boop' x))
      goal (n , inr x) = (suc n) , (inr (cong boop' x))

    closed : Cong {Σb} {Syn.O[ 𝟙 , Ans ]} property
    closed boop M = goal where 
      have : 𝟙 ⊢c Ans 
      have = M zero .fst 

      have' : have ∈ property 
      have' = M zero .snd

      dumb : ops 𝟙 Ans boop (λ i → M i .fst) ≡ boop' have
      dumb = cong (λ h → ops 𝟙 Ans boop h) (funExt λ {zero → refl})

      goal : ops 𝟙 Ans boop (λ i → M i .fst) ∈ property 
      goal = subst (λ x → x ∈ property) (sym dumb) (closed' have have')

    int : InterpGen (LM CL) (pres⊤ CL)
    int .InterpGen.interpAns .fst = property
    int .InterpGen.interpAns .snd = closed
    int .InterpGen.interpYes V tt* = 
      ∣ (0 , (inl (cong₂ subC (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subCId))) ∣₁
    int .InterpGen.interpNo V tt* = 
      ∣ (0 , (inr (cong₂ subC (sym (η𝟙 V) ∙ η𝟙 var) refl ∙ subCId))) ∣₁
    
    BoopLR : CBPVSection
    BoopLR  = M-elim-local CL int 

    theorem : ∀ (M : 𝟙 ⊢c Ans) → ∥ (Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n yes) ⊎ (M ≡ boopⁿ n no))) ∥₁ 
    theorem M = subst (λ h → h ∈ property) subCId (BoopLR .snd  .snd M var tt*)
    
  module StateExample where 

    data StateOp : Type where 
      get set0 set1 : StateOp

    -- boolean state
    ΣSt : Signature 
    ΣSt .Op = StateOp
    ΣSt .arity get = 2
    ΣSt .arity set0 = 1
    ΣSt .arity set1 = 1
    
    open Syntax ΣSt
    open SyntacticModel ΣSt using (SynModel)
    module Syn = CBPVModel SynModel
    open AlgLog ΣSt 
    open U1
    open LocalElim ΣSt (AlgModel ΣSt) AlgLogic has⊤ unit using (M-elim-local ; LM ; pres⊤)
    open ModelSection CL AlgLogic using (CBPVSection)  

    Free : Type
    Free = FreeOn ΣSt (𝟙 ⊢c Ans)

    property' : 𝟙  ⊢c Ans → Type 
    property' M = {!   !}

    property : ℙ (𝟙  ⊢c Ans)
    property M = ∥ property' M ∥₁ , squash₁

    closed : Cong {ΣSt} {Syn.O[ 𝟙 , Ans ]} property
    closed = {!   !}

    yes∈ : yes ∈ property 
    yes∈ = {!   !}

    no∈ : no ∈ property 
    no∈ = {!   !}

    int : InterpGen (LM CL) (pres⊤ CL)
    int .InterpGen.interpAns .fst = property
    int .InterpGen.interpAns .snd = closed
    int .InterpGen.interpYes V tt* =  {!   !}
    int .InterpGen.interpNo V tt* = {!   !}

    StateLR : CBPVSection 
    StateLR = M-elim-local CL int 

