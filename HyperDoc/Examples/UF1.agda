
{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Examples.UF1 where 

  open import Cubical.Data.Bool
  open import Cubical.Data.Empty.Base renaming (elim to elim⊥)
  open import Cubical.Data.FinData
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
  open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎)
  open import Cubical.Relation.Nullary.Base

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
  open import HyperDoc.CBPV.Syntax.UF1
  open import HyperDoc.CBPV.TypeStructure
  open import HyperDoc.Connectives.Connectives
  open import HyperDoc.Lib
  open import HyperDoc.Logic.Base
  open import HyperDoc.Logic.UF1
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
  open Equation

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
    open Model Σb 
    open LocalElim Σb AlgModel AlgLogic has⊤ hasV𝟙 hasPush using (M-elim-local ; LM ; pres⊤)
    open ModelSection CL AlgLogic using (CBPVSection)  
    open Section
    open CBPVMorphism CL

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

    return : 𝟙 ⊢v Ans → 𝟙 ⊢c F Ans
    return V = subC V ret

    open Recursor AlgModel using (M-rec ; InterpGen)
    open Recursor.InterpGen

    int'  : Recursor.InterpGen AlgModel hasV𝟙 hasUTy hasFTy 
    int' .interp-Ans = Bool , isSetBool
    int' .interp-yes tt = true
    int' .interp-no tt = false

    module F = CBPVMorphism (M-rec hasV𝟙 hasUTy hasFTy int')

    yes≠no : ¬ yes ≡ no
    yes≠no p = true≢false (cong have p) where 
      have : 𝟙 ⊢v Ans → Bool
      have V = F.FV .F-hom V tt

    retyes≠retno :  ¬ (return yes ≡ return no)
    retyes≠retno p = true≢false (lem (cong have p)) where 

      have : 𝟙 ⊢c F Ans → FreeOn Σb Bool
      have M = F.FO .N-ob (𝟙 , F Ans) .carmap M tt

      lem : inc true ≡ inc false → true ≡ false 
      lem p = cong (λ {(inc x) → x
                     ; (ops o x) → true}) p


    ClosedVal : ∥ Iso (𝟙 ⊢v Ans) Bool ∥₁
    ClosedVal = 
      hmap ClosedVal' 
      (choice 
        (λ _ → isProp⊎ (isSet⊢v _ _) (isSet⊢v _ _) 
        λ p q → yes≠no (sym p ∙ q)) 
        isYesOrNo) where 

        isYesOrNo : ∀ (V : 𝟙 ⊢v Ans) → ∥ (V ≡ yes) ⊎ (V ≡ no) ∥₁
        isYesOrNo V = 
          subst2 
            (λ h h' → ∥  (h ≡ yes) ⊎ (h' ≡ no) ∥₁ ) 
            (subVIdl _) 
            (subVIdl _) 
            (BoopLR .fst .F-homᴰ V var tt*)

        ClosedVal' : (asm  : ∀ (V : 𝟙 ⊢v Ans) → (V ≡ yes) ⊎ (V ≡ no)) → Iso (𝟙 ⊢v Ans) Bool
        ClosedVal' asm .fun V = rec⊎  (λ _ → true) (λ _ → false) (asm V)
        ClosedVal' asm .inv b = if b then yes else no
        ClosedVal' asm .sec false with (asm no)
        ... | inl x = elim⊥  {A = λ _ → true ≡ false} (yes≠no (sym x))
        ... | inr x = refl
        ClosedVal' asm .sec true with (asm yes)
        ... | inl x = refl
        ... | inr x = elim⊥  {A = λ _ → false ≡ true} (yes≠no x)
        ClosedVal' asm .Iso.ret V with (asm V) 
        ... | inl x = sym x
        ... | inr x = sym x

    ClosedComp :  
      (M : 𝟙 ⊢c F Ans) → 
      ∥ Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n (return yes)) ⊎ (M ≡ boopⁿ n (return no))) ∥₁
    ClosedComp M = 
      hmap 
        (ClosedComp' M)  
        (subst (λ h →  ∥  DI h ∥₁) 
        subCId 
        have) where 

      DI :  𝟙 ⊢c F Ans → Type 
      DI = 
        UF1.DirectImageCong' 
          ((𝟙 ⊢v Ans) , isSet⊢v) 
          (FreeCompAlg 𝟙 (F Ans)) 
          (λ V → subC V ret)  
          property

      ClosedComp' : 
        (M : 𝟙 ⊢c F Ans) → 
        DI M  → 
        Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n (return yes)) ⊎ (M ≡ boopⁿ n (return no)))
      ClosedComp' = 
        DICong-elim _ _ _ _ 
          (λ M _ → Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n (return yes)) ⊎ (M ≡ boopⁿ n (return no)))) 
          (λ M V eq' prf → 0 , 
            hrec 
              (isProp⊎ (isSet⊢c _ _) (isSet⊢c _ _) (λ p q → retyes≠retno (sym p ∙ q))) 
              (map⊎ 
                (λ p → sym eq' ∙ cong₂ subC p refl) 
                (λ p → sym eq' ∙ cong₂ subC p refl)) 
              prf) 
          λ {boop args dargs Hind → 
            let (n , prf' ) = Hind zero in 
              (suc n) , 
              (map⊎ 
                ((λ p → cong (λ h → ops 𝟙 (F Ans) boop h) (funExt λ {zero → p}))) 
                ((λ p → cong (λ h → ops 𝟙 (F Ans) boop h) (funExt λ {zero → p}))) 
                prf') }

      have : ∥  DI (subC var M)  ∥₁
      have = BoopLR .snd .snd M var tt*

{-

    thing : (asm : (M : 𝟙 ⊢c F Ans) → Σ[ n ∈ ℕ ] ((M ≡ boopⁿ n (return yes)) ⊎ (M ≡ boopⁿ n (return no)))) → 
      Iso (𝟙 ⊢c F Ans) (ℕ × Bool) -- or  (FreeOn Σb Bool)
    thing asm .fun M = let (n , prf) = (asm M) in n , rec⊎ (λ _ → true) (λ _ → false) prf
    thing asm .inv (n , b) = if b then boopⁿ n (return yes) else boopⁿ n (return no)
    thing asm .sec = {!   !} -- this bit is more annoying
    thing asm .retract M with (asm M) 
    ... | n , inl x = sym x
    ... | n , inr x = sym x
-}

