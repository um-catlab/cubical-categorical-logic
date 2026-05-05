{-# OPTIONS --lossy-unification #-}
module HyperDoc.Operational.Effects.Example where 

open import Cubical.Data.Nat 
open import Cubical.Data.FinData
open import Cubical.Data.Sum 
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation renaming (map to hmap ; rec to hrec)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Posets.Base

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.BiAlgebra
open import HyperDoc.Operational.Effects.LocalElim
open import HyperDoc.Operational.Effects.Syntax
open import HyperDoc.Operational.Effects.Logic
open import HyperDoc.Operational.Effects.Instances hiding (LC)
open import HyperDoc.Operational.Effects.Section
open import HyperDoc.Operational.Effects.Model
open import HyperDoc.Syntax

open CBPVModelSyntax


open BiAlgᴰ
open BiAlgHomᴰ
open Category
open Functor
open SectionNat
open NatTrans
-- concrete for the moment 
data Boop : Type where 
  boop : Boop

boopSig : Signature
boopSig .Signature.Op = Boop
boopSig .Signature.arity boop = 1

open Syntax boopSig
open CBPVMorphismSyntax (CL boopSig)

open LocalElimLogic 
  {boopSig}
  {Sem boopSig} 
  (SemLog boopSig) 
  (has𝟙ᴸ boopSig) 
  (has+ᴸ boopSig) 
  (hasFTyᴸ boopSig) 
open CBPVLogic (SemLog boopSig)

LR : CBPVSection
LR = LocalElim (CL boopSig)

boopⁿ : ℕ → 𝟙 ⊢c F 𝟚 → 𝟙 ⊢c F 𝟚 
boopⁿ zero M = M
boopⁿ (suc n) M = ops boop λ x → boopⁿ n M

_↦*_ : 𝟙 ⊢c F 𝟚 → 𝟙 ⊢c F 𝟚 → Type 
_↦*_ M M' = _◂_↦*_ boopSig (SynMod.bialg boopSig 𝟙 (F 𝟚)) M M'

seq↦*' : {M M' M'' : 𝟙 ⊢c F 𝟚} → M ↦* M' → M' ↦* M'' → M ↦* M'' 
seq↦*' = seq↦*  boopSig {B = (SynMod.bialg boopSig 𝟙 (F 𝟚))}

inc↦' : {M M' : 𝟙 ⊢c F 𝟚} → ⟨ BiAlg.rgraph (SynModel.bialg boopSig 𝟙 (F 𝟚)) .fst .snd M M' ⟩ → M ↦* M' 
inc↦' = inc↦ boopSig  {B = (SynMod.bialg boopSig 𝟙 (F 𝟚))}

𝓥[_] : (A : VTy) → LV.F∣ FV .F-ob  A ∣ 
𝓥[_] A = LR .fst .Section.F-obᴰ A

𝓒[_] : (B : CTy) → LC.F∣ FC .F-ob  B ∣ 
𝓒[_] B = LR .snd .fst .Section.F-obᴰ B

boop! : 𝟙 ⊢c F 𝟚 → 𝟙 ⊢c F 𝟚 
boop! M = ops boop λ {zero → M}

boop-cong : {M M' : 𝟙 ⊢c F 𝟚} → 
  M ↦* M' → 
  boop! M ↦* boop! M'
boop-cong (ref _) = ref βrefl
boop-cong {M}{M'}(tran {X = M''} M''↦M' M↦*M'') = goal where 
  have : boop! M'' ↦ boop! M' 
  have = alg-cong λ {zero → M''↦M'} 

  have' : boop! M ↦* boop! M'' 
  have' = boop-cong M↦*M''

  goal : boop! M ↦* boop! M'
  goal = tran have have'
boop-cong (isProp↦* d d₁ i) = isProp↦* (boop-cong d) (boop-cong d₁) i

theorem : ∀ (M : 𝟙 ⊢c F 𝟚) → ∥ (Σ[ n ∈ ℕ ](Σ[ V ∈ 𝟙 ⊢v 𝟚 ] (M ↦* boopⁿ n (ret' V)))) ∥₁
theorem M = hmap (goal M) have where 

  property+ :  𝟙 ⊢v 𝟚 → hProp _ 
  property+ W = 
    (∥ 
      ∥ (Σ[ V ∈ 𝟙 ⊢v 𝟙 ] (subV V σ₁ ≡ W) × Lift Unit) ∥₁ 
      ⊎ 
      ∥ (Σ[ V ∈ 𝟙 ⊢v 𝟙 ] (subV V σ₂ ≡ W) × Lift Unit) ∥₁ 
    ∥₁ , squash₁)

  have : M ∈ 𝓒[ F 𝟚 ] .fst
  have = subst (λ h → h ∈ 𝓒[ F 𝟚  ] .fst) subCId have' where 
    have' : (subC var M) ∈ 𝓒[ F 𝟚 ] .fst
    have' = LR .snd .snd .F-Car {𝟙}{F 𝟚} M var tt*

  free : (M : 𝟙 ⊢c F 𝟚) →  Type 
  free M = FreeBiPred' boopSig (λ V → subC V (ret hole)) property+ M 

  _ :  M ∈ 𝓒[ F 𝟚 ] .fst ≡ ∥ free M ∥₁
  _ = refl

  goal : (M : 𝟙 ⊢c F 𝟚) → free M → (Σ[ n ∈ ℕ ](Σ[ V ∈ 𝟙 ⊢v 𝟚 ] (M ↦* boopⁿ n (ret' V)))) 
  goal =
    FreeBiPred-Elim 
      boopSig  
      (λ V → subC V (ret hole)) 
      property+ 
      (λ M _ → (Σ[ n ∈ ℕ ](Σ[ V ∈ 𝟙 ⊢v 𝟚 ] (M ↦* boopⁿ n (ret' V))))) 
      (λ V M' M'≡retV V∈prop+ → 0 , V , subst (λ h → M' ↦* h) M'≡retV (ref βrefl)) 
      (λ {boop M' dargs mots → 
        let (n , (V , M'↦*boopⁿnretV)) = mots zero in 
          (suc n) , V ,  subst2 
              (λ h h' → ops boop h ↦* ops boop h') 
              (funExt (λ {zero → refl})) 
              (funExt (λ {zero → refl})) 
              (boop-cong M'↦*boopⁿnretV)}) 
      (λ {M}{M'} M↦M' M'∈Free (n , V , prf) → n , (V , seq↦*' M↦M' prf))
      
