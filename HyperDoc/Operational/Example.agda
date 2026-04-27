module HyperDoc.Operational.Example where 


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sum 
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic

open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties
  renaming (rec to hrec ; rec2 to hrec2; map to hmap ; map2 to hmap2 ; elim to helim)

open import HyperDoc.Operational.Initial 
open import HyperDoc.Operational.Instances -- using (Sem ; CL)
open import HyperDoc.Operational.Elim
open import HyperDoc.Operational.Section
open import HyperDoc.Operational.Logic
open import HyperDoc.Operational.Model
open import HyperDoc.Connectives.Connectives

open Category
open Functor
open SectionNat
open PreorderStr
open IsPreorder
open MonFun renaming (f to fun)


open LocalElimLogic SemLog has𝟙ᴸ has+ᴸ hasFTyᴸ

LR : CBPVSection {F = CL}{ConvertLogic.Mᴰ SemLog} 
LR = LocalElim CL

𝟚 : VTy 
𝟚 = 𝟙 ⊕ 𝟙{! CL  .fst .F-hom V var  !} 

Tsys = CL .snd .fst .F-ob (F 𝟚)
_↦*_ = Tsys .fst .snd ._≤_

true : 𝟙 ⊢v 𝟚 
true = subV tt σ₁

false : 𝟙 ⊢v 𝟚 
false = subV tt σ₂

ret' : {A : VTy} → 𝟙 ⊢v A → 𝟙 ⊢c F A 
ret' V = subC V (ret hole) 

-- use recursor into Set model to define this 
lemma : (V : 𝟙 ⊢v 𝟙) → ∥ V ≡ tt ∥₁ 
lemma V = {!   !}

theorem : (M : 𝟙 ⊢c F 𝟚) → ∥ (M ↦* ret' true) ⊎ (M ↦* ret' false) ∥₁ 
theorem M = hrec squash₁ convert have where 

  what = ((L' CL LogicalToDisplayed.+TyDep.⋀ᴰ has+)
    (Reindex.pres+ᴸ CL SemLog has+ᴸ)
    (L⊤.HA.top (Reindex.pres𝟙ᴸ CL SemLog has𝟙ᴸ .fst 𝟙))
    (L⊤.HA.top (Reindex.pres𝟙ᴸ CL SemLog has𝟙ᴸ .fst 𝟙)))

  FP : ℙ ⟨ Tsys .fst ⟩
  FP = FreeARPred (𝟙 ⊢v 𝟚 , isSet⊢v) Tsys ret' what .fst

  have : M ∈ FP
  have = subst (λ h → h ∈ FP) subCId (LR .snd .snd .F-Node M var tt*)

  convert : FreeARPred' ((𝟙 ⊢v 𝟚) , isSet⊢v) Tsys ret' what M → ∥ (M ↦* ret' true) ⊎ (M ↦* ret' false) ∥₁
  convert (free _ V M≤ret'V  V∈what) = 
    hmap (λ {(_⊎_.inl x) → 
                _⊎_.inl (
                    hrec 
                      (Tsys .fst .snd .is-prop-valued _ _) 
                      (λ {(Vtt , true≡V , tt*) → 
                        hrec 
                          (Tsys .fst .snd .is-prop-valued _ _) 
                          (λ Vtt≡tt → 
                            subst 
                              (λ h → (Tsys .fst .snd ≤ M) (ret' h)) 
                              (sym true≡V ∙ cong₂ subV Vtt≡tt refl) M≤ret'V) 
                              (lemma Vtt)}) 
                      x)
           ; (_⊎_.inr x) → 
                  _⊎_.inr (
                    hrec 
                      (Tsys .fst .snd .is-prop-valued _ _) 
                      (λ {(Vtt , false≡V , tt*) → 
                        hrec 
                          (Tsys .fst .snd .is-prop-valued _ _) 
                          (λ Vtt≡tt → 
                            subst 
                              (λ h → (Tsys .fst .snd ≤ M) (ret' h)) 
                              (sym false≡V ∙ cong₂ subV Vtt≡tt refl) M≤ret'V) 
                              (lemma Vtt)}) 
                      x)}) V∈what

