module HyperDoc.foo where  

open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.FinData

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

data Ty : Type where
  𝟙 Ref : Ty 
  _×ty_ _+_ : Ty → Ty → Ty

𝟚 = 𝟙 + 𝟙

data _◂_⊢_ : ℕ → Ty → Ty → Type where 
  ref : ∀ {n Γ A'} → 
    Fin n → 
    ---------------
    n ◂ Γ ⊢ Ref
  read :  ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ Ref) → 
    -------------------
    n ◂ Γ ⊢ 𝟚

  alloc : ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ 𝟚) → 
    ------------------ 
    suc n ◂ Γ ⊢ Ref

open import Cubical.Categories.Monoidal.Instances.Presheaf 