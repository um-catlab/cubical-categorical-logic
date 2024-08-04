{-

  A simple category with families is the "categorical essence" of
  simply typed λ calculus

-}

{-# OPTIONS --safe #-}
module Syntax.SimpleCategoryWithFamilies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.SumFin
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.W.Indexed
open import Cubical.Functions.FunExtEquiv

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import Cubical.Categories.Displayed.Section.Base as Disp
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Limits.Terminal


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰ''' : Level

open Category
open Functor
open Functorᴰ
open Disp.Section
open PshSection
open UniversalElement
open UniversalElementᴰ

ProdWith : ∀ {C : Category ℓ ℓ'}
  → (P : Presheaf C ℓ'')
  → Functor C (PresheafCategory C (ℓ-max ℓ' ℓ''))
  -- laboriously filling in implicit args
ProdWith {ℓ = ℓ}{ℓ' = ℓ'}{ℓ'' = ℓ''} {C = C} P =
  funcComp {D = PresheafCategory C ℓ'} {E = PresheafCategory C (ℓ-max ℓ' ℓ'')} {C = C}
  (appR (PshProd {C = C}{ℓA = ℓ'}{ℓB = ℓ''}) P) YO

ProdWithᴰ : ∀ {C : Category ℓ ℓ'}{Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓ''}(Pᴰ : Presheafᴰ Cᴰ P ℓᴰ'')
  {Γ : C .ob}(Γᴰ : Cᴰ .Categoryᴰ.ob[_] Γ )
  → Presheafᴰ Cᴰ (ProdWith P ⟅ Γ ⟆) (ℓ-max ℓᴰ' ℓᴰ'')
ProdWithᴰ {Cᴰ = Cᴰ} Pᴰ Γᴰ = PshProdᴰ (Cᴰ [-][-, Γᴰ ]) Pᴰ
  
SimpleCategoryWithFamilies : ∀ (ℓ ℓ' ℓ'' ℓ''' : Level) → Type _
SimpleCategoryWithFamilies ℓ ℓ' ℓ'' ℓ''' =
  -- A category
  Σ[ C ∈ Category ℓ ℓ' ]
  -- "types"
  Σ[ Ty ∈ Type ℓ'' ]
  -- "terms"
  Σ[ Tm ∈ (∀ (A : Ty) → Presheaf C ℓ''') ]
  -- the category has a terminal object
  Terminal' C ×
  -- and "comprehension"
  (∀ (Γ : C .ob)(A : Ty) → UniversalElement C (ProdWith (Tm A) ⟅ Γ ⟆))

module _ (CT : SimpleCategoryWithFamilies ℓ ℓ' ℓ'' ℓ''') where
  private
    C = CT .fst
    Ty = CT .snd .fst
    Tm = CT .snd .snd .fst
    term = CT .snd .snd .snd .fst
    comprehension = CT .snd .snd .snd .snd
  SCWFᴰ : ∀ (ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰ''' : Level) → Type _
  SCWFᴰ ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰ''' =
    Σ[ Cᴰ ∈ Categoryᴰ C ℓᴰ ℓᴰ' ]
    Σ[ Tyᴰ ∈ (Ty → Type ℓᴰ'') ]
    Σ[ Tmᴰ ∈ (∀ {A : Ty} (Aᴰ : Tyᴰ A) → Presheafᴰ Cᴰ (Tm A) ℓᴰ''') ]
    LiftedTerminal Cᴰ term ×
    ∀ {Γ}{A} Γᴰ Aᴰ →
    UniversalElementᴰ Cᴰ (ProdWithᴰ (Tmᴰ Aᴰ) Γᴰ) (comprehension Γ A)

  module _ (CTᴰ : SCWFᴰ ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰ''') where
    private
      Cᴰ = CTᴰ .fst
      module Cᴰ = Categoryᴰ Cᴰ
      Tyᴰ = CTᴰ .snd .fst
      Tmᴰ = CTᴰ .snd .snd .fst
      termᴰ = CTᴰ .snd .snd .snd .fst
      comprehensionᴰ = CTᴰ .snd .snd .snd .snd
    Section : Type _
    Section =
      Σ[ sC ∈ Disp.GlobalSection Cᴰ ]
      Σ[ sTy ∈ (∀ A → Tyᴰ A ) ]
      Σ[ sTm ∈ (∀ {A} → PshSection Cᴰ (Tmᴰ (sTy A)) sC) ]
      -- these last few are probably not necessary to formulate:
      -- preserves the terminal object
      (sC .F-obᴰ (term .vertex) ≡ termᴰ .vertexᴰ)
      × (∀ Γ A →
      -- preserves the comprehension (i.e., the type and the projections, modulo the equivalence between the types)
        Σ[ pres-× ∈ (sC .F-obᴰ (comprehension Γ A .vertex) ≡ comprehensionᴰ (sC .F-obᴰ Γ) (sTy A) .vertexᴰ) ]
        (PathP (λ i → Cᴰ.Hom[ comprehension Γ A .element .fst ][ pres-× i , sC .F-obᴰ Γ ])
          (sC .F-homᴰ (comprehension Γ A .element .fst))
          (comprehensionᴰ (sC .F-obᴰ Γ) (sTy A) .elementᴰ .fst) ×
        (PathP (λ i → Tmᴰ (sTy A) .F-obᴰ (pres-× i) (comprehension Γ A .element .snd) .fst ) (sTm .F-hom (comprehension Γ A .element .snd)) (comprehensionᴰ (sC .F-obᴰ Γ) (sTy A) .elementᴰ .snd))))
