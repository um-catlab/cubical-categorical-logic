{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Free.Category.GuardedFixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)
import Cubical.HITs.SetTruncation as Trunc

open import Cubical.Categories.Category.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.FixedPoint
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTransᴰ
open PshIso
open Section
open UniversalElement

data Ob : Type where
  [RetBool] [1] : Ob

data Exp : Ob → Ob → Type where
  idₑ : ∀ {A} → Exp A A
  _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
  ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
  ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
  ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
          → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
  isSetExp : ∀ {A B} → isSet (Exp A B)

  -- [1] is terminal
  []ₑ : ∀ {A} → Exp A [1]
  1ηₑ : ∀ {A}{M : Exp A [1]} → M ≡ []ₑ

  -- [RetBool] contains constants
  [tru] [fls] : Exp [1] [RetBool]
  -- [ifthen_else_] : ∀ {B}
  --   → Exp [1] B
  --   → Exp [1] B
  --   → Exp [RetBool] B

  -- delay/step/pay/fuel
  [δ] : ∀ {B} → Exp B B
  -- [ite-δ] : ∀ {B} {M1 M2 : Exp [1] B}
  --   → [δ] ⋆ₑ [ifthen M1 else M2 ] ≡ [ifthen M1 else M2 ] ⋆ₑ [δ]

  -- guarded fixed points:
  --   every term of the form ([δ] ⋆ M) has a fixed point.
  [fix] : ∀ {B} → Exp B B → Exp [1] B
  [fix]-gfix : ∀ {B} (M : Exp B B)
    → ([fix] M ⋆ₑ ([δ] ⋆ₑ M)) ≡ [fix] M

quoteBool : Bool → Exp [1] [RetBool]
quoteBool false = [fls]
quoteBool true = [tru]

EXP : Category ℓ-zero ℓ-zero
EXP .ob = Ob
EXP .Hom[_,_] = Exp
EXP .id = idₑ
EXP ._⋆_ = _⋆ₑ_
EXP .⋆IdL = ⋆ₑIdL
EXP .⋆IdR = ⋆ₑIdR
EXP .⋆Assoc = ⋆ₑAssoc
EXP .isSetHom = isSetExp

[1]-TERMINAL : Terminal' EXP
[1]-TERMINAL .vertex = [1]
[1]-TERMINAL .element = tt
[1]-TERMINAL .universal Γ = isIsoToIsEquiv
  ( (λ z → []ₑ)
  , (λ _ → refl)
  , (λ _ → sym 1ηₑ))

module EXP where
  open Category EXP public

guarded-fixed-points : ∀ {B} (M : Exp B B) → fixed-point EXP [1] ([δ] EXP.⋆ M)
guarded-fixed-points M .fst = [fix] M
guarded-fixed-points M .snd = [fix]-gfix M

module _ (Cᴰ : Categoryᴰ EXP ℓCᴰ ℓCᴰ') (1ᴰ : Terminalᴰ Cᴰ [1]-TERMINAL)
  where
  private
    module Cᴰ = Fibers Cᴰ
    module 1ᴰ = TerminalᴰNotation Cᴰ {term = [1]-TERMINAL} 1ᴰ

  -- this is all just a bunch of one-off compatibility lemmas for now
  module _
    (⟦RetBool⟧ : Cᴰ.ob[ [RetBool] ])
    -- ([ifᴰthen_else_] : ∀ {B} {Bᴰ : Cᴰ.ob[ B ]}
    --   {M1 M2 : Exp [1] B}
    --   → Cᴰ.Hom[ M1 ][ 1ᴰ .fst , Bᴰ ]
    --   → Cᴰ.Hom[ M2 ][ 1ᴰ .fst , Bᴰ ]
    --   → Cᴰ.Hom[ [ifthen M1 else M2 ] ][ ⟦RetBool⟧ , Bᴰ ]
    --   )
    -- (δᴰ-ifᴰ : ∀ {B} {Bᴰ : Cᴰ.ob[ B ]}
    --   {M1 M2 : Exp [1] B}
    --   → (M1ᴰ : Cᴰ.Hom[ M1 ][ 1ᴰ .fst , Bᴰ ])
    --   → (M2ᴰ : Cᴰ.Hom[ M2 ][ 1ᴰ .fst , Bᴰ ])
    --   → (δᴰ Cᴰ.⋆ᴰ [ifᴰthen M1ᴰ else M2ᴰ ]) Cᴰ.≡[ [ite-δ] ] [ifᴰthen M1ᴰ else M2ᴰ ] Cᴰ.⋆ᴰ δᴰ
    --   )
    where
    elimOb : ∀ B → Cᴰ.ob[ B ]
    elimOb [RetBool] = ⟦RetBool⟧
    elimOb [1] = 1ᴰ .fst

    module _
      ([truᴰ] : Cᴰ.Hom[ [tru] ][ 1ᴰ .fst , ⟦RetBool⟧ ])
      ([flsᴰ] : Cᴰ.Hom[ [fls] ][ 1ᴰ .fst , ⟦RetBool⟧ ])
      (δᴰ : ∀ {B} → Cᴰ.Hom[ [δ] ][ elimOb B , elimOb B ])
      (fixᴰ : ∀ {B}{M : Exp B B} (Mᴰ : Cᴰ.Hom[ M ][ elimOb B , elimOb B ])
        → fixed-pointᴰ Cᴰ (guarded-fixed-points M) (1ᴰ .fst) (δᴰ Cᴰ.⋆ᴰ Mᴰ))
      where
      elimHom : ∀ {B1 B2} → (M : Exp B1 B2) → Cᴰ.Hom[ M ][ elimOb B1 , elimOb B2 ]
      elimHom idₑ = Cᴰ.idᴰ
      elimHom (M ⋆ₑ M₁) = elimHom M Cᴰ.⋆ᴰ elimHom M₁
      elimHom (⋆ₑIdL M i) = Cᴰ.⋆IdLᴰ (elimHom M) i
      elimHom (⋆ₑIdR M i) = Cᴰ.⋆IdRᴰ (elimHom M) i
      elimHom (⋆ₑAssoc M M₁ M₂ i) = Cᴰ.⋆Assocᴰ (elimHom M) (elimHom M₁) (elimHom M₂) i
      elimHom (isSetExp M M₁ x y i i₁) = isSetHomᴰ' Cᴰ (elimHom M) (elimHom M₁) (λ i → elimHom (x i)) ((λ i → elimHom (y i))) i i₁
      elimHom []ₑ = 1ᴰ.introᴰ _
      elimHom (1ηₑ {M = M} i) = Cᴰ.rectify {e' = 1ηₑ} (1ᴰ.ηᴰ (elimHom M)) i
      elimHom [tru] = [truᴰ]
      elimHom [fls] = [flsᴰ]
      -- elimHom [ifthen M else M₁ ] = [ifᴰthen elimHom M else elimHom M₁ ]
      elimHom [δ] = δᴰ
      -- elimHom ([ite-δ] {M1 = M1}{M2 = M2} i) = δᴰ-ifᴰ (elimHom M1) (elimHom M2) i
      elimHom ([fix] M) = fixᴰ (elimHom M) .fst
      elimHom ([fix]-gfix M i) = fixᴰ (elimHom M) .snd i

      elim : GlobalSection Cᴰ
      elim .Section.F-obᴰ = elimOb
      elim .Section.F-homᴰ = elimHom
      elim .Section.F-idᴰ = refl
      elim .Section.F-seqᴰ _ _ = refl

