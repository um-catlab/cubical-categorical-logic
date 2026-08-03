-- Additive structure for unary CBPV categories.
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base

open Functor
open Category

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' : Level
  module KindCat = Category KIND

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  ValueOb : Type ℓ
  ValueOb = C.ob[ 𝒱 ]

  ComputationOb : Type ℓ
  ComputationOb = C.ob[ 𝒞 ]

  EqTerminalⱽ : (k : Kind) → Type _
  EqTerminalⱽ k = EqPsh.Reprⱽ
    (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, k ]})

  EqInitialⱽ : (k : Kind) → Type _
  EqInitialⱽ k = EqPsh.Reprⱽ
    (EqPsh.UnitⱽPsh {Cᴰ = C ^opᴰ} {P = (KIND ^op) [-, k ]})

  EqBinProductⱽ : ∀ {k} (A₁ A₂ : C.ob[ k ]) → Type _
  EqBinProductⱽ A₁ A₂ = EqPsh.Reprⱽ
    ((EqPsh._[-][-,_] C A₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C A₂))

  EqBinCoProductⱽ : ∀ {k} (A₁ A₂ : C.ob[ k ]) → Type _
  EqBinCoProductⱽ A₁ A₂ = EqPsh.Reprⱽ
    ((EqPsh._[-][-,_] (C ^opᴰ) A₁) EqPsh.×ⱽPsh
     (EqPsh._[-][-,_] (C ^opᴰ) A₂))

AddCBPVCat : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
AddCBPVCat ℓ ℓ' =
  Σ[ C ∈ MultCBPVCat ℓ ℓ' ]
    Terminalⱽ (C .fst) 𝒱
  × (∀ (A₁ A₂ : ValueOb (C .fst)) → BinProductⱽ (C .fst) A₁ A₂)
  × Initialⱽ (C .fst) 𝒱
  × (∀ (A₁ A₂ : ValueOb (C .fst)) → BinCoProductⱽ (C .fst) A₁ A₂)
  × Terminalⱽ (C .fst) 𝒞
  × (∀ (B₁ B₂ : ComputationOb (C .fst)) → BinProductⱽ (C .fst) B₁ B₂)

AddCBPVCatEq : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
AddCBPVCatEq ℓ ℓ' =
  Σ[ C ∈ MultCBPVCatEq ℓ ℓ' ]
    EqTerminalⱽ (C .fst) 𝒱
  × (∀ (A₁ A₂ : ValueOb (C .fst)) → EqBinProductⱽ (C .fst) A₁ A₂)
  × EqInitialⱽ (C .fst) 𝒱
  × (∀ (A₁ A₂ : ValueOb (C .fst)) →
      EqBinCoProductⱽ (C .fst) A₁ A₂)
  × EqTerminalⱽ (C .fst) 𝒞
  × (∀ (B₁ B₂ : ComputationOb (C .fst)) →
      EqBinProductⱽ (C .fst) B₁ B₂)

forgetAddEq : AddCBPVCatEq ℓ ℓ' → AddCBPVCat ℓ ℓ'
forgetAddEq C .fst = forgetEq (C .fst)
forgetAddEq C .snd .fst =
  EqTerminalⱽ→Terminalⱽ KINDAssoc (C .fst .fst) (C .snd .fst)
forgetAddEq C .snd .snd .fst A₁ A₂ =
  EqBinProductⱽ→BinProductⱽ KINDAssoc (C .fst .fst)
    (C .snd .snd .fst A₁ A₂)
forgetAddEq C .snd .snd .snd .fst =
  EqTerminalⱽ→Terminalⱽ KIND^opAssoc ((C .fst .fst) ^opᴰ)
    (C .snd .snd .snd .fst)
forgetAddEq C .snd .snd .snd .snd .fst A₁ A₂ =
  EqBinProductⱽ→BinProductⱽ KIND^opAssoc ((C .fst .fst) ^opᴰ)
    (C .snd .snd .snd .snd .fst A₁ A₂)
forgetAddEq C .snd .snd .snd .snd .snd .fst =
  EqTerminalⱽ→Terminalⱽ KINDAssoc (C .fst .fst)
    (C .snd .snd .snd .snd .snd .fst)
forgetAddEq C .snd .snd .snd .snd .snd .snd B₁ B₂ =
  EqBinProductⱽ→BinProductⱽ KINDAssoc (C .fst .fst)
    (C .snd .snd .snd .snd .snd .snd B₁ B₂)

module _ {C : CBPVCat ℓ ℓ'} (Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Categoryᴰ C
    module Cᴰ = Categoryᴰ Cᴰ

  -- Cartesian lifts are only required over vertical morphisms in the chosen
  -- CBPV fiber.  These are the morphisms containing product projections.
  hasVerticalCartesianLiftsAt : (k : Kind) → Type _
  hasVerticalCartesianLiftsAt k =
    ∀ {A B : C.ob[ k ]} (f : C.Hom[ KindCat.id ][ A , B ])
      (Bᴰ : Cᴰ.ob[ k , B ])
    → CartesianLift Cᴰ (_ , f) Bᴰ

  -- Dually, these are precisely the lifts needed for coproduct injections.
  hasVerticalOpcartesianLiftsAt : (k : Kind) → Type _
  hasVerticalOpcartesianLiftsAt k =
    ∀ {A B : C.ob[ k ]} (f : C.Hom[ KindCat.id ][ A , B ])
      (Aᴰ : Cᴰ.ob[ k , A ])
    → CartesianLift (Cᴰ ^opᴰ) (_ , f) Aᴰ

  ValueTerminalsⱽ : Type _
  ValueTerminalsⱽ = ∀ A → Terminalⱽ Cᴰ (𝒱 , A)

  ValueBinProductsⱽ : Type _
  ValueBinProductsⱽ =
    ∀ {A} (A₁ᴰ A₂ᴰ : Cᴰ.ob[ 𝒱 , A ])
    → BinProductⱽ Cᴰ A₁ᴰ A₂ᴰ

  ValueInitialsⱽ : Type _
  ValueInitialsⱽ = ∀ A → Initialⱽ Cᴰ (𝒱 , A)

  ValueBinCoProductsⱽ : Type _
  ValueBinCoProductsⱽ =
    ∀ {A} (A₁ᴰ A₂ᴰ : Cᴰ.ob[ 𝒱 , A ])
    → BinCoProductⱽ Cᴰ A₁ᴰ A₂ᴰ

  ComputationTerminalsⱽ : Type _
  ComputationTerminalsⱽ = ∀ B → Terminalⱽ Cᴰ (𝒞 , B)

  ComputationBinProductsⱽ : Type _
  ComputationBinProductsⱽ =
    ∀ {B} (B₁ᴰ B₂ᴰ : Cᴰ.ob[ 𝒞 , B ])
    → BinProductⱽ Cᴰ B₁ᴰ B₂ᴰ

AddCBPVCatⱽ : ∀ (C : CBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type _
AddCBPVCatⱽ C ℓᴰ ℓᴰ' =
  Σ[ Cⱽ ∈ MultCBPVCatⱽ C ℓᴰ ℓᴰ' ]
    ValueTerminalsⱽ (Cⱽ .fst)
  × ValueBinProductsⱽ (Cⱽ .fst)
  × hasVerticalCartesianLiftsAt (Cⱽ .fst) 𝒱
  × ValueInitialsⱽ (Cⱽ .fst)
  × ValueBinCoProductsⱽ (Cⱽ .fst)
  × hasVerticalOpcartesianLiftsAt (Cⱽ .fst) 𝒱
  × ComputationTerminalsⱽ (Cⱽ .fst)
  × ComputationBinProductsⱽ (Cⱽ .fst)
  × hasVerticalCartesianLiftsAt (Cⱽ .fst) 𝒞

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓ'' ℓᴰ}
  (Dⱽ : AddCBPVCatⱽ D ℓᴰᴰ ℓᴰᴰ')
  (F : Functorⱽ C D)
  where
  private
    module F = Functorᴰ F
    Dᴰ = Dⱽ .fst .fst
    G = ∫F F

    -- The direct opposite avoids the toOpOp transports introduced by _^opF.
    G-op : Functor ((∫C C) ^op) ((∫C D) ^op)
    G-op .F-ob = G .F-ob
    G-op .F-hom = G .F-hom
    G-op .F-id = G .F-id
    G-op .F-seq f g = G .F-seq g f

  -- These cases are just eta expansions to get around the
  -- no-eta-equality for Categoryᴰ, specifically more ∫ and ^op stuff.
  reindexValueInitialⱽ : ValueInitialsⱽ (reindex Dᴰ G)
  reindexValueInitialⱽ A =
    init' .fst ,
    pshiso
      (pshhom
        (λ x → init' .snd .PshIso.trans .PshHom.N-ob x)
        (λ _ _ _ _ → refl))
      (init' .snd .PshIso.nIso)
    where
    init' = reindexTerminalⱽ G-op (𝒱 , A)
      (Dⱽ .snd .snd .snd .snd .fst (F.F-obᴰ A))

  reindexValueBinCoProductⱽ : ValueBinCoProductsⱽ (reindex Dᴰ G)
  reindexValueBinCoProductⱽ A₁ᴰ A₂ᴰ =
    bcp' .fst ,
    pshiso
      (pshhom
        (λ x → bcp' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y f p → bcp' .snd .PshIso.trans .PshHom.N-hom x y f p))
      (bcp' .snd .PshIso.nIso)
    where
    bcp' = reindexBinProductⱽ G-op A₁ᴰ A₂ᴰ
      (Dⱽ .snd .snd .snd .snd .snd .fst A₁ᴰ A₂ᴰ)

  reindexValueOpcartesianLifts :
    hasVerticalOpcartesianLiftsAt (reindex Dᴰ G) 𝒱
  reindexValueOpcartesianLifts f Aᴰ =
    lift' .fst ,
    pshiso
      (pshhom
        (λ x → lift' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y g p → lift' .snd .PshIso.trans .PshHom.N-hom x y g p))
      (lift' .snd .PshIso.nIso)
    where
    lift' = reindexCartesianLift (Dᴰ ^opᴰ) G-op (_ , f) Aᴰ
      (Dⱽ .snd .snd .snd .snd .snd .snd .fst (F.F-homᴰ f) Aᴰ)

  AddCBPVCatⱽReindex : AddCBPVCatⱽ C ℓᴰᴰ ℓᴰᴰ'
  AddCBPVCatⱽReindex .fst = MultCBPVCatⱽReindex (Dⱽ .fst) F
  AddCBPVCatⱽReindex .snd .fst A =
    reindexTerminalⱽ G (𝒱 , A) (Dⱽ .snd .fst (F.F-obᴰ A))
  AddCBPVCatⱽReindex .snd .snd .fst A₁ᴰ A₂ᴰ =
    reindexBinProductⱽ G A₁ᴰ A₂ᴰ (Dⱽ .snd .snd .fst A₁ᴰ A₂ᴰ)
  AddCBPVCatⱽReindex .snd .snd .snd .fst f Bᴰ =
    reindexCartesianLift Dᴰ G (_ , f) Bᴰ
      (Dⱽ .snd .snd .snd .fst (F.F-homᴰ f) Bᴰ)
  AddCBPVCatⱽReindex .snd .snd .snd .snd .fst = reindexValueInitialⱽ
  AddCBPVCatⱽReindex .snd .snd .snd .snd .snd .fst = reindexValueBinCoProductⱽ
  AddCBPVCatⱽReindex .snd .snd .snd .snd .snd .snd .fst =
    reindexValueOpcartesianLifts
  AddCBPVCatⱽReindex .snd .snd .snd .snd .snd .snd .snd .fst B =
    reindexTerminalⱽ G (𝒞 , B)
      (Dⱽ .snd .snd .snd .snd .snd .snd .snd .fst (F.F-obᴰ B))
  AddCBPVCatⱽReindex .snd .snd .snd .snd .snd .snd .snd .snd .fst B₁ᴰ B₂ᴰ =
    reindexBinProductⱽ G B₁ᴰ B₂ᴰ
      (Dⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst B₁ᴰ B₂ᴰ)
  AddCBPVCatⱽReindex .snd .snd .snd .snd .snd .snd .snd .snd .snd f Bᴰ =
    reindexCartesianLift Dᴰ G (_ , f) Bᴰ
      (Dⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd (F.F-homᴰ f) Bᴰ)
