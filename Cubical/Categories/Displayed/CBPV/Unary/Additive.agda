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

AddCBPVCatᴰ : ∀ (C : AddCBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type _
AddCBPVCatᴰ C ℓᴰ ℓᴰ' =
  Σ[ Cᴰ ∈ MultCBPVCatᴰ (C .fst) ℓᴰ ℓᴰ' ]
    Terminalⱽᴰ (Cᴰ .fst) (C .snd .fst)
  × (∀ A₁ A₂
      (A₁ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒱 , A₁))
      (A₂ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒱 , A₂))
      → BinProductⱽᴰ (Cᴰ .fst) (C .snd .snd .fst A₁ A₂) A₁ᴰ A₂ᴰ)
  × Initialⱽᴰ (Cᴰ .fst) (C .snd .snd .snd .fst)
  × (∀ A₁ A₂
      (A₁ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒱 , A₁))
      (A₂ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒱 , A₂))
      → BinCoProductⱽᴰ (Cᴰ .fst) (C .snd .snd .snd .snd .fst A₁ A₂) A₁ᴰ A₂ᴰ)
  × Terminalⱽᴰ (Cᴰ .fst) (C .snd .snd .snd .snd .snd .fst)
  × (∀ B₁ B₂
      (B₁ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒞 , B₁))
      (B₂ᴰ : Categoryᴰ.ob[_] (Cᴰ .fst) (𝒞 , B₂))
      → BinProductⱽᴰ (Cᴰ .fst) (C .snd .snd .snd .snd .snd .snd B₁ B₂) B₁ᴰ B₂ᴰ)

module AddCBPVCatᴰNotation
  (C : AddCBPVCat ℓ ℓ') (Cᴰ : AddCBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    Dᴰ = Cᴰ .fst .fst

  open TerminalⱽᴰNotation Dᴰ (C .snd .fst) (Cᴰ .snd .fst) public renaming
    (vertexᴰ to value-terminal-obᴰ ; !ⱽᴰ to value-terminal-introᴰ ;
     !ηⱽᴰ to value-terminal-ηᴰ ; !ηⱽᴰ-on to value-terminal-ηᴰ-on)

  module _ {A₁ A₂}
    (A₁ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒱 , A₁))
    (A₂ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒱 , A₂)) where
    open BinProductⱽᴰNotation Dᴰ (C .snd .snd .fst A₁ A₂)
      (Cᴰ .snd .snd .fst A₁ A₂ A₁ᴰ A₂ᴰ) public renaming
      (vertexᴰ to value-product-obᴰ ; πᴰ₁ to value-πᴰ₁ ; πᴰ₂ to value-πᴰ₂ ;
       _,ⱽᴰ_ to value-pairᴰ ; ×βⱽᴰ₁ to value-×βᴰ₁ ;
       ×βⱽᴰ₂ to value-×βᴰ₂ ; ×ηⱽᴰ to value-×ηᴰ ;
       ×βⱽᴰ₁-on to value-×βᴰ₁-on ; ×βⱽᴰ₂-on to value-×βᴰ₂-on ;
       ×ηⱽᴰ-on to value-×ηᴰ-on)

  open InitialⱽᴰNotation Dᴰ (C .snd .snd .snd .fst)
    (Cᴰ .snd .snd .snd .fst) public renaming
    (vertexᴰ to value-initial-obᴰ ; ¡ⱽᴰ to value-initial-elimᴰ ;
     ¡ηⱽᴰ to value-initial-ηᴰ ; ¡ηⱽᴰ-on to value-initial-ηᴰ-on)

  module _ {A₁ A₂}
    (A₁ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒱 , A₁))
    (A₂ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒱 , A₂)) where
    open BinCoProductⱽᴰNotation Dᴰ (C .snd .snd .snd .snd .fst A₁ A₂)
      (Cᴰ .snd .snd .snd .snd .fst A₁ A₂ A₁ᴰ A₂ᴰ) public renaming
      (vertexᴰ to value-coproduct-obᴰ ; σᴰ₁ to value-σᴰ₁ ; σᴰ₂ to value-σᴰ₂ ;
       [_,ⱽᴰ_] to value-copairᴰ ; +βⱽᴰ₁ to value-+βᴰ₁ ;
       +βⱽᴰ₂ to value-+βᴰ₂ ; +ηⱽᴰ to value-+ηᴰ ;
       +βⱽᴰ₁-on to value-+βᴰ₁-on ; +βⱽᴰ₂-on to value-+βᴰ₂-on ;
       +ηⱽᴰ-on to value-+ηᴰ-on)

  open TerminalⱽᴰNotation Dᴰ (C .snd .snd .snd .snd .snd .fst)
    (Cᴰ .snd .snd .snd .snd .snd .fst) public renaming
    (vertexᴰ to computation-terminal-obᴰ ; !ⱽᴰ to computation-terminal-introᴰ ;
     !ηⱽᴰ to computation-terminal-ηᴰ ;
     !ηⱽᴰ-on to computation-terminal-ηᴰ-on)

  module _ {B₁ B₂}
    (B₁ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒞 , B₁))
    (B₂ᴰ : Categoryᴰ.ob[_] Dᴰ (𝒞 , B₂)) where
    open BinProductⱽᴰNotation Dᴰ (C .snd .snd .snd .snd .snd .snd B₁ B₂)
      (Cᴰ .snd .snd .snd .snd .snd .snd B₁ B₂ B₁ᴰ B₂ᴰ) public renaming
      (vertexᴰ to computation-product-obᴰ ; πᴰ₁ to computation-πᴰ₁ ;
       πᴰ₂ to computation-πᴰ₂ ; _,ⱽᴰ_ to computation-pairᴰ ;
       ×βⱽᴰ₁ to computation-×βᴰ₁ ; ×βⱽᴰ₂ to computation-×βᴰ₂ ;
       ×ηⱽᴰ to computation-×ηᴰ ;
       ×βⱽᴰ₁-on to computation-×βᴰ₁-on ;
       ×βⱽᴰ₂-on to computation-×βᴰ₂-on ;
       ×ηⱽᴰ-on to computation-×ηᴰ-on)

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

AddCBPVCatⱽ→ᴰ : {C : AddCBPVCat ℓ ℓ'}
  → AddCBPVCatⱽ (C .fst .fst) ℓᴰ ℓᴰ'
  → AddCBPVCatᴰ C ℓᴰ ℓᴰ'
AddCBPVCatⱽ→ᴰ Cⱽ .fst = MultCBPVCatⱽ→ᴰ (Cⱽ .fst)
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .fst =
  Terminalⱽ→ⱽᴰ D value-terminal
    (Cⱽ .snd .fst (value-terminal .fst))
  where
  D = Cⱽ .fst .fst
  value-terminal = C .snd .fst
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd .fst A₁ A₂ A₁ᴰ A₂ᴰ =
  BinProductⱽ+π*→ⱽᴰ D bp A₁ᴰ A₂ᴰ π₁*A₁ᴰ π₂*A₂ᴰ
    (Cⱽ .snd .snd .fst (π₁*A₁ᴰ .fst) (π₂*A₂ᴰ .fst))
  where
  D = Cⱽ .fst .fst
  bp = C .snd .snd .fst A₁ A₂
  module bp = BinProductⱽNotation (C .fst .fst) bp
  π₁*A₁ᴰ = Cⱽ .snd .snd .snd .fst bp.π₁ A₁ᴰ
  π₂*A₂ᴰ = Cⱽ .snd .snd .snd .fst bp.π₂ A₂ᴰ
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd .snd .fst =
  Terminalⱽ→ⱽᴰ (D ^opᴰᴰ) value-initial
    (Terminalⱽ^opᴰ→^opᴰᴰ D
      (Cⱽ .snd .snd .snd .snd .fst (value-initial .fst)))
  where
  D = Cⱽ .fst .fst
  value-initial = C .snd .snd .snd .fst
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd .snd .snd .fst
  A₁ A₂ A₁ᴰ A₂ᴰ =
  BinProductⱽ+π*→ⱽᴰ (D ^opᴰᴰ) bcp A₁ᴰ A₂ᴰ σ₁!A₁ᴰ σ₂!A₂ᴰ
    (BinProductⱽ^opᴰ→^opᴰᴰ D
      (Cⱽ .snd .snd .snd .snd .snd .fst (σ₁!A₁ᴰ .fst) (σ₂!A₂ᴰ .fst)))
  where
  D = Cⱽ .fst .fst
  bcp = C .snd .snd .snd .snd .fst A₁ A₂
  module bcp = BinProductⱽNotation ((C .fst .fst) ^opᴰ) bcp
  σ₁!A₁ᴰ = CartesianLift^opᴰ→^opᴰᴰ D
    (Cⱽ .snd .snd .snd .snd .snd .snd .fst bcp.π₁ A₁ᴰ)
  σ₂!A₂ᴰ = CartesianLift^opᴰ→^opᴰᴰ D
    (Cⱽ .snd .snd .snd .snd .snd .snd .fst bcp.π₂ A₂ᴰ)
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd .snd .snd .snd .fst =
  Terminalⱽ→ⱽᴰ D computation-terminal
    (Cⱽ .snd .snd .snd .snd .snd .snd .snd .fst
      (computation-terminal .fst))
  where
  D = Cⱽ .fst .fst
  computation-terminal = C .snd .snd .snd .snd .snd .fst
AddCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd .snd .snd .snd .snd
  B₁ B₂ B₁ᴰ B₂ᴰ =
  BinProductⱽ+π*→ⱽᴰ D bp B₁ᴰ B₂ᴰ π₁*B₁ᴰ π₂*B₂ᴰ
    (Cⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst
      (π₁*B₁ᴰ .fst) (π₂*B₂ᴰ .fst))
  where
  D = Cⱽ .fst .fst
  bp = C .snd .snd .snd .snd .snd .snd B₁ B₂
  module bp = BinProductⱽNotation (C .fst .fst) bp
  π₁*B₁ᴰ = Cⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd
    bp.π₁ B₁ᴰ
  π₂*B₂ᴰ = Cⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd
    bp.π₂ B₂ᴰ

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓ'' ℓᴰ}
  (Dⱽ : AddCBPVCatⱽ D ℓᴰᴰ ℓᴰᴰ')
  (F : Functorⱽ C D)
  where
  private
    module F = Functorᴰ F
    Dᴰ = Dⱽ .fst .fst
    G = ∫F F


  reindexValueInitialⱽ : ValueInitialsⱽ (reindex Dᴰ G)
  reindexValueInitialⱽ A =
    reindexInitialⱽ G (𝒱 , A) (Dⱽ .snd .snd .snd .snd .fst (F.F-obᴰ A))

  reindexValueBinCoProductⱽ : ValueBinCoProductsⱽ (reindex Dᴰ G)
  reindexValueBinCoProductⱽ A₁ᴰ A₂ᴰ =
    reindexBinCoProductⱽ G A₁ᴰ A₂ᴰ
      (Dⱽ .snd .snd .snd .snd .snd .fst A₁ᴰ A₂ᴰ)

  reindexValueOpcartesianLifts :
    hasVerticalOpcartesianLiftsAt (reindex Dᴰ G) 𝒱
  reindexValueOpcartesianLifts f Aᴰ =
    reindexOpcartesianLift G (_ , f) Aᴰ
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
