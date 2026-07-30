{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More


open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

CBPVCat : ∀ ℓ ℓ' → Type _
CBPVCat = Categoryᴰ KIND

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  CBPVCatᴰ : ∀ ℓᴰ ℓᴰ' → Type _
  CBPVCatᴰ = Categoryᴰ (∫C C)

  U-Spec : (B : C.ob[ 𝓒 ]) → Presheafⱽ 𝓥 C ℓ'
  U-Spec B = reindPshᴰNatTrans (yoRec (KIND [-, 𝓒 ]) _) (C [-][-, B ])

  -- N.b.: this implies that C is a fibration because the only other
  -- morphisms in the base are identities
  hasU : Type _
  hasU = Quadrable C {x = 𝓥}{y = 𝓒} _

  -- This is better because KIND is strict category
  hasUEq : Type _
  hasUEq = ∀ (B : C.ob[ 𝓒 ]) → EqPsh.CartesianLift C (λ _ _ _ _ _ _ → Eq.refl)
    {x = 𝓥}{y = 𝓒}
    _
    B

  -- this similarly implies that C is an opfibration
  hasF : Type _
  hasF = Quadrable (C ^opᴰ) {x = 𝓒}{y = 𝓥} _

  hasFEq : Type _
  hasFEq = ∀ (A : C.ob[ 𝓥 ]) → EqPsh.CartesianLift (C ^opᴰ) (λ _ _ _ _ _ _ → Eq.refl)
    {x = 𝓒}{y = 𝓥}
    _
    A

module _ {C : CBPVCat ℓ ℓ'}(Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Fibers C
    module Cᴰ = Fibers Cᴰ

  hasUⱽ : Type _
  hasUⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable Cᴰ (_ , f)

  hasFⱽ : Type _
  hasFⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable (Cᴰ ^opᴰ) (_ , f)

  -- TODO: hasUⱽ/hasFⱽ are closed under reindexing. Should be just an instantiation of something else in the library already.

  -- hasUⱽ : Type _
  -- hasUⱽ = isFibration Cᴰ
--   π≤ : ∀ B → PshHom (PresheafᴰNotation.∫ C (KIND [-, 𝓥 ]) (U-Spec C B)) (∫C C [-, 𝓒 , B ])
--   π≤ B = ∫PshHomᴰ {α = yoRec (KIND [-, 𝓒 ]) _} idPshHom ⋆PshHom (∫Repr-iso C) .PshIso.trans

--   Uᴰ-Specᴰ : ∀ {B}(Bᴰ : Cᴰ.ob[ 𝓒 , B ]) → Presheafᴰ (PresheafᴰNotation.∫ C (KIND [-, 𝓥 ]) (U-Spec C B)) Cᴰ ℓᴰ'
--   Uᴰ-Specᴰ {B} Bᴰ = reindPshᴰNatTrans (π≤ B) (Cᴰ [-][-, Bᴰ ])

--   module _ {B} (UB : Representableⱽ C 𝓥 (U-Spec C B)) where
--     force : C [ _ ][ UB .fst , B ]
--     force = UB .snd .PshIso.trans .PshHom.N-ob (𝓥 , UB .fst , ı tt) C.idᴰ

--     half-force* : PshHom (∫C C [-, 𝓥 , UB .fst ]) (PresheafᴰNotation.∫ C (KIND [-, 𝓥 ]) (U-Spec C B))
--     half-force* = invPshIso (∫Repr-iso C) .PshIso.trans ⋆PshHom ∫PshHomⱽ (UB .snd .PshIso.trans)

--     force* force*' : PshHom (∫C C [-, 𝓥 , UB .fst ]) (∫C C [-, 𝓒 , B ])
--     force* = (yoRec ((∫C C) [-, 𝓒 , B ]) (_ , force)) -- i.e. _⋆ force ≡ _⋆ thunk⁻ id
--     force*' = half-force* ⋆PshHom π≤ B                -- i.e., thunk⁻

--     -- force*' is the one that actually has better behavior because it avoids using yoRec
--     -- if UB were constructed *using* yoRec, you get a double yoRec boo
--     force*≡force*' : force* ≡ force*'
--     force*≡force*' = yoInd (∫C C [-, 𝓒 , B ]) force* force*' (C.⋆IdL _)

--     module _ (Bᴰ : Cᴰ.ob[ 𝓒 , B ]) where
--       Uᴰ-Specⱽ : Presheafⱽ (𝓥 , UB .fst) Cᴰ _
--       Uᴰ-Specⱽ = reindPshᴰNatTrans force* (Cᴰ [-][-, Bᴰ ])

--       Uᴰ-Specⱽ' : Presheafⱽ (𝓥 , UB .fst) Cᴰ _
--       Uᴰ-Specⱽ' = reindPshᴰNatTrans force*' (Cᴰ [-][-, Bᴰ ])

--       -- takes long (possibly forever) without --lossy-unification
--       Uᴰ-Specⱽ'≅ᴰ : PshIso Uᴰ-Specⱽ' (reindPshᴰNatTrans half-force* (Uᴰ-Specᴰ Bᴰ))
--       Uᴰ-Specⱽ'≅ᴰ = invPshIso $ reindPshᴰNatTrans-tri half-force* (π≤ B) (half-force* ⋆PshHom (π≤ B)) (Cᴰ [-][-, Bᴰ ]) refl

--       Uᴰ-Specⱽ≅ᴰ : PshIso Uᴰ-Specⱽ (reindPshᴰNatTrans half-force* (Uᴰ-Specᴰ Bᴰ))
--       Uᴰ-Specⱽ≅ᴰ = reindPshᴰNatTrans-Path force* force*' force*≡force*' (Cᴰ [-][-, Bᴰ ]) ⋆PshIso Uᴰ-Specⱽ'≅ᴰ

--   module _ (U : hasU C) where
--     hasUᴰ : Type _
--     hasUᴰ = ∀ {B} (Bᴰ : Cᴰ.ob[ 𝓒 , B ])
--       → Representableᴰ Cᴰ _ (Uᴰ-Specᴰ Bᴰ) (∫Representableⱽ C 𝓥 (U-Spec C B) (U B))

--     hasUⱽ : Type _
--     hasUⱽ = ∀ {B} (Bᴰ : Cᴰ.ob[ 𝓒 , B ]) → Representableⱽ Cᴰ (𝓥 , U B .fst) (Uᴰ-Specⱽ (U B) Bᴰ)

--     hasUⱽ→ᴰ : hasUⱽ → hasUᴰ
--     hasUⱽ→ᴰ Uⱽ {B} Bᴰ .fst = Uⱽ Bᴰ .fst
--     hasUⱽ→ᴰ Uⱽ {B} Bᴰ .snd = FiberwisePshIsoᴰ→PshIsoᴰ $
--       Uⱽ Bᴰ .snd
--       ⋆PshIso Uᴰ-Specⱽ≅ᴰ (U B) Bᴰ

--   -- We now need three theorems:
--   --   1. eq-based to non-eq based for vertical
--   --   2. reindexing of vertical
--   --   3. vertical to displayed
