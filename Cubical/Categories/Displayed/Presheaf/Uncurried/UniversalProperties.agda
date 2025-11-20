{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open PshIso
open UniversalElement

module _ {C : Category ℓC ℓC'}(P : Presheaf C ℓP)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module P = PresheafNotation P
  CartesianLiftPsh : ∀ {x} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (p : P.p[ x ])
    → Type _
  CartesianLiftPsh {x = x} Pᴰ p = Representableⱽ Cᴰ x (reindPshᴰNatTrans (yoRec P p) Pᴰ)

  isFibrationPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → Type _
  isFibrationPshᴰ Pᴰ = ∀ x (p : P.p[ x ]) → CartesianLiftPsh Pᴰ p

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  CartesianLift : ∀ {x y} (f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ])
    → Type _
  CartesianLift f yᴰ = CartesianLiftPsh (C [-, _ ]) Cᴰ (Cᴰ [-][-, yᴰ ]) f

  CartesianLiftable : ∀ {y} (yᴰ : Cᴰ.ob[ y ])
    → Type _
  CartesianLiftable {y} yᴰ = ∀ {x} (f : C [ x , y ]) → CartesianLift f yᴰ

  Quadrable : ∀ {x y} (f : C [ x , y ]) → Type _
  Quadrable f = ∀ yᴰ → CartesianLift f yᴰ

  isFibration : Type _
  isFibration = ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isFibrationPshᴰ (C [-, x ]) Cᴰ (Cᴰ [-][-, xᴰ ])

  Terminalⱽ : ∀ (x : C.ob) → Type _
  Terminalⱽ x = Representableⱽ Cᴰ x UnitPshᴰ

  Terminalsⱽ : Type _
  Terminalsⱽ = ∀ x → Terminalⱽ x

  BinProductⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductⱽ {x} Γᴰ xᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh (Cᴰ [-][-, xᴰ ]))

  BinProductsWithⱽ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductsWithⱽ {x} xᴰ = ∀ Γᴰ → BinProductⱽ Γᴰ xᴰ

  isLRⱽ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  isLRⱽ {x} xᴰ = Σ[ lifts ∈ CartesianLiftable xᴰ ]
    (∀ {Γ}(f : C [ Γ , x ]) → BinProductsWithⱽ (lifts f .fst))

  LRⱽObᴰ : ∀ (x : C.ob) → Type _
  LRⱽObᴰ x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] isLRⱽ xᴰ

  LRⱽObᴰ→LRⱽ : ∀ {x} → (xᴰ : LRⱽObᴰ x) → LRⱽPresheafᴰ (C [-, x ]) Cᴰ _
  LRⱽObᴰ→LRⱽ (xᴰ , _) .fst = Cᴰ [-][-, xᴰ ]
  LRⱽObᴰ→LRⱽ (xᴰ , _*xᴰ , _*xᴰ×ⱽ_) .snd {Γ} Γᴰ f = ((f *xᴰ×ⱽ Γᴰ) .fst) ,
    ((f *xᴰ×ⱽ Γᴰ) .snd ⋆PshIsoⱽ ×PshIso idPshIso ((f *xᴰ) .snd))

  BinProductsⱽ : Type _
  BinProductsⱽ = ∀ {x} xᴰ yᴰ → BinProductⱽ {x} xᴰ yᴰ

  LargeExponentialⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  LargeExponentialⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ⇒ⱽPshLarge (Cᴰ [-][-, yᴰ ]))

  LargeExponentialsⱽ : Type _
  LargeExponentialsⱽ = ∀ {x} xᴰ yᴰ → LargeExponentialⱽ {x} xᴰ yᴰ

  -- The one without the qualifier represents the *small* exponential
  Exponentialⱽ : ∀ {x} ((xᴰ , _×ⱽxᴰ) : LRⱽObᴰ x) (yᴰ : Cᴰ.ob[ x ]) → Type _
  Exponentialⱽ {x} xᴰ yᴰ =
    Representableⱽ Cᴰ x (LRⱽObᴰ→LRⱽ xᴰ ⇒ⱽPshSmall (Cᴰ [-][-, yᴰ ]))

  BinProductsⱽ+Fibration→AllLRⱽ : BinProductsⱽ → isFibration
    → ∀ x (xᴰ : Cᴰ.ob[ x ]) → isLRⱽ xᴰ
  BinProductsⱽ+Fibration→AllLRⱽ bpⱽ lifts x xᴰ =
    (λ {x = y} → lifts xᴰ y) , (λ {Γ} f → λ Γᴰ → bpⱽ Γᴰ (lifts xᴰ Γ f .fst))

  Exponentialsⱽ : BinProductsⱽ → isFibration → Type _
  Exponentialsⱽ bpⱽ lifts = ∀ {x} (xᴰ yᴰ : Cᴰ.ob[ x ])
    → Exponentialⱽ (xᴰ , (BinProductsⱽ+Fibration→AllLRⱽ bpⱽ lifts x xᴰ)) yᴰ

  isLR∀Ob : (A : C.ob) → Type _
  isLR∀Ob A =
    Σ[ _×A ∈ BinProductsWith C A ]
    ∀ (Γ : C.ob) → Quadrable ((Γ ×A) .element .fst)

  BinProducts+isFibration→isLR∀Ob : BinProducts C → isFibration
    → ∀ A → isLR∀Ob A
  BinProducts+isFibration→isLR∀Ob bp lifts A = (λ Γ → bp (Γ , A)) ,
    λ Γ yᴰ → lifts yᴰ (bp (Γ , A) .vertex) (bp (Γ , A) .element .fst)

  LR∀Ob : Type _
  LR∀Ob = Σ C.ob isLR∀Ob

  -- TODO: double check to make sure this is the right definition, the
  -- reindPshᴰ is a little suspicious
  UniversalQuantifier : ∀ {Γ} ((A , _×A , π₁*) : LR∀Ob) (Aᴰ : Cᴰ.ob[ (Γ ×A) .vertex ]) → Type _
  UniversalQuantifier {Γ} (A , _×A , π₁*) Aᴰ = Representableⱽ Cᴰ Γ (
    ∀PshSmall Cᴰ ((C [-, A ]) , (_×A , (λ {x} → π₁* x)))
                 (reindPshᴰNatTrans (invPshIso (yoRecIso (Γ ×A)) .trans) (Cᴰ [-][-, Aᴰ ])))

  UniversalQuantifiers : BinProducts C → isFibration → Type _
  UniversalQuantifiers bp lifts = ∀ Γ A (Aᴰ : Cᴰ.ob[ bp (Γ , A) .vertex ]) →
    UniversalQuantifier {Γ = Γ} (A , BinProducts+isFibration→isLR∀Ob bp lifts A) Aᴰ
