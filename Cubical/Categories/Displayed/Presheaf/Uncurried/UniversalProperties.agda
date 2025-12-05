{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

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

open PshHom
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

  isLRⱽObᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  isLRⱽObᴰ {x} xᴰ = LocallyRepresentableⱽ (Cᴰ [-][-, xᴰ ])
    -- Σ[ lifts ∈ CartesianLiftable xᴰ ]
    -- (∀ {Γ}(f : C [ Γ , x ]) → BinProductsWithⱽ (lifts f .fst))

  LRⱽObᴰ : ∀ (x : C.ob) → Type _
  LRⱽObᴰ x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] isLRⱽObᴰ xᴰ

  LRⱽObᴰ→LRⱽ : ∀ {x} → (xᴰ : LRⱽObᴰ x) → LRⱽPresheafᴰ (C [-, x ]) Cᴰ _
  LRⱽObᴰ→LRⱽ xᴰ = (Cᴰ [-][-, xᴰ .fst ]) , (xᴰ .snd)

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
  -- TODO: make an explicit definition for the functor you get out of an LRⱽ

  BinProductsⱽ+Fibration→AllLRⱽ : BinProductsⱽ → isFibration
    → ∀ x (xᴰ : Cᴰ.ob[ x ]) → isLRⱽObᴰ xᴰ
  BinProductsⱽ+Fibration→AllLRⱽ bpⱽ lifts x xᴰ {Γ} Γᴰ f =
    (bpⱽ Γᴰ (lifts xᴰ Γ f .fst) .fst)
    , (bpⱽ _ _ .snd
      ⋆PshIsoⱽ ×PshIso idPshIso (lifts xᴰ Γ f .snd))

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

  module LRⱽPresheafᴰNotation {P : Presheaf C ℓP} (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ) where
    private
      module P = PresheafNotation P
    open PresheafᴰNotation Cᴰ P (Pᴰ .fst)
    _×ⱽ_* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
    Γᴰ ×ⱽ p * = Pᴰ .snd Γᴰ p .fst

    introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → p[ γ P.⋆ p ][ Δᴰ ]
      → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
    introᴰ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ = Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .fst
      (γᴰ , γpᴰ)

    congP-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
      {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
      (γ≡γ' : γ ≡ γ')
      (γᴰ≡γᴰ' : γᴰ Cᴰ.≡[ γ≡γ' ] γᴰ')
      (γpᴰ≡γ'pᴰ : γpᴰ ≡[ (λ i → γ≡γ' i P.⋆ p) ] γ'pᴰ)
      → introᴰ γᴰ γpᴰ Cᴰ.≡[ γ≡γ' ] introᴰ γᴰ' γ'pᴰ
    congP-introᴰ γ≡γ' γᴰ≡γᴰ' γpᴰ≡γ'pᴰ = λ i → introᴰ (γᴰ≡γᴰ' i) (γpᴰ≡γ'pᴰ i)

    cong∫-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
      {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
      (γᴰ≡γᴰ' : Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
      (γpᴰ≡γ'pᴰ : γpᴰ ∫≡ γ'pᴰ)
      → Path (Cᴰ.Hom[ _ , _ ]) (_ , introᴰ γᴰ γpᴰ) (_ , introᴰ γᴰ' γ'pᴰ)
    cong∫-introᴰ γᴰ≡γᴰ' γpᴰ≡γ'pᴰ =
      Cᴰ.≡in $ congP-introᴰ (PathPΣ γᴰ≡γᴰ' .fst) (Cᴰ.≡out γᴰ≡γᴰ') (rectify $ ≡out $ γpᴰ≡γ'pᴰ)

    _⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
      → Cᴰ [ γ ][ Δᴰ , Γᴰ ]
    γᴰ ⋆π₁ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .fst

    ⟨_⟩⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ ⋆π₁ⱽ) (_ , γᴰ' ⋆π₁ⱽ))
    ⟨ γᴰ≡γᴰ' ⟩⋆π₁ⱽ i = (γᴰ≡γᴰ' i .fst) , (γᴰ≡γᴰ' i .snd ⋆π₁ⱽ)

    ⋆π₁ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
      → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₁ⱽ) (_ , δᴰ Cᴰ.⋆ᴰ (γᴰ ⋆π₁ⱽ))
    ⋆π₁ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
      ⟨ Cᴰ.reind-filler refl (δᴰ Cᴰ.⋆ᴰ γᴰ) ⟩⋆π₁ⱽ ∙ Cᴰ.≡in (cong fst (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , (λ i → δ C.⋆ γ)) _))
      ∙ (sym $ Cᴰ.reind-filler _ _)

    π₁ⱽ : ∀ {Γ Γᴰ p} → Cᴰ [ C.id {Γ} ][ Γᴰ ×ⱽ p * , Γᴰ ]
    π₁ⱽ = Cᴰ.idᴰ ⋆π₁ⱽ

    β₁ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ ⋆π₁ⱽ)) (_ , γᴰ)
    β₁ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      Cᴰ.≡in $ cong fst $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ)

    β₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ Cᴰ.⋆ᴰ π₁ⱽ)) (_ , γᴰ)
    β₁ⱽ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      (sym $ ⋆π₁ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ) ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₁ⱽ ∙ β₁ⱽ' γᴰ γpᴰ

    _⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
      → p[ γ P.⋆ p ][ Δᴰ ]
    γᴰ ⋆π₂ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .snd

    π₂ⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p} → p[ C.id P.⋆ p ][ Γᴰ ×ⱽ p * ]
    π₂ⱽ = Cᴰ.idᴰ ⋆π₂ⱽ

    ⟨_⟩⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
      → (γᴰ ⋆π₂ⱽ) ∫≡ (γᴰ' ⋆π₂ⱽ)
    ⟨ γᴰ≡γᴰ' ⟩⋆π₂ⱽ i = (γᴰ≡γᴰ' i .fst P.⋆ _) , (γᴰ≡γᴰ' i .snd ⋆π₂ⱽ)

    ⋆π₂ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
      → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → ((δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₂ⱽ) ∫≡ (δᴰ ⋆ᴰ (γᴰ ⋆π₂ⱽ))
    ⋆π₂ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
      ⟨ Cᴰ.reind-filler _ _ ⟩⋆π₂ⱽ
      ∙ (≡in $ (PathPΣ (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , refl) _)) .snd)
      ∙ ⋆ᴰ-reind _ _ _

    β₂ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → (introᴰ γᴰ γpᴰ ⋆π₂ⱽ) ∫≡ γpᴰ
    β₂ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      ≡in $ snd $ PathPΣ (Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ))

    β₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → (introᴰ γᴰ γpᴰ ⋆ᴰ π₂ⱽ) ∫≡ γpᴰ
    β₂ⱽ γᴰ γpᴰ =
      sym (⋆π₂ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ)
      ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₂ⱽ
      ∙ β₂ⱽ' γᴰ γpᴰ

    ηⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ (γᴰ ⋆π₁ⱽ) (γᴰ ⋆π₂ⱽ)) (_ , γᴰ)
    ηⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ =
      Cᴰ.≡in $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .snd γᴰ

    introᴰ≡ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      → {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → Path Cᴰ.Hom[ _ , _ ] (_ , γᴰ) (_ , (γᴰ' ⋆π₁ⱽ))
      → (γpᴰ ∫≡ (γᴰ' ⋆π₂ⱽ))
      → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ γᴰ γpᴰ) (_ , γᴰ')
    introᴰ≡ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {γ'} {p} {γᴰ} {γpᴰ} {γᴰ'} γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂ =
      cong∫-introᴰ γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂
      ∙ ηⱽ' γᴰ'
