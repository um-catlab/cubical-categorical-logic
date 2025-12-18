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
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
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
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

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

  LRⱽObᴰ : ∀ (x : C.ob) → Type _
  LRⱽObᴰ x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] isLRⱽObᴰ xᴰ

  LRⱽObᴰ→LRⱽ : ∀ {x} → (xᴰ : LRⱽObᴰ x) → LRⱽPresheafᴰ (C [-, x ]) Cᴰ _
  LRⱽObᴰ→LRⱽ xᴰ = (Cᴰ [-][-, xᴰ .fst ]) , (xᴰ .snd)

  BinProductsⱽ : Type _
  BinProductsⱽ = ∀ {x} xᴰ yᴰ → BinProductⱽ {x} xᴰ yᴰ

  AllLRⱽ : Type _
  AllLRⱽ = ∀ {x} xᴰ → isLRⱽObᴰ {x} xᴰ

  LargeExponentialⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  LargeExponentialⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ⇒ⱽPshLarge (Cᴰ [-][-, yᴰ ]))

  LargeExponentialsⱽ : Type _
  LargeExponentialsⱽ = ∀ {x} xᴰ yᴰ → LargeExponentialⱽ {x} xᴰ yᴰ

  -- The one without the qualifier represents the *small* exponential
  Exponentialⱽ : ∀ {x} ((xᴰ , _×ⱽxᴰ) : LRⱽObᴰ x) (yᴰ : Cᴰ.ob[ x ]) → Type _
  Exponentialⱽ {x} xᴰ yᴰ =
    Representableⱽ Cᴰ x (LRⱽObᴰ→LRⱽ xᴰ ⇒ⱽPshSmall (Cᴰ [-][-, yᴰ ]))

  -- BinProductsⱽ+Fibration→AllLRⱽ : BinProductsⱽ → isFibration
  --   → AllLRⱽ
  -- BinProductsⱽ+Fibration→AllLRⱽ bpⱽ lifts {x} xᴰ {Γ} Γᴰ f =
  --   (bpⱽ Γᴰ (lifts xᴰ Γ f .fst) .fst)
  --   , (bpⱽ _ _ .snd
  --     ⋆PshIsoⱽ ×PshIso idPshIso (lifts xᴰ Γ f .snd))

  -- Exponentialsⱽ : AllLRⱽ → Type _
  -- Exponentialsⱽ lrⱽ = ∀ {x} (xᴰ yᴰ : Cᴰ.ob[ x ])
  --   → Exponentialⱽ (xᴰ , lrⱽ xᴰ) yᴰ

  -- π₁-Quadrable : ∀ {A} (_×A : BinProductsWith C A) → Type _
  -- π₁-Quadrable _×A = ∀ Γ → Quadrable ((Γ ×A) .element .fst)

  -- π₁F : ∀ {Γ A} (_×A : BinProductsWith C A)
  --   → Functor (Cᴰ / (C [-, (Γ ×A) .vertex ])) (Cᴰ / (C [-, Γ ]))
  -- π₁F _×A = Idᴰ /Fⱽ yoRec (C [-, _ ]) ((_ ×A) .element .fst)

  -- wkProf : ∀ {Γ A} (_×A : BinProductsWith C A)
  --   → Profunctor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, (Γ ×A) .vertex ])) {!!}
  -- wkProf _×A = {!!}

  -- wk : ∀ {Γ A} (_×A : BinProductsWith C A) (π₁* : π₁-Quadrable _×A)
  --   → Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, (Γ ×A) .vertex ]))
  -- wk _×A π₁* = {!FunctorComprehension!}

  -- wkOb : ∀ {A} (_×A : BinProductsWith C A) (π₁* : π₁-Quadrable _×A) Γ (Γ×A : BinProduct C (Γ , A))
  --   → Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, Γ×A .vertex ]))
  -- wkOb _×A π₁* Γ Γ×A = record
  --   { F-ob = λ (Δ , Δᴰ , γ) →
  --     -×A.vertex {Δ} , π₁* Δ Δᴰ .fst , Γ×A.intro ((-×A.element .fst C.⋆ γ) , (-×A.element .snd))
  --   ; F-hom = λ (δ , δᴰ , δ⋆γ≡γ') →
  --     (-×A.intro ((-×A.element .fst C.⋆ δ) , -×A.element .snd))
  --     , (π₁* _ _ .snd .nIso _ .fst (Cᴰ.reind (C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ (sym $ PathPΣ -×A.β .fst)) (π₁* _ _ .snd .trans .N-ob _ Cᴰ.idᴰ Cᴰ.⋆ᴰ δᴰ)))
  --     , (sym $ Γ×A.intro≡ $ sym $ ΣPathP ((C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ fst $ PathPΣ $ Γ×A.β ⟩ ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ fst $ PathPΣ $ -×A.β ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ δ⋆γ≡γ' ⟩)
  --     , (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ snd $ PathPΣ $ Γ×A.β ⟩ ∙ (snd $ PathPΣ $ -×A.β))))
  --   ; F-id =
  --     λ {(Δ , Δᴰ , γ)} → ΣPathP ({!!} , (ΣPathPProp (λ _ → C.isSetHom _ _) {!!}))
  --   ; F-seq = {!!} }
  --   where
  --     module Γ×A = UniversalElementNotation Γ×A
  --     module -×A {Δ : C.ob} = UniversalElementNotation (Δ ×A)
  -- -- wkOb _×A π₁* Γ Γ×A .Functor.F-ob (Δ , Δᴰ , f) = (Δ ×A) .vertex , π₁* Δ Δᴰ .fst , {!Γ×A .intro!}
  -- -- wkOb _×A π₁* Γ Γ×A .Functor.F-hom = {!!}
  -- -- wkOb _×A π₁* Γ Γ×A .Functor.F-id = {!!}
  -- -- wkOb _×A π₁* Γ Γ×A .Functor.F-seq = {!!}

  -- isLR∀Ob : (A : C.ob) (_×A : BinProductsWith C A) → Type _
  -- isLR∀Ob A _×A = ∀ (Γ : C.ob) → Quadrable ((Γ ×A) .element .fst)

  -- -- -- TODO: double check to make sure this is the right definition, the
  -- -- -- reindPshᴰ is a little suspicious
  -- UniversalQuantifier : ∀ {Γ} A (_×A : BinProductsWith C A) (π₁* : isLR∀Ob A _×A) (Aᴰ : Cᴰ.ob[ (Γ ×A) .vertex ]) → Type _
  -- UniversalQuantifier {Γ} A _×A π₁* Aᴰ = Representableⱽ Cᴰ Γ $
  --   reindPsh (wkLR∀ Cᴰ ((C [-, A ]) , (_×A , (π₁* _))))    $
  --   reindPshᴰNatTrans (invPshIso (yoRecIso (Γ ×A)) .trans) $ -- ×-introF
  --   Cᴰ [-][-, Aᴰ ]

  -- module _ (bp : BinProducts C) where
  --   AllLR∀ : Type _
  --   AllLR∀ = ∀ (A Γ : C.ob) → Quadrable (bp (Γ , A) .element .fst)

  --   BinProducts+isFibration→AllLR∀ : isFibration → AllLR∀
  --   BinProducts+isFibration→AllLR∀ lifts A Γ yᴰ =
  --     lifts yᴰ (bp (Γ , A) .vertex) (bp (Γ , A) .element .fst)

  --   LR∀Ob : Type _
  --   LR∀Ob = Σ[ A ∈ C.ob ] isLR∀Ob A (λ c → bp (c , A))

  --   UniversalQuantifiers : AllLR∀ → Type _
  --   UniversalQuantifiers lr∀ = ∀ Γ A (Aᴰ : Cᴰ.ob[ bp (Γ , A) .vertex ]) → UniversalQuantifier A (λ c → bp (c , A))
  --     (lr∀ A)
  --     Aᴰ

  -- module LRⱽPresheafᴰNotation {P : Presheaf C ℓP} (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ) where
  --   private
  --     module P = PresheafNotation P
  --   open PresheafᴰNotation Cᴰ P (Pᴰ .fst)
  --   _×ⱽ_* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
  --   Γᴰ ×ⱽ p * = Pᴰ .snd Γᴰ p .fst

  --   introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
  --     → p[ γ P.⋆ p ][ Δᴰ ]
  --     → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
  --   introᴰ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ = Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .fst
  --     (γᴰ , γpᴰ)

  --   congP-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
  --     {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
  --     {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
  --     {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
  --     {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
  --     (γ≡γ' : γ ≡ γ')
  --     (γᴰ≡γᴰ' : γᴰ Cᴰ.≡[ γ≡γ' ] γᴰ')
  --     (γpᴰ≡γ'pᴰ : γpᴰ ≡[ (λ i → γ≡γ' i P.⋆ p) ] γ'pᴰ)
  --     → introᴰ γᴰ γpᴰ Cᴰ.≡[ γ≡γ' ] introᴰ γᴰ' γ'pᴰ
  --   congP-introᴰ γ≡γ' γᴰ≡γᴰ' γpᴰ≡γ'pᴰ = λ i → introᴰ (γᴰ≡γᴰ' i) (γpᴰ≡γ'pᴰ i)

  --   cong∫-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
  --     {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
  --     {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
  --     {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
  --     {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
  --     (γᴰ≡γᴰ' : Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
  --     (γpᴰ≡γ'pᴰ : γpᴰ ∫≡ γ'pᴰ)
  --     → Path (Cᴰ.Hom[ _ , _ ]) (_ , introᴰ γᴰ γpᴰ) (_ , introᴰ γᴰ' γ'pᴰ)
  --   cong∫-introᴰ γᴰ≡γᴰ' γpᴰ≡γ'pᴰ =
  --     Cᴰ.≡in $ congP-introᴰ (PathPΣ γᴰ≡γᴰ' .fst) (Cᴰ.≡out γᴰ≡γᴰ') (rectify $ ≡out $ γpᴰ≡γ'pᴰ)

  --   _⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
  --     → Cᴰ [ γ ][ Δᴰ , Γᴰ ]
  --   γᴰ ⋆π₁ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .fst

  --   ⟨_⟩⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
  --     → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
  --     → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
  --     → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
  --     → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ ⋆π₁ⱽ) (_ , γᴰ' ⋆π₁ⱽ))
  --   ⟨ γᴰ≡γᴰ' ⟩⋆π₁ⱽ i = (γᴰ≡γᴰ' i .fst) , (γᴰ≡γᴰ' i .snd ⋆π₁ⱽ)

  --   ⋆π₁ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
  --     → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
  --     → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , (δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₁ⱽ) (_ , δᴰ Cᴰ.⋆ᴰ (γᴰ ⋆π₁ⱽ))
  --   ⋆π₁ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
  --     ⟨ Cᴰ.reind-filler refl (δᴰ Cᴰ.⋆ᴰ γᴰ) ⟩⋆π₁ⱽ ∙ Cᴰ.≡in (cong fst (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , (λ i → δ C.⋆ γ)) _))
  --     ∙ (sym $ Cᴰ.reind-filler _ _)

  --   π₁ⱽ : ∀ {Γ Γᴰ p} → Cᴰ [ C.id {Γ} ][ Γᴰ ×ⱽ p * , Γᴰ ]
  --   π₁ⱽ = Cᴰ.idᴰ ⋆π₁ⱽ

  --   β₁ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
  --     → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ ⋆π₁ⱽ)) (_ , γᴰ)
  --   β₁ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
  --     Cᴰ.≡in $ cong fst $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ)

  --   β₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
  --     → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ Cᴰ.⋆ᴰ π₁ⱽ)) (_ , γᴰ)
  --   β₁ⱽ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
  --     (sym $ ⋆π₁ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ) ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₁ⱽ ∙ β₁ⱽ' γᴰ γpᴰ

  --   _⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
  --     → p[ γ P.⋆ p ][ Δᴰ ]
  --   γᴰ ⋆π₂ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .snd

  --   π₂ⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p} → p[ C.id P.⋆ p ][ Γᴰ ×ⱽ p * ]
  --   π₂ⱽ = Cᴰ.idᴰ ⋆π₂ⱽ

  --   ⟨_⟩⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
  --     → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
  --     → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
  --     → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
  --     → (γᴰ ⋆π₂ⱽ) ∫≡ (γᴰ' ⋆π₂ⱽ)
  --   ⟨ γᴰ≡γᴰ' ⟩⋆π₂ⱽ i = (γᴰ≡γᴰ' i .fst P.⋆ _) , (γᴰ≡γᴰ' i .snd ⋆π₂ⱽ)

  --   ⋆π₂ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
  --     → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
  --     → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
  --     → ((δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₂ⱽ) ∫≡ (δᴰ ⋆ᴰ (γᴰ ⋆π₂ⱽ))
  --   ⋆π₂ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
  --     ⟨ Cᴰ.reind-filler _ _ ⟩⋆π₂ⱽ
  --     ∙ (≡in $ (PathPΣ (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , refl) _)) .snd)
  --     ∙ ⋆ᴰ-reind _ _ _

  --   β₂ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
  --     → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
  --     → (introᴰ γᴰ γpᴰ ⋆π₂ⱽ) ∫≡ γpᴰ
  --   β₂ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
  --     ≡in $ snd $ PathPΣ (Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ))

  --   β₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
  --     → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
  --     → (introᴰ γᴰ γpᴰ ⋆ᴰ π₂ⱽ) ∫≡ γpᴰ
  --   β₂ⱽ γᴰ γpᴰ =
  --     sym (⋆π₂ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ)
  --     ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₂ⱽ
  --     ∙ β₂ⱽ' γᴰ γpᴰ

  --   ηⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
  --     → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ (γᴰ ⋆π₁ⱽ) (γᴰ ⋆π₂ⱽ)) (_ , γᴰ)
  --   ηⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ =
  --     Cᴰ.≡in $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .snd γᴰ

  --   introᴰ≡ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
  --     → {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
  --     → {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
  --     → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , γᴰ) (_ , (γᴰ' ⋆π₁ⱽ))
  --     → (γpᴰ ∫≡ (γᴰ' ⋆π₂ⱽ))
  --     → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ γᴰ γpᴰ) (_ , γᴰ')
  --   introᴰ≡ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {γ'} {p} {γᴰ} {γpᴰ} {γᴰ'} γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂ =
  --     cong∫-introᴰ γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂
  --     ∙ ηⱽ' γᴰ'
