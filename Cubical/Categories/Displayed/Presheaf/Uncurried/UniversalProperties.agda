{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory using (∫C)
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓCᴰᴰ ℓCᴰᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open isIso
open PshHom
open PshIso
open UniversalElementNotation

open UniversalElement
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  Terminalⱽ : ∀ (x : C.ob) → Type _
  Terminalⱽ x = Representableⱽ Cᴰ x UnitPshᴰ

  Terminalsⱽ : Type _
  Terminalsⱽ = ∀ x → Terminalⱽ x

  TerminalᴰSpec : Presheafᴰ UnitPsh Cᴰ ℓ-zero
  TerminalᴰSpec = UnitPshᴰ

  Terminalᴰ : ∀ (term : Terminal' C) → Type _
  Terminalᴰ = UniversalElementᴰ Cᴰ UnitPsh UnitPshᴰ

  module TerminalᴰNotation {term : Terminal' C} (termᴰ : Terminalᴰ term) = UniversalElementᴰNotation Cᴰ _ _ termᴰ

  Terminalⱽ→ᴰ : ∀ (term : Terminal' C) → Terminalⱽ (term .vertex) → Terminalᴰ term
  Terminalⱽ→ᴰ term termⱽ = Representableⱽ→UniversalElementᴰ Cᴰ UnitPsh UnitPshᴰ term
    (termⱽ .fst , termⱽ .snd ⋆PshIso (invPshIso $ reindPsh-Unit _))

  BinProductⱽSpec : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Presheafⱽ x Cᴰ (ℓ-max ℓCᴰ' ℓCᴰ')
  BinProductⱽSpec {x} xᴰ yᴰ = (Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ])

  BinProductⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ]))

  BinProductsWithⱽ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductsWithⱽ {x} xᴰ = ∀ Γᴰ → BinProductⱽ Γᴰ xᴰ

  BinProductsⱽ : Type _
  BinProductsⱽ = ∀ {x} xᴰ yᴰ → BinProductⱽ {x} xᴰ yᴰ

  module BinProductⱽNotation {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Aᴰ Bᴰ) where
    vert : Cᴰ.ob[ x ]
    vert = bpⱽ .fst

    private
      bp-ue = RepresentationPshIso→UniversalElement _
        (∫Representableⱽ Cᴰ _ _ bpⱽ)
      module ue = UniversalElementNotation bp-ue
      module spec = PresheafNotation
        (PresheafᴰNotation.∫ Cᴰ (C [-, x ]) (BinProductⱽSpec Aᴰ Bᴰ))

    π₁ : Cᴰ [ C.id ][ vert , Aᴰ ]
    π₁ = ue.element .snd .fst

    π₂ : Cᴰ [ C.id ][ vert , Bᴰ ]
    π₂ = ue.element .snd .snd

    infixr 4 _,ⱽ_
    _,ⱽ_ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
      → Cᴰ [ f ][ Γᴰ , Aᴰ ] → Cᴰ [ f ][ Γᴰ , Bᴰ ]
      → Cᴰ [ f ][ Γᴰ , vert ]
    _,ⱽ_ {f = f} fᴰ gᴰ = ue.intro (f , fᴰ , gᴰ) .snd

    -- Both projections' β laws in total-space (∫≡) form, sharing a single
    -- occurrence of the universal element's β, which is the expensive term.
    private
      ×βⱽ∫ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
        {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
        → (((fᴰ ,ⱽ gᴰ) Cᴰ.⋆ᴰ π₁) Cᴰ.∫≡ fᴰ)
        × (((fᴰ ,ⱽ gᴰ) Cᴰ.⋆ᴰ π₂) Cᴰ.∫≡ gᴰ)
      ×βⱽ∫ =
        (Cᴰ.reind-filler _ ∙ Cᴰ.≡in (βs .fst))
        , (Cᴰ.reind-filler _ ∙ Cᴰ.≡in (βs .snd))
        where
        βs = PathPΣ (PathPΣ ue.β .snd)

    ×βⱽ₁ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      → ((fᴰ ,ⱽ gᴰ) Cᴰ.⋆ᴰ π₁) Cᴰ.≡[ C.⋆IdR f ] fᴰ
    ×βⱽ₁ = Cᴰ.rectifyOut $ ×βⱽ∫ .fst

    ×βⱽ₂ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      → ((fᴰ ,ⱽ gᴰ) Cᴰ.⋆ᴰ π₂) Cᴰ.≡[ C.⋆IdR f ] gᴰ
    ×βⱽ₂ = Cᴰ.rectifyOut $ ×βⱽ∫ .snd

    ×ηⱽ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
      {hᴰ : Cᴰ [ f ][ Γᴰ , vert ]}
      → hᴰ Cᴰ.≡[ cong fst ue.η ]
          (ue.intro ((f , hᴰ) spec.⋆ ue.element) .snd)
    ×ηⱽ = PathPΣ ue.η .snd

  BinProductᴰ'Spec : ∀ {A B} → (A×B : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → Presheafⱽ (A×B .vertex) Cᴰ _
  BinProductᴰ'Spec {A}{B} A×B Aᴰ Bᴰ =
    reindPshᴰNatTrans (yoRec (C [-, A ]) (A×B .element .fst)) (Cᴰ [-][-, Aᴰ ]) ×ⱽPsh
    reindPshᴰNatTrans (yoRec (C [-, B ]) (A×B .element .snd)) (Cᴰ [-][-, Bᴰ ])

  BinProductᴰ' : ∀ {A B} → (A×B : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → Type _
  BinProductᴰ' {A}{B} A×B Aᴰ Bᴰ = Representableⱽ Cᴰ (A×B .vertex) (BinProductᴰ'Spec A×B Aᴰ Bᴰ)

  BinProductᴰSpec : ∀ {A B} → (A×B : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → Presheafᴰ ((C [-, A ]) ×Psh (C [-, B ])) Cᴰ (ℓ-max ℓCᴰ' ℓCᴰ')
  BinProductᴰSpec {A}{B} A×B Aᴰ Bᴰ = (Cᴰ [-][-, Aᴰ ]) ×ᴰPshStrict (Cᴰ [-][-, Bᴰ ])

  BinProductᴰ : ∀ {A B} → (A×B : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → Type _
  BinProductᴰ {A}{B} A×B Aᴰ Bᴰ = UniversalElementᴰ Cᴰ _ (BinProductᴰSpec A×B Aᴰ Bᴰ) A×B

  BinProductsWithᴰ : ∀ {A} (-×A : BinProductsWith C A) (Aᴰ : Cᴰ.ob[ A ]) → Type _
  BinProductsWithᴰ -×A Aᴰ = ∀ {B} (Bᴰ : Cᴰ.ob[ B ]) → BinProductᴰ (-×A B) Bᴰ Aᴰ

  BinProductsᴰ : (bp : BinProducts C) → Type _
  BinProductsᴰ bp = ∀ {A B} (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → BinProductᴰ (bp (A , B)) Aᴰ Bᴰ

  BinProductᴰ'Spec≅BinProductᴰSpec :
    ∀ {A B} (bp : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → FiberwisePshIsoᴰ (asPshIso bp .trans)
        (BinProductᴰ'Spec bp Aᴰ Bᴰ)
        (BinProductᴰSpec bp Aᴰ Bᴰ)
  BinProductᴰ'Spec≅BinProductᴰSpec {A} {B} bp Aᴰ Bᴰ =
    Isos→PshIso (λ _ → idIso) λ _ _ _ (aᴰ , bᴰ) →
      ΣPathP ( Cᴰ.rectifyOut (Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler _)
             , Cᴰ.rectifyOut (Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler _))

  BinProductⱽ→ᴰ : ∀ {A B} (bp : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → BinProductᴰ' bp Aᴰ Bᴰ
    → BinProductᴰ bp Aᴰ Bᴰ
  BinProductⱽ→ᴰ bp Aᴰ Bᴰ (Aᴰ×ᴰBᴰ , repr) =
    Representableⱽ→UniversalElementᴰ Cᴰ ((C [-, _ ]) ×Psh (C [-, _ ]))
      ((Cᴰ [-][-, Aᴰ ]) ×ᴰPshStrict (Cᴰ [-][-, Bᴰ ])) bp
      (Aᴰ×ᴰBᴰ , repr ⋆PshIsoⱽ BinProductᴰ'Spec≅BinProductᴰSpec bp Aᴰ Bᴰ)

  BinProductⱽ+π*→ᴰ : ∀ {A B} (bp : BinProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → (π₁*Aᴰ : CartesianLift Cᴰ (BinProductNotation.π₁ bp) Aᴰ)
    → (π₂*Bᴰ : CartesianLift Cᴰ (BinProductNotation.π₂ bp) Bᴰ)
    → BinProductⱽ (π₁*Aᴰ .fst) (π₂*Bᴰ .fst)
    → BinProductᴰ bp Aᴰ Bᴰ
  BinProductⱽ+π*→ᴰ bp Aᴰ Bᴰ π₁*Aᴰ π₂*Bᴰ bpᴰ = BinProductⱽ→ᴰ _ Aᴰ Bᴰ
    (bpᴰ ◁PshIsoⱽ ×PshIso (π₁*Aᴰ .snd) (π₂*Bᴰ .snd))

  module BinProductᴰNotation {A B Aᴰ Bᴰ} (A×B : BinProduct C (A , B)) (Aᴰ×ᴰBᴰ : BinProductᴰ A×B Aᴰ Bᴰ) where
    private
      module A×B = UniversalElementNotation A×B
    open UniversalElementᴰNotation Cᴰ _ _ Aᴰ×ᴰBᴰ public

    πᴰ₁ : Cᴰ [ ue.element .fst ][ Aᴰ×ᴰBᴰ .fst , Aᴰ ]
    πᴰ₁ = Aᴰ×ᴰBᴰ .snd .fst .fst

    πᴰ₂ : Cᴰ [ ue.element .snd ][ Aᴰ×ᴰBᴰ .fst , Bᴰ ]
    πᴰ₂ = Aᴰ×ᴰBᴰ .snd .fst .snd

    -- as ×βⱽ∫ above: one occurrence of `βᴰ` serves both projections
    private
      ×βᴰ∫ : ∀ {Γ Γᴰ}
        {f : C [ Γ , A ]}
        {g : C [ Γ , B ]}
        (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ])
        (gᴰ : Cᴰ [ g ][ Γᴰ , Bᴰ ])
        → ((introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₁) Cᴰ.∫≡ fᴰ)
        × ((introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₂) Cᴰ.∫≡ gᴰ)
      ×βᴰ∫ {Γ}{Γᴰ}{f}{g} fᴰ gᴰ =
        (Cᴰ.reind-filler _ ∙ Cᴰ.≡in (βs .fst))
        , (Cᴰ.reind-filler _ ∙ Cᴰ.≡in (βs .snd))
        where
        βs = PathPΣ (βᴰ {p = (f , g)} (fᴰ , gᴰ))

    ×βᴰ₁ : ∀ {Γ Γᴰ}
      {f : C [ Γ , A ]}
      {g : C [ Γ , B ]}
      (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ])
      (gᴰ : Cᴰ [ g ][ Γᴰ , Bᴰ ])
      → (introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₁) Cᴰ.≡[ PathPΣ (A×B.β {p = (f , g)}) .fst ] fᴰ
    ×βᴰ₁ {Γ}{Γᴰ}{f}{g} fᴰ gᴰ = Cᴰ.rectifyOut $ ×βᴰ∫ fᴰ gᴰ .fst

    ×βᴰ₂ : ∀ {Γ Γᴰ}
      {f : C [ Γ , A ]}
      {g : C [ Γ , B ]}
      (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ])
      (gᴰ : Cᴰ [ g ][ Γᴰ , Bᴰ ])
      → (introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₂) Cᴰ.≡[ PathPΣ (A×B.β {p = (f , g)}) .snd ] gᴰ
    ×βᴰ₂ {Γ}{Γᴰ}{f}{g} fᴰ gᴰ = Cᴰ.rectifyOut $ ×βᴰ∫ fᴰ gᴰ .snd

    ×ηᴰ : ∀ {Γ Γᴰ}
      → {f : C [ Γ , A×B .vertex ]}
      → (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ×ᴰBᴰ .fst ])
      → fᴰ Cᴰ.≡[ A×B.η {f = f} ] introᴰ ((fᴰ Cᴰ.⋆ᴰ πᴰ₁) , (fᴰ Cᴰ.⋆ᴰ πᴰ₂))
    ×ηᴰ {Γ} {Γᴰ} {f} fᴰ = Cᴰ.rectifyOut $
      Cᴰ.≡in (ηᴰ {f = f} fᴰ)
      ∙ cong (∫PshIsoᴰ (asReprᴰ .snd) .nIso _ .fst)
          (ΣPathPᴰ
              (sym $ Cᴰ.reind-filler _)
              (sym $ Cᴰ.reind-filler _))

  module BinProductsᴰNotation (bp : BinProducts C) (bpᴰ : BinProductsᴰ bp) where
    _×ᴰ_ : ∀ {A B} (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → Cᴰ.ob[ bp (A , B) .vertex ]
    Aᴰ ×ᴰ Bᴰ = bpᴰ Aᴰ Bᴰ .fst

    private
      module BPNotation {A : C.ob}{B : C.ob} {Aᴰ : Cᴰ.ob[ A ]}{Bᴰ : Cᴰ.ob[ B ]}
        = BinProductᴰNotation (bp (A , B)) (bpᴰ Aᴰ Bᴰ)
    open BPNotation public

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Cᴰᴰ : Categoryᴰ (∫C Cᴰ) ℓCᴰᴰ ℓCᴰᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Cᴰᴰ = Fibers Cᴰᴰ
    module ∫Cᴰ = Category (∫C Cᴰ)

  Terminalⱽᴰ : ∀ {x} → (termⱽ : Terminalⱽ Cᴰ x)
    → Type _
  Terminalⱽᴰ {x} termⱽ =
    Representableᴰ Cᴰᴰ _ UnitPshᴰ (∫Representableⱽ Cᴰ x UnitPshᴰ termⱽ)

  Terminalⱽ→ⱽᴰ : ∀ {x} (termⱽ : Terminalⱽ Cᴰ x)
    → Terminalⱽ Cᴰᴰ (x , termⱽ .fst)
    → Terminalⱽᴰ termⱽ
  Terminalⱽ→ⱽᴰ termⱽ termⱽⱽ .fst = termⱽⱽ .fst
  Terminalⱽ→ⱽᴰ termⱽ termⱽⱽ .snd =
    FiberwisePshIsoᴰ→PshIsoᴰ
      (termⱽⱽ .snd ⋆PshIso
        invPshIso (reindPsh-Unit (Idᴰ /Fⱽ
          (∫Representableⱽ Cᴰ _ UnitPshᴰ termⱽ .snd .trans))))

  module TerminalⱽᴰNotation {x} (termⱽ : Terminalⱽ Cᴰ x)
    (termⱽᴰ : Terminalⱽᴰ termⱽ) where
    private
      term-reprᴰ : RepresentationPshIso
        (PresheafᴰNotation.∫ Cᴰᴰ _ UnitPshᴰ)
      term-reprᴰ =
        ((x , termⱽ .fst) , termⱽᴰ .fst) ,
        (invPshIso (∫Repr-iso Cᴰᴰ) ⋆PshIso ∫PshIsoᴰ (termⱽᴰ .snd))
      term-ueᴰ = RepresentationPshIso→UniversalElement _ term-reprᴰ
      module termᴰ = UniversalElementNotation term-ueᴰ

    vertexᴰ : Cᴰᴰ.ob[ x , termⱽ .fst ]
    vertexᴰ = termⱽᴰ .fst

    !ⱽᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      → Cᴰᴰ [ f , termᴰ.intro {c = ( (Γ , Γᴰ) , Γᴰᴰ )}
          ((f , tt) , tt) .fst .snd ][ Γᴰᴰ , vertexᴰ ]
    !ⱽᴰ {Γ = Γ} {Γᴰ = Γᴰ} {Γᴰᴰ = Γᴰᴰ} {f = f} =
      termᴰ.intro {c = ( (Γ , Γᴰ) , Γᴰᴰ )} ((f , tt) , tt) .snd

    private
      !η-genericᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
        {f : C [ Γ , x ]} {fᴰ : Cᴰ [ f ][ Γᴰ , termⱽ .fst ]}
        (η : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , termⱽ .fst) ]
          (f , fᴰ)
          (termᴰ.intro {c = ((Γ , Γᴰ) , Γᴰᴰ)} ((f , tt) , tt) .fst))
        (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , vertexᴰ ])
        → PathP (λ i → Cᴰᴰ [ η i ][ Γᴰᴰ , vertexᴰ ]) fᴰᴰ !ⱽᴰ
      !η-genericᴰ {Γ = Γ} {Γᴰ = Γᴰ} {f = f} {fᴰ = fᴰ} η fᴰᴰ =
        symP $ Cᴰᴰ.rectify {e' = sym η} $
          termⱽᴰ .snd .snd (Γ , Γᴰ) _ .isIsoOver.leftInv (f , fᴰ) fᴰᴰ

    !ηⱽᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]} {fᴰ : Cᴰ [ f ][ Γᴰ , termⱽ .fst ]}
      {g : ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , termⱽ .fst) ]}
      (intro≡g : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , termⱽ .fst) ]
        (termᴰ.intro {c = ((Γ , Γᴰ) , Γᴰᴰ)} ((f , tt) , tt) .fst) g)
      (η : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , termⱽ .fst) ] (f , fᴰ) g)
      (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , vertexᴰ ])
      → PathP (λ i → Cᴰᴰ [ η i ][ Γᴰᴰ , vertexᴰ ])
          fᴰᴰ (Cᴰᴰ.reind intro≡g !ⱽᴰ)
    !ηⱽᴰ {Γ = Γ} {Γᴰ = Γᴰ} {f = f} {fᴰ = fᴰ} intro≡g η fᴰᴰ =
      Cᴰᴰ.rectifyOut {e' = η}
        ((Cᴰᴰ.≡in (!η-genericᴰ (η ∙ sym intro≡g) fᴰᴰ))
        ∙ Cᴰᴰ.reind-filler {p = !ⱽᴰ} intro≡g)

  BinProductⱽᴰSpec : ∀ {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    (Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]) (Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ])
    → Presheafᴰᴰ (BinProductⱽSpec Cᴰ Aᴰ Bᴰ) Cᴰᴰ _
  BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ =
    reindPshᴰNatTrans (∫Repr-iso Cᴰ .trans) (Cᴰᴰ [-][-, Aᴰᴰ ])
    ×ⱽᴰPsh
    reindPshᴰNatTrans (∫Repr-iso Cᴰ .trans) (Cᴰᴰ [-][-, Bᴰᴰ ])

  BinProductⱽᴰ : ∀ {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    (Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]) (Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ]) → Type _
  BinProductⱽᴰ bpⱽ Aᴰᴰ Bᴰᴰ =
    Representableᴰ Cᴰᴰ _ (BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ)
      (∫Representableⱽ Cᴰ _ _ bpⱽ)

  BinProductⱽᴰ'Spec : ∀ {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    (Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]) (Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ])
    → Presheafⱽ (x , BinProductⱽNotation.vert Cᴰ bpⱽ) Cᴰᴰ _
  BinProductⱽᴰ'Spec bpⱽ Aᴰᴰ Bᴰᴰ =
    CartesianLiftPshSpec ((∫C Cᴰ) [-, _ , _ ]) Cᴰᴰ
      (Cᴰᴰ [-][-, Aᴰᴰ ]) (C.id , BinProductⱽNotation.π₁ Cᴰ bpⱽ)
    ×ⱽPsh
    CartesianLiftPshSpec ((∫C Cᴰ) [-, _ , _ ]) Cᴰᴰ
      (Cᴰᴰ [-][-, Bᴰᴰ ]) (C.id , BinProductⱽNotation.π₂ Cᴰ bpⱽ)

  BinProductⱽᴰ'Spec≅BinProductⱽᴰSpec : ∀ {x}
    {Aᴰ Bᴰ : Cᴰ.ob[ x ]} (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    (Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]) (Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ])
    → PshIsoⱽ (BinProductⱽᴰ'Spec bpⱽ Aᴰᴰ Bᴰᴰ)
        (reindPshᴰNatTrans
          (∫Representableⱽ Cᴰ _ _ bpⱽ .snd .trans)
          (BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ))
  BinProductⱽᴰ'Spec≅BinProductⱽᴰSpec {x = x} {Aᴰ = Aᴰ} {Bᴰ = Bᴰ}
    bpⱽ Aᴰᴰ Bᴰᴰ =
    ×PshIso
      (reindPshᴰNatTrans-factorStrict _ _ _ _ _
        (makePshHomPath $ funExt λ (Γ , Γᴰ) → funExt λ (f , hᴰ) → π₁-natural hᴰ))
      (reindPshᴰNatTrans-factorStrict _ _ _ _ _
        (makePshHomPath $ funExt λ (Γ , Γᴰ) → funExt λ (f , hᴰ) → π₂-natural hᴰ))
    ⋆PshIso invPshIso (reindPsh× _ _ _)
    where
    module bp = BinProductⱽNotation Cᴰ bpⱽ
    -- Both projections read off the same naturality square of bpⱽ's
    -- representation iso, applied to the same identity coercion, so the
    -- pair of them is stated once here.
    module _ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {f : C [ Γ , x ]}
      (hᴰ : Cᴰ [ f ][ Γᴰ , bp.vert ]) where
      private
        natural = bpⱽ .snd .trans .N-hom
          (Γ , Γᴰ , f) (x , bp.vert , C.id)
          (f , hᴰ , C.⋆IdR f) Cᴰ.idᴰ
        ⋆id = Cᴰ.rectifyOut {e' = refl}
          (Cᴰ.reind-filler⁻ _ ∙ Cᴰ.⋆IdR (f , hᴰ))
      π₁-natural : Path (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Aᴰ ])
          (f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bp.π₁)
          (f , bpⱽ .snd .trans .N-ob (Γ , Γᴰ , f) hᴰ .fst)
      π₁-natural =
        Cᴰ.reind-filler _
        ∙ cong (f ,_) (sym (cong fst natural))
        ∙ cong (λ z → f , bpⱽ .snd .trans .N-ob (Γ , Γᴰ , f) z .fst) ⋆id
      π₂-natural : Path (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Bᴰ ])
          (f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bp.π₂)
          (f , bpⱽ .snd .trans .N-ob (Γ , Γᴰ , f) hᴰ .snd)
      π₂-natural =
        Cᴰ.reind-filler _
        ∙ cong (f ,_) (sym (cong snd natural))
        ∙ cong (λ z → f , bpⱽ .snd .trans .N-ob (Γ , Γᴰ , f) z .snd) ⋆id

  BinProductⱽ+π*→ⱽᴰ : ∀ {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    (Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]) (Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ])
    → (π₁*Aᴰᴰ : CartesianLift Cᴰᴰ
        (C.id , BinProductⱽNotation.π₁ Cᴰ bpⱽ) Aᴰᴰ)
    → (π₂*Bᴰᴰ : CartesianLift Cᴰᴰ
        (C.id , BinProductⱽNotation.π₂ Cᴰ bpⱽ) Bᴰᴰ)
    → BinProductⱽ Cᴰᴰ (π₁*Aᴰᴰ .fst) (π₂*Bᴰᴰ .fst)
    → BinProductⱽᴰ bpⱽ Aᴰᴰ Bᴰᴰ
  BinProductⱽ+π*→ⱽᴰ bpⱽ Aᴰᴰ Bᴰᴰ π₁*Aᴰᴰ π₂*Bᴰᴰ bpⱽⱽ .fst =
    bpⱽⱽ .fst
  BinProductⱽ+π*→ⱽᴰ bpⱽ Aᴰᴰ Bᴰᴰ π₁*Aᴰᴰ π₂*Bᴰᴰ bpⱽⱽ .snd =
    FiberwisePshIsoᴰ→PshIsoᴰ
      (bpⱽⱽ .snd ⋆PshIso
        ×PshIso (π₁*Aᴰᴰ .snd) (π₂*Bᴰᴰ .snd)
      ⋆PshIso BinProductⱽᴰ'Spec≅BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ)

  module BinProductⱽᴰNotation {x} {Aᴰ Bᴰ : Cᴰ.ob[ x ]}
    (bpⱽ : BinProductⱽ Cᴰ Aᴰ Bᴰ)
    {Aᴰᴰ : Cᴰᴰ.ob[ x , Aᴰ ]} {Bᴰᴰ : Cᴰᴰ.ob[ x , Bᴰ ]}
    (bpⱽᴰ : BinProductⱽᴰ bpⱽ Aᴰᴰ Bᴰᴰ) where
    private
      module bpⱽ = BinProductⱽNotation Cᴰ bpⱽ
      bp-reprᴰ : RepresentationPshIso
        (PresheafᴰNotation.∫ Cᴰᴰ _ (BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ))
      bp-reprᴰ =
        ((x , bpⱽ.vert) , bpⱽᴰ .fst) ,
        (invPshIso (∫Repr-iso Cᴰᴰ) ⋆PshIso ∫PshIsoᴰ (bpⱽᴰ .snd))
      bp-ueᴰ = RepresentationPshIso→UniversalElement _ bp-reprᴰ
      module bpᴰ = UniversalElementNotation bp-ueᴰ
      module specᴰ = PresheafNotation
        (PresheafᴰNotation.∫ Cᴰᴰ _ (BinProductⱽᴰSpec bpⱽ Aᴰᴰ Bᴰᴰ))

    vertexᴰ : Cᴰᴰ.ob[ x , bpⱽ.vert ]
    vertexᴰ = bpⱽᴰ .fst

    πᴰ₁ : Cᴰᴰ [ C.id , bpⱽ.π₁ ][ vertexᴰ , Aᴰᴰ ]
    πᴰ₁ = bpᴰ.element .snd .fst

    πᴰ₂ : Cᴰᴰ [ C.id , bpⱽ.π₂ ][ vertexᴰ , Bᴰᴰ ]
    πᴰ₂ = bpᴰ.element .snd .snd

    infixr 4 _,ⱽᴰ_
    _,ⱽᴰ_ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      → Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ] → Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ]
      → Cᴰᴰ [ f , (fᴰ bpⱽ.,ⱽ gᴰ) ][ Γᴰᴰ , vertexᴰ ]
    _,ⱽᴰ_ {f = f} {fᴰ = fᴰ} {gᴰ = gᴰ} fᴰᴰ gᴰᴰ =
      bpᴰ.intro ((f , fᴰ , gᴰ) , fᴰᴰ , gᴰᴰ) .snd

    -- Both projections' β laws, stated once against ∫≡ (the total-space
    -- view). bpᴰ.β -- the universal-element β at the ∫-presheaf of the
    -- BinProductⱽᴰ spec -- is by a wide margin the most expensive term in
    -- this file, so it is shared by the pair, and the reind crossing that
    -- the spec presheaf's action introduces is paid here once.
    private
      ×βⱽᴰ∫ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
        {f : C [ Γ , x ]}
        {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
        (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ]) (gᴰᴰ : Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ])
        → (((fᴰᴰ ,ⱽᴰ gᴰᴰ) Cᴰᴰ.⋆ᴰ πᴰ₁) Cᴰᴰ.∫≡ fᴰᴰ)
        × (((fᴰᴰ ,ⱽᴰ gᴰᴰ) Cᴰᴰ.⋆ᴰ πᴰ₂) Cᴰᴰ.∫≡ gᴰᴰ)
      ×βⱽᴰ∫ fᴰᴰ gᴰᴰ =
        (Cᴰᴰ.reind-filler _ ∙ Cᴰᴰ.≡in (βs .fst))
        , (Cᴰᴰ.reind-filler _ ∙ Cᴰᴰ.≡in (βs .snd))
        where
        βs = PathPΣ (PathPΣ bpᴰ.β .snd)

    ×βⱽᴰ₁ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ]) (gᴰᴰ : Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ])
      → ((fᴰᴰ ,ⱽᴰ gᴰᴰ) Cᴰᴰ.⋆ᴰ πᴰ₁)
        Cᴰᴰ.≡[ Cᴰ.≡in bpⱽ.×βⱽ₁ ] fᴰᴰ
    ×βⱽᴰ₁ fᴰᴰ gᴰᴰ = Cᴰᴰ.rectifyOut $ ×βⱽᴰ∫ fᴰᴰ gᴰᴰ .fst

    ×βⱽᴰ₂ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ]) (gᴰᴰ : Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ])
      → ((fᴰᴰ ,ⱽᴰ gᴰᴰ) Cᴰᴰ.⋆ᴰ πᴰ₂)
        Cᴰᴰ.≡[ Cᴰ.≡in bpⱽ.×βⱽ₂ ] gᴰᴰ
    ×βⱽᴰ₂ fᴰᴰ gᴰᴰ = Cᴰᴰ.rectifyOut $ ×βⱽᴰ∫ fᴰᴰ gᴰᴰ .snd

    ×βⱽᴰ₁-on : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      {π' : ∫Cᴰ.Hom[ (x , bpⱽ.vert) , (x , Aᴰ) ]}
      (π≡π' : Path ∫Cᴰ.Hom[ (x , bpⱽ.vert) , (x , Aᴰ) ]
        (C.id , bpⱽ.π₁) π')
      (β' : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , Aᴰ) ]
        ((f , fᴰ bpⱽ.,ⱽ gᴰ) ∫Cᴰ.⋆ π') (f , fᴰ))
      (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ])
      (gᴰᴰ : Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ])
      → PathP (λ i → Cᴰᴰ [ β' i ][ Γᴰᴰ , Aᴰᴰ ])
          ((Cᴰᴰ.reind (ΣPathP (refl , refl)) (fᴰᴰ ,ⱽᴰ gᴰᴰ))
            Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind π≡π' πᴰ₁) fᴰᴰ
    ×βⱽᴰ₁-on π≡π' β' fᴰᴰ gᴰᴰ = Cᴰᴰ.rectifyOut {e' = β'} $
      Cᴰᴰ.⟨ Cᴰᴰ.reind-filler⁻ (ΣPathP (refl , refl)) ⟩⋆⟨⟩
      ∙ Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler⁻ π≡π' ⟩
      ∙ ×βⱽᴰ∫ fᴰᴰ gᴰᴰ .fst

    ×βⱽᴰ₂-on : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]}
      {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {gᴰ : Cᴰ [ f ][ Γᴰ , Bᴰ ]}
      {π' : ∫Cᴰ.Hom[ (x , bpⱽ.vert) , (x , Bᴰ) ]}
      (π≡π' : Path ∫Cᴰ.Hom[ (x , bpⱽ.vert) , (x , Bᴰ) ]
        (C.id , bpⱽ.π₂) π')
      (β' : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , Bᴰ) ]
        ((f , fᴰ bpⱽ.,ⱽ gᴰ) ∫Cᴰ.⋆ π') (f , gᴰ))
      (fᴰᴰ : Cᴰᴰ [ f , fᴰ ][ Γᴰᴰ , Aᴰᴰ ])
      (gᴰᴰ : Cᴰᴰ [ f , gᴰ ][ Γᴰᴰ , Bᴰᴰ ])
      → PathP (λ i → Cᴰᴰ [ β' i ][ Γᴰᴰ , Bᴰᴰ ])
          ((Cᴰᴰ.reind (ΣPathP (refl , refl)) (fᴰᴰ ,ⱽᴰ gᴰᴰ))
            Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind π≡π' πᴰ₂) gᴰᴰ
    ×βⱽᴰ₂-on π≡π' β' fᴰᴰ gᴰᴰ = Cᴰᴰ.rectifyOut {e' = β'} $
      Cᴰᴰ.⟨ Cᴰᴰ.reind-filler⁻ (ΣPathP (refl , refl)) ⟩⋆⟨⟩
      ∙ Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler⁻ π≡π' ⟩
      ∙ ×βⱽᴰ∫ fᴰᴰ gᴰᴰ .snd

    -- as ×βⱽᴰ∫ above: bpᴰ.η is stated once in total-space (∫≡) form and
    -- rectified at whichever index each consumer below needs.
    private
      ×ηⱽᴰ∫ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
        {f : C [ Γ , x ]} {hᴰ : Cᴰ [ f ][ Γᴰ , bpⱽ.vert ]}
        (hᴰᴰ : Cᴰᴰ [ f , hᴰ ][ Γᴰᴰ , vertexᴰ ])
        → hᴰᴰ Cᴰᴰ.∫≡
            (bpᴰ.intro (((f , hᴰ) , hᴰᴰ) specᴰ.⋆ bpᴰ.element) .snd)
      ×ηⱽᴰ∫ {f = f} {hᴰ = hᴰ} hᴰᴰ = bpᴰ.η {f = ((f , hᴰ) , hᴰᴰ)}

    ×ηⱽᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]} {hᴰ : Cᴰ [ f ][ Γᴰ , bpⱽ.vert ]}
      (hᴰᴰ : Cᴰᴰ [ f , hᴰ ][ Γᴰᴰ , vertexᴰ ])
      → hᴰᴰ Cᴰᴰ.≡[ Cᴰ.≡in bpⱽ.×ηⱽ ]
          (bpᴰ.intro (((f , hᴰ) , hᴰᴰ) specᴰ.⋆ bpᴰ.element) .snd)
    ×ηⱽᴰ hᴰᴰ = Cᴰᴰ.rectifyOut $ ×ηⱽᴰ∫ hᴰᴰ

    -- Assemble the path in the doubly-nested Σ that bpᴰ.intro consumes out
    -- of its two component paths, rectifying the second component's index
    -- along the first.
    -- The implicits are the components rather than the Σs on purpose:
    -- stating it with {z z' : Σ …} and projecting makes the use sites solve
    -- w .fst, which is not a pattern.
    private
      pairΣᴰᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
        {g g' : C [ Γ , x ]}
        {a : Cᴰ [ g ][ Γᴰ , Aᴰ ]} {b : Cᴰ [ g ][ Γᴰ , Bᴰ ]}
        {a' : Cᴰ [ g' ][ Γᴰ , Aᴰ ]} {b' : Cᴰ [ g' ][ Γᴰ , Bᴰ ]}
        {u : Cᴰᴰ [ g , a ][ Γᴰᴰ , Aᴰᴰ ]} {v : Cᴰᴰ [ g , b ][ Γᴰᴰ , Bᴰᴰ ]}
        {u' : Cᴰᴰ [ g' , a' ][ Γᴰᴰ , Aᴰᴰ ]} {v' : Cᴰᴰ [ g' , b' ][ Γᴰᴰ , Bᴰᴰ ]}
        → Path (Σ[ ga ∈ (Σ[ h ∈ C [ Γ , x ] ] Cᴰ [ h ][ Γᴰ , Aᴰ ]) ]
                 Cᴰᴰ [ ga .fst , ga .snd ][ Γᴰᴰ , Aᴰᴰ ])
            ((g , a) , u) ((g' , a') , u')
        → Path (Σ[ gb ∈ (Σ[ h ∈ C [ Γ , x ] ] Cᴰ [ h ][ Γᴰ , Bᴰ ]) ]
                 Cᴰᴰ [ gb .fst , gb .snd ][ Γᴰᴰ , Bᴰᴰ ])
            ((g , b) , v) ((g' , b') , v')
        → Path (Σ[ y ∈ (Σ[ h ∈ C [ Γ , x ] ]
                 (Cᴰ [ h ][ Γᴰ , Aᴰ ] × Cᴰ [ h ][ Γᴰ , Bᴰ ])) ]
                 (Cᴰᴰ [ y .fst , y .snd .fst ][ Γᴰᴰ , Aᴰᴰ ] ×
                  Cᴰᴰ [ y .fst , y .snd .snd ][ Γᴰᴰ , Bᴰᴰ ]))
            ((g , a , b) , u , v) ((g' , a' , b') , u' , v')
      pairΣᴰᴰ c₁ c₂ i =
        let e₁ = cong fst c₁
            e₂ = cong fst c₂
            e₂' = λ j → e₁ j .fst , Cᴰ.rectifyOut {e' = cong fst e₁} e₂ j
            p₁ = Cᴰᴰ.rectifyOut {e' = e₁} c₁
            p₂ = Cᴰᴰ.rectifyOut {e' = e₂'} c₂
        in ((e₁ i .fst , e₁ i .snd , e₂' i .snd) , p₁ i , p₂ i)

    ×ηⱽᴰ-on : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {Γᴰᴰ : Cᴰᴰ.ob[ Γ , Γᴰ ]}
      {f : C [ Γ , x ]} {hᴰ : Cᴰ [ f ][ Γᴰ , bpⱽ.vert ]}
      {π₁' : Cᴰ [ C.id ][ bpⱽ.vert , Aᴰ ]}
      {π₂' : Cᴰ [ C.id ][ bpⱽ.vert , Bᴰ ]}
      (π₁≡π₁' : bpⱽ.π₁ ≡ π₁')
      (π₂≡π₂' : bpⱽ.π₂ ≡ π₂')
      (η' : Path ∫Cᴰ.Hom[ (Γ , Γᴰ) , (x , bpⱽ.vert) ]
        (f , hᴰ)
        (f C.⋆ C.id , (hᴰ Cᴰ.⋆ᴰ π₁') bpⱽ.,ⱽ (hᴰ Cᴰ.⋆ᴰ π₂')))
      (hᴰᴰ : Cᴰᴰ [ f , hᴰ ][ Γᴰᴰ , vertexᴰ ])
      → PathP (λ i → Cᴰᴰ [ η' i ][ Γᴰᴰ , vertexᴰ ]) hᴰᴰ
          (Cᴰᴰ.reind (ΣPathP (refl , refl))
            ((hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind (ΣPathP (refl , π₁≡π₁')) πᴰ₁) ,ⱽᴰ
             (hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind (ΣPathP (refl , π₂≡π₂')) πᴰ₂)))
    ×ηⱽᴰ-on {Γ = Γ} {Γᴰ = Γᴰ} {Γᴰᴰ = Γᴰᴰ} {f = f} {hᴰ = hᴰ}
      {π₁' = π₁'} {π₂' = π₂'} π₁≡π₁' π₂≡π₂' η' hᴰᴰ = Cᴰᴰ.rectifyOut {e' = η'} $
      ×ηⱽᴰ∫ hᴰᴰ
      ∙ cong bpᴰ.intro (pairΣᴰᴰ (q₁ ∙ r₁) (q₂ ∙ r₂))
      ∙ Cᴰᴰ.reind-filler (ΣPathP (refl , refl))
      where
      q₁ :
        let s = (((f , hᴰ) , hᴰᴰ) specᴰ.⋆ bpᴰ.element)
        in Path (Σ[ ga ∈ (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Aᴰ ]) ]
             Cᴰᴰ [ ga .fst , ga .snd ][ Γᴰᴰ , Aᴰᴰ ])
             ((s .fst .fst , s .fst .snd .fst) , s .snd .fst)
             ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bpⱽ.π₁) , hᴰᴰ Cᴰᴰ.⋆ᴰ πᴰ₁)
      q₁ = sym (Cᴰᴰ.reind-filler _)
      q₂ :
        let s = (((f , hᴰ) , hᴰᴰ) specᴰ.⋆ bpᴰ.element)
        in Path (Σ[ gb ∈ (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Bᴰ ]) ]
             Cᴰᴰ [ gb .fst , gb .snd ][ Γᴰᴰ , Bᴰᴰ ])
             ((s .fst .fst , s .fst .snd .snd) , s .snd .snd)
             ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bpⱽ.π₂) , hᴰᴰ Cᴰᴰ.⋆ᴰ πᴰ₂)
      q₂ = sym (Cᴰᴰ.reind-filler _)
      r₁ : Path
        (Σ[ ga ∈ (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Aᴰ ]) ]
          Cᴰᴰ [ ga .fst , ga .snd ][ Γᴰᴰ , Aᴰᴰ ])
        ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bpⱽ.π₁) , hᴰᴰ Cᴰᴰ.⋆ᴰ πᴰ₁)
        ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ π₁') ,
          hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind (ΣPathP (refl , π₁≡π₁')) πᴰ₁)
      r₁ = Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler (ΣPathP (refl , π₁≡π₁')) ⟩
      r₂ : Path
        (Σ[ gb ∈ (Σ[ g ∈ C [ Γ , x ] ] Cᴰ [ g ][ Γᴰ , Bᴰ ]) ]
          Cᴰᴰ [ gb .fst , gb .snd ][ Γᴰᴰ , Bᴰᴰ ])
        ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ bpⱽ.π₂) , hᴰᴰ Cᴰᴰ.⋆ᴰ πᴰ₂)
        ((f C.⋆ C.id , hᴰ Cᴰ.⋆ᴰ π₂') ,
          hᴰᴰ Cᴰᴰ.⋆ᴰ Cᴰᴰ.reind (ΣPathP (refl , π₂≡π₂')) πᴰ₂)
      r₂ = Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler (ΣPathP (refl , π₂≡π₂')) ⟩

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Cᴰᴰ : Categoryᴰ (∫C Cᴰ) ℓCᴰᴰ ℓCᴰᴰ') where

  Initialⱽᴰ : ∀ {x} → (initⱽ : Terminalⱽ (Cᴰ ^opᴰ) x) → Type _
  Initialⱽᴰ = Terminalⱽᴰ (Cᴰᴰ ^opᴰᴰ)

  module InitialⱽᴰNotation {x} (initⱽ : Terminalⱽ (Cᴰ ^opᴰ) x)
    (initⱽᴰ : Initialⱽᴰ initⱽ) =
    TerminalⱽᴰNotation (Cᴰᴰ ^opᴰᴰ) initⱽ initⱽᴰ renaming
      (!ⱽᴰ to ¡ⱽᴰ ; !ηⱽᴰ to ¡ηⱽᴰ)

  BinCoProductⱽᴰ : ∀ {x} {Aᴰ Bᴰ : Categoryᴰ.ob[_] Cᴰ x}
    (bcpⱽ : BinProductⱽ (Cᴰ ^opᴰ) Aᴰ Bᴰ)
    (Aᴰᴰ : Categoryᴰ.ob[_] Cᴰᴰ (x , Aᴰ))
    (Bᴰᴰ : Categoryᴰ.ob[_] Cᴰᴰ (x , Bᴰ)) → Type _
  BinCoProductⱽᴰ = BinProductⱽᴰ (Cᴰᴰ ^opᴰᴰ)

  module BinCoProductⱽᴰNotation {x} {Aᴰ Bᴰ : Categoryᴰ.ob[_] Cᴰ x}
    (bcpⱽ : BinProductⱽ (Cᴰ ^opᴰ) Aᴰ Bᴰ)
    {Aᴰᴰ : Categoryᴰ.ob[_] Cᴰᴰ (x , Aᴰ)}
    {Bᴰᴰ : Categoryᴰ.ob[_] Cᴰᴰ (x , Bᴰ)}
    (bcpⱽᴰ : BinCoProductⱽᴰ bcpⱽ Aᴰᴰ Bᴰᴰ) =
    BinProductⱽᴰNotation (Cᴰᴰ ^opᴰᴰ) bcpⱽ bcpⱽᴰ renaming
      (πᴰ₁ to σᴰ₁ ; πᴰ₂ to σᴰ₂ ; _,ⱽᴰ_ to [_,ⱽᴰ_] ;
       ×βⱽᴰ₁ to +βⱽᴰ₁ ; ×βⱽᴰ₂ to +βⱽᴰ₂ ; ×ηⱽᴰ to +ηⱽᴰ ;
       ×βⱽᴰ₁-on to +βⱽᴰ₁-on ; ×βⱽᴰ₂-on to +βⱽᴰ₂-on ;
       ×ηⱽᴰ-on to +ηⱽᴰ-on)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    Cᴰop = Cᴰ ^opᴰ
    module Cᴰop = Fibers Cᴰop

  Initialⱽ : ∀ (x : C.ob) → Type _
  Initialⱽ x = Terminalⱽ Cᴰop x

  Initialsⱽ : Type _
  Initialsⱽ = Terminalsⱽ Cᴰop

  Initialᴰ : ∀ (init : Terminal' (C ^op)) → Type _
  Initialᴰ = Terminalᴰ Cᴰop

  BinCoProductⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  BinCoProductⱽ = BinProductⱽ Cᴰop

  BinCoProductsWithⱽ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  BinCoProductsWithⱽ = BinProductsWithⱽ Cᴰop

  BinCoProductsⱽ : Type _
  BinCoProductsⱽ = BinProductsⱽ Cᴰop

  BinCoProductᴰ' : ∀ {A B} →
    (A+B : BinCoProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → Type _
  BinCoProductᴰ' = BinProductᴰ' Cᴰop

  BinCoProductᴰ : ∀ {A B} → (A+B : BinCoProduct C (A , B)) (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ]) → Type _
  BinCoProductᴰ = BinProductᴰ Cᴰop

  BinCoProductsᴰ : (bcp : BinCoProducts C) → Type _
  BinCoProductsᴰ = BinProductsᴰ Cᴰop

  BinCoproductⱽ→ᴰ : ∀ {A B} (bcp : BinCoProduct C (A , B))
    (Aᴰ : Cᴰ.ob[ A ]) (Bᴰ : Cᴰ.ob[ B ])
    → BinCoProductᴰ' bcp Aᴰ Bᴰ
    → BinCoProductᴰ bcp Aᴰ Bᴰ
  BinCoproductⱽ→ᴰ = BinProductⱽ→ᴰ Cᴰop

  module BinCoProductᴰNotation {A B Aᴰ Bᴰ} (A+B : BinCoProduct C (A , B))
    (Aᴰ+ᴰBᴰ : BinCoProductᴰ A+B Aᴰ Bᴰ) =
    BinProductᴰNotation Cᴰop A+B Aᴰ+ᴰBᴰ renaming
      (πᴰ₁ to σᴰ₁ ; πᴰ₂ to σᴰ₂)

  module BinCoProductsᴰNotation (bcp : BinCoProducts C) (bcpᴰ : BinCoProductsᴰ bcp)
    = BinProductsᴰNotation Cᴰop bcp bcpᴰ renaming (_×ᴰ_ to _+ᴰ_)
