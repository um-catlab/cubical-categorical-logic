{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom
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
  module TerminalᴰNotation {term : Terminal' C}(termᴰ : Terminalᴰ term) where
    open UniversalElementᴰNotation Cᴰ _ _ termᴰ public

  module BinProductᴰNotation {A B Aᴰ Bᴰ} (A×B : BinProduct C (A , B)) (Aᴰ×ᴰBᴰ : BinProductᴰ A×B Aᴰ Bᴰ) where
    private
      module A×B = UniversalElementNotation A×B
    open UniversalElementᴰNotation Cᴰ _ _ Aᴰ×ᴰBᴰ public

    πᴰ₁ : Cᴰ [ ue.element .fst ][ Aᴰ×ᴰBᴰ .fst , Aᴰ ]
    πᴰ₁ = Aᴰ×ᴰBᴰ .snd .fst .fst

    πᴰ₂ : Cᴰ [ ue.element .snd ][ Aᴰ×ᴰBᴰ .fst , Bᴰ ]
    πᴰ₂ = Aᴰ×ᴰBᴰ .snd .fst .snd

    ×βᴰ₁ : ∀ {Γ Γᴰ}
      {f : C [ Γ , A ]}
      {g : C [ Γ , B ]}
      (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ])
      (gᴰ : Cᴰ [ g ][ Γᴰ , Bᴰ ])
      → (introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₁) Cᴰ.≡[ PathPΣ (A×B.β {p = (f , g)}) .fst ] fᴰ
    ×βᴰ₁ {Γ}{Γᴰ}{f}{g} fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      Cᴰ.reind-filler _ ∙ (Cᴰ.≡in $ PathPΣ (βᴰ {p = (f , g)} (fᴰ , gᴰ)) .fst)

    ×βᴰ₂ : ∀ {Γ Γᴰ}
      {f : C [ Γ , A ]}
      {g : C [ Γ , B ]}
      (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ])
      (gᴰ : Cᴰ [ g ][ Γᴰ , Bᴰ ])
      → (introᴰ (fᴰ , gᴰ) Cᴰ.⋆ᴰ πᴰ₂) Cᴰ.≡[ PathPΣ (A×B.β {p = (f , g)}) .snd ] gᴰ
    ×βᴰ₂ {Γ}{Γᴰ}{f}{g} fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      Cᴰ.reind-filler _ ∙ (Cᴰ.≡in $ PathPΣ (βᴰ {p = (f , g)} (fᴰ , gᴰ)) .snd)

    ×ηᴰ : ∀ {Γ Γᴰ}
      → {f : C [ Γ , A×B .vertex ]}
      → (fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ×ᴰBᴰ .fst ])
      → fᴰ Cᴰ.≡[ A×B.η {f = f} ] introᴰ ((fᴰ Cᴰ.⋆ᴰ πᴰ₁) , (fᴰ Cᴰ.⋆ᴰ πᴰ₂))
    ×ηᴰ {Γ} {Γᴰ} {f} fᴰ = Cᴰ.rectify $ Cᴰ.≡out $
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
