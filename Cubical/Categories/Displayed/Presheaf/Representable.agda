{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Functor
open Functorᴰ
open PshHomᴰ
open isIsoOver

-- Displayed Yoneda
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  yoRecᴰ : ∀ {c}{cᴰ : Cᴰ.ob[ c ]} {p : P.p[ c ]}
    → (pᴰ : Pᴰ.p[ p ][ cᴰ ]) → PshHomᴰ (yoRec P p) (Cᴰ [-][-, cᴰ ]) Pᴰ
  yoRecᴰ pᴰ .N-obᴰ fᴰ = fᴰ Pᴰ.⋆ᴰ pᴰ
  yoRecᴰ pᴰ .N-homᴰ = Pᴰ.⋆Assocᴰ _ _ _

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (ue : UniversalElement C P) (Pᴰ : Presheafᴰ P D ℓPᴰ) where
  private
    module D = Fibers D
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  record UniversalElementᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    field
      vertexᴰ : D.ob[ vertex ]
      elementᴰ : Pᴰ.p[ element ][ vertexᴰ ]
      universalᴰ :
        isPshIsoᴰ (yoRec P element) (D [-][-, vertexᴰ ]) Pᴰ
          (yoRecᴰ Pᴰ elementᴰ) ⋆element-isPshIso

    introᴰ : ∀ {x xᴰ} {p : P.p[ x ]}
        → Pᴰ.p[ p ][ xᴰ ]
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ = universalᴰ .isIsoOver.inv _

    ∫ue : UniversalElement (TotalCat.∫C D) (∫P Pᴰ)
    ∫ue .UniversalElement.vertex = vertex , vertexᴰ
    ∫ue .UniversalElement.element = element , elementᴰ
    ∫ue .UniversalElement.universal (v , vᴰ) =
      isIsoToIsEquiv (isIsoOver→isIsoΣ universalᴰ)

    module ∫ue = UniversalElementNotation ∫ue
    module Pshᴰ = PresheafᴰNotation Pᴰ

    -- We only provide the ∫ versions of these because working with
    -- the PathP versions is extremely slow.
    introᴰ≡ = ∫ue.intro≡
    introᴰ-natural = ∫ue.intro-natural
    extensionalityᴰ = ∫ue.extensionality
    βᴰ = ∫ue.β
    ηᴰ = ∫ue.η
    weak-ηᴰ = ∫ue.weak-η

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} {ue : UniversalElement C P} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
         (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
         where
  private
    module ueᴰ = UniversalElementᴰ ueᴰ
  yoRecIsoᴰ : PshIsoᴰ (yoRecIso ue) (Cᴰ [-][-, ueᴰ.vertexᴰ ]) Pᴰ
  yoRecIsoᴰ .fst = yoRecᴰ Pᴰ ueᴰ.elementᴰ
  yoRecIsoᴰ .snd = ueᴰ.universalᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} ((x , yx≅P) : RepresentationPshIso P)
         (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  RepresentationPshIsoᴰ : Type _
  RepresentationPshIsoᴰ =
    Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] PshIsoᴰ yx≅P (Cᴰ [-][-, xᴰ ]) Pᴰ

  open UniversalElementᴰ
  module _  ((xᴰ , yxᴰ≅Pᴰ) : RepresentationPshIsoᴰ) where
    private
      ∫repr→ue : UniversalElement (TotalCat.∫C Cᴰ) (∫P Pᴰ)
      ∫repr→ue = RepresentationPshIso→UniversalElement
        (∫P Pᴰ)
        (_ , (∫PshIsoᴰ yxᴰ≅Pᴰ))
      module ∫repr→ue = UniversalElementNotation ∫repr→ue

    RepresentationPshIsoᴰ→UniversalElementᴰ :
      UniversalElementᴰ Cᴰ
        (RepresentationPshIso→UniversalElement P (x , yx≅P))
        Pᴰ
    RepresentationPshIsoᴰ→UniversalElementᴰ .vertexᴰ  = ∫repr→ue.vertex .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .elementᴰ = ∫repr→ue.element .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .inv p pᴰ = ∫repr→ue.intro (p , pᴰ) .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .rightInv p pᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫repr→ue.β
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $ sym $ ∫repr→ue.η

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {P : Presheaf C ℓC'} (Pᴰ : Presheafᴰ P Cᴰ ℓCᴰ')
  where
  private
    module Cᴰ = Fibers Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
  Representsᵁᴰ : ∀ {x} → Representsᵁ C P x → (xᴰ : Cᴰ.ob[ x ]) → Type _
  Representsᵁᴰ yx≡P xᴰ =
    PathP (λ i → Presheafᴰ (yx≡P i) Cᴰ ℓCᴰ')
      (Cᴰ [-][-, xᴰ ])
      Pᴰ

  Representationᵁᴰ : Representationᵁ C P → Type _
  Representationᵁᴰ (x , yx≡P) = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Representsᵁᴰ yx≡P xᴰ
  -- same but uglier:
  -- fiberOver {Q = λ P → Presheafᴰ P Cᴰ ℓCᴰ'} (x , yx≡P) (λ _ → Cᴰ [-][-,_]) Pᴰ

  ∫Reprᵁ : ∀ {repr : Representationᵁ C P} → Representationᵁᴰ repr → Representationᵁ (TotalCat.∫C Cᴰ) (∫P Pᴰ)
  ∫Reprᵁ {repr} reprᴰ .fst = repr .fst , reprᴰ .fst
  ∫Reprᵁ {repr} reprᴰ .snd = Functor≡
    (λ (c , cᴰ) → ΣPathP ((λ i → Σ (repr .snd i .F-ob c .fst) λ x → reprᴰ .snd i .F-obᴰ cᴰ x .fst) , isProp→PathP (λ _ → isPropIsSet) _ _))
    λ (f , fᴰ) → λ i (x , xᴰ) → (repr .snd i .F-hom f x) , reprᴰ .snd i .F-homᴰ fᴰ x xᴰ

  UniversalElementᴰ→Representationᵁᴰ :
    ∀ {ue : UniversalElement C P}
    → UniversalElementᴰ Cᴰ ue Pᴰ
    → Representationᵁᴰ (UniversalElement→Representationᵁ C P ue)
  UniversalElementᴰ→Representationᵁᴰ {ue} ueᴰ = ueᴰ.vertexᴰ
    , PshIsoᴰ→PathP _ _ _
    ( yoRecᴰ Pᴰ ueᴰ.elementᴰ
    , (isisoover
         (λ _ → ueᴰ.introᴰ)
         (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ ueᴰ.βᴰ)
         λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueᴰ.ηᴰ))
    where
      module ueᴰ = UniversalElementᴰ ueᴰ

  module _ {repr : Representationᵁ C P} (reprᴰ : Representationᵁᴰ repr) where
    private
      ∫repr : Representationᵁ (TotalCat.∫C Cᴰ) (∫P Pᴰ)
      ∫repr = ∫Reprᵁ reprᴰ

      ∫reprpshiso = Representationᵁ→RepresentationPshIso (TotalCat.∫C Cᴰ) (∫P Pᴰ) ∫repr

    Representationᵁᴰ→RepresentationPshIsoᴰ
      : RepresentationPshIsoᴰ Cᴰ (Representationᵁ→RepresentationPshIso C P repr) Pᴰ
    Representationᵁᴰ→RepresentationPshIsoᴰ .fst = reprᴰ .fst
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .fst .N-obᴰ pᴰ = ∫reprpshiso .snd .fst .fst _ (_ , pᴰ) .snd
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .fst .N-homᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫reprpshiso .snd .fst .snd _ _ _ _
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .inv p pᴰ =
      ∫reprpshiso .snd .snd _ .fst (p , pᴰ) .snd
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .rightInv p pᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫reprpshiso .snd .snd _ .snd .fst (p , pᴰ)
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $ ∫reprpshiso .snd .snd _ .snd .snd (f , fᴰ)

    Representationᵁᴰ→UniversalElementᴰ :
      UniversalElementᴰ Cᴰ (Representationᵁ→UniversalElement C P repr) Pᴰ
    Representationᵁᴰ→UniversalElementᴰ =
      RepresentationPshIsoᴰ→UniversalElementᴰ Cᴰ (Representationᵁ→RepresentationPshIso C P repr) Pᴰ
        Representationᵁᴰ→RepresentationPshIsoᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafⱽNotation Pⱽ

  -- A UniversalElementⱽ is equivalent to a UniversalElementᴰ but
  -- stated in terms of Pⱽ.⋆ᴰⱽ instead of Pⱽ.⋆ᴰ, so the universality
  -- property is simpler.

  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.pⱽ[ vertexⱽ ]
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]) → fᴰ Pⱽ.⋆ᴰⱽ elementⱽ
    toUniversalᴰ : UniversalElementᴰ Cᴰ (selfUnivElt C x) Pⱽ
    toUniversalᴰ .UniversalElementᴰ.vertexᴰ = vertexⱽ
    toUniversalᴰ .UniversalElementᴰ.elementᴰ = elementⱽ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.inv f fᴰ =
      universalⱽ .fst fᴰ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.rightInv f fᴰ =
      Pⱽ.rectify $ Pⱽ.≡out $
        (Pⱽ.≡in $ Pⱽ.⋆ᴰid≡⋆ᴰⱽ _ _)
        ∙ (Pⱽ.≡in $ universalⱽ .snd .fst fᴰ)
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        (Cᴰ.≡in $ (λ i → universalⱽ .fst (Pⱽ.⋆ᴰid≡⋆ᴰⱽ fᴰ elementⱽ i)))
        ∙ (Cᴰ.≡in $ universalⱽ .snd .snd fᴰ)

    open UniversalElementᴰ toUniversalᴰ hiding (module Pshᴰ) public
    module Pshⱽ = PresheafⱽNotation Pⱽ

    introⱽ : ∀ {xᴰ} → Pⱽ.p[ C.id ][ xᴰ ] → Cᴰ.v[ x ] [ xᴰ , vertexᴰ ]
    introⱽ = introᴰ

    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : Pⱽ.p[ f ][ yᴰ ]}
      → introᴰ pᴰ Pⱽ.⋆ᴰⱽ elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introᴰ (fᴰ Pⱽ.⋆ᴰⱽ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {x : C .Category.ob} {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafⱽNotation Pⱽ

  open UniversalElementⱽ
  fromUniversalᴰ : UniversalElementᴰ Cᴰ (selfUnivElt C x) Pⱽ → UniversalElementⱽ Cᴰ x Pⱽ
  fromUniversalᴰ ueᴰ = record
    { vertexⱽ = ueᴰ.vertexᴰ
    ; elementⱽ = ueᴰ.elementᴰ
    ; universalⱽ = (ueᴰ.universalᴰ .inv _)
      , (λ pᴰ → Pⱽ.rectify $ Pⱽ.≡out $ (sym $ Pⱽ.reind-filler _ _) ∙ ueᴰ.βᴰ)
      , λ fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ ueᴰ.∫ue.intro⟨ sym $ Pⱽ.reind-filler _ _ ⟩ ∙ sym ueᴰ.ηᴰ
    } where module ueᴰ = UniversalElementᴰ ueᴰ

  yoRecⱽ : ∀ {xᴰ} → Pⱽ.pⱽ[ xᴰ ] → PshHomⱽ (Cᴰ [-][-, xᴰ ]) Pⱽ
  yoRecⱽ pⱽ .N-obᴰ fᴰ = fᴰ Pⱽ.⋆ᴰⱽ pⱽ
  yoRecⱽ pⱽ .N-homᴰ = Pⱽ.⋆Assocᴰᴰⱽ _ _ _

  module _ (ueⱽ : UniversalElementⱽ Cᴰ x Pⱽ) where
    private
      module ueⱽ = UniversalElementⱽ ueⱽ

    yoRecIsoⱽ : PshIsoⱽ (Cᴰ [-][-, ueⱽ.vertexᴰ ]) Pⱽ
    yoRecIsoⱽ .fst = yoRecⱽ ueⱽ.elementⱽ
    yoRecIsoⱽ .snd = isisoover
      (λ a → ueⱽ.universalⱽ .fst)
      (λ b → ueⱽ.universalⱽ .snd .fst)
      (λ a → ueⱽ.universalⱽ .snd .snd)

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c} {Pⱽ : Presheafⱽ c Cᴰ ℓCᴰ'}
  where

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c} (Pⱽ : Presheafⱽ c Cᴰ ℓCᴰ')
  where
  Representationᵁⱽ : Type _
  Representationᵁⱽ = Representationᵁᴰ Cᴰ Pⱽ (_ , refl)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {ue : UniversalElement C P}{α : PshIso P Q}
  where
  _◃PshIsoᴰ_ : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
    → UniversalElementᴰ Cᴰ (ue ◃PshIso α) Qᴰ
  ueᴰ ◃PshIsoᴰ αᴰ = record
    { vertexᴰ = ∫◃ .vertex .snd
    ; elementᴰ = ∫◃ .element .snd
    ; universalᴰ = isisoover
      (λ q qᴰ → ∫◃.intro (q , qᴰ) .snd)
      (λ q qᴰ → Qᴰ.rectify $ Qᴰ.≡out $ ∫◃.β)
      λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ∫◃.η
    } where
      open UniversalElement
      module Cᴰ = Fibers Cᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module ueᴰ = UniversalElementᴰ ueᴰ
      ∫◃ = ueᴰ.∫ue ◃PshIso ∫PshIsoᴰ αᴰ
      module ∫◃ = UniversalElementNotation ∫◃

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {x}
  {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ}{Qⱽ : Presheafⱽ x Cᴰ ℓQᴰ}
  where
  _◃PshIsoⱽ_ : UniversalElementⱽ Cᴰ x Pⱽ → PshIsoⱽ Pⱽ Qⱽ → UniversalElementⱽ Cᴰ x Qⱽ
  ueⱽ ◃PshIsoⱽ αⱽ = fromUniversalᴰ record
    { vertexᴰ = ueⱽ◃αⱽ.vertexᴰ
    ; elementᴰ = ueⱽ◃αⱽ.elementᴰ -- ueᴰ◃αⱽ.elementᴰ
    ; universalᴰ = isisoover
      (λ _ → ueⱽ◃αⱽ.introᴰ)
      (λ _ _ → Qⱽ.rectify $ Qⱽ.≡out $ ueⱽ◃αⱽ.βᴰ)
      (λ _ _ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueⱽ◃αⱽ.ηᴰ)
    } where
      module ueⱽ = UniversalElementⱽ ueⱽ
      ueᴰ◃αⱽ = ueⱽ.toUniversalᴰ ◃PshIsoᴰ αⱽ
      module Cᴰ = Fibers Cᴰ
      module Qⱽ = PresheafⱽNotation Qⱽ
      module ueⱽ◃αⱽ = UniversalElementᴰ ueᴰ◃αⱽ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
  {ue : UniversalElement C P}
  where
  _◃PshIsoᴰⱽ_ : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) (αⱽ : PshIsoⱽ Pᴰ Qᴰ)
    → UniversalElementᴰ Cᴰ ue Qᴰ
  ueᴰ ◃PshIsoᴰⱽ αⱽ = record
    { vertexᴰ = ueᴰ◃αⱽ.vertexᴰ
    ; elementᴰ = ueᴰ◃αⱽ.elementᴰ
    ; universalᴰ = isisoover
      (λ p qᴰ → ueᴰ◃αⱽ.introᴰ qᴰ)
      (λ p qᴰ → Qᴰ.rectify $ Qᴰ.≡out $ ueᴰ◃αⱽ.βᴰ)
      (λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueᴰ◃αⱽ.ηᴰ)
    } where
      ueᴰ◃αⱽ = ueᴰ ◃PshIsoᴰ αⱽ
      module Cᴰ = Fibers Cᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module ueᴰ◃αⱽ = UniversalElementᴰ ueᴰ◃αⱽ

open UniversalElement
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Q : Presheaf C ℓQ}
  {ue : UniversalElement C Q}
  {Pⱽ : Presheafⱽ (ue .vertex) Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  -- This could probably be implemented as a subst instead of manually.
  _◃PshIsoⱽᴰ_ : UniversalElementⱽ Cᴰ (ue .vertex) Pⱽ
    → PshIsoᴰ (yoRecIso ue) Pⱽ Qᴰ
    → UniversalElementᴰ Cᴰ ue Qᴰ
  ueⱽ ◃PshIsoⱽᴰ αᴰ = record
    { vertexᴰ = ueⱽ.vertexⱽ
    ; elementᴰ = Qᴰ.reind (Q.⋆IdL _) (αᴰ .fst .N-obᴰ ueⱽ.elementⱽ)
    ; universalᴰ = isisoover
      (λ q qᴰ → ueⱽ.introᴰ (αᴰ .snd .inv q qᴰ))
      (λ q qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
        Qᴰ.⟨⟩⋆⟨ (sym $ Qᴰ.reind-filler _ _) ∙ refl ⟩
        ∙ (sym $ ∫α .fst .snd _ _ _ _)
        ∙ cong (∫α .fst .fst _) ueⱽ.βᴰ
        ∙ ∫α .snd _ .snd .fst _)
      (λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $
        ueⱽ.∫ue.intro≡ $
          invPshIso ∫α .fst .snd _ _ _ _
          ∙ Pⱽ.⟨⟩⋆⟨ cong (∫α .snd _ .fst) (sym $ Qᴰ.reind-filler _ _)
          ∙ ∫α .snd _ .snd .snd _ ⟩)
    } where
      ∫α = ∫PshIsoᴰ αᴰ
      module ue = UniversalElementNotation ue
      module ueⱽ = UniversalElementⱽ ueⱽ
      module Q = PresheafNotation Q
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Pⱽ = PresheafⱽNotation Pⱽ
      module Cᴰ = Fibers Cᴰ
