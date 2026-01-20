
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.LocalRepresentability.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ
open Section

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  -- TODO:
  -- LRᴰProfᴰ : ∀
  --   {P : Presheaf C ℓP}
  --   (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  --   → Profunctorᴰ (LRProf P) Cᴰ Cᴰ _
  -- LRᴰProfᴰ {P = P} Pᴰ .F-obᴰ xᴰ = (Cᴰ [-][-, xᴰ ]) ×ᴰPsh Pᴰ
  -- LRᴰProfᴰ {P = P} Pᴰ .F-homᴰ fᴰ = {!PshHomᴰ→NatTransᴰ!}
  -- LRᴰProfᴰ {P = P} Pᴰ .F-idᴰ = {!!}
  -- LRᴰProfᴰ {P = P} Pᴰ .F-seqᴰ = {!!}

  LocallyRepresentableᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Presheafᴰ P Cᴰ ℓPᴰ
    → Type _
  LocallyRepresentableᴰ (P , _×P) Pᴰ = ∀ {c} cᴰ → UniversalElementᴰ Cᴰ (c ×P) ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh Pᴰ)

  open UniversalElement
  ∫LocallyRepresentable :
    {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
    → ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
    → LocallyRepresentable (∫P Pᴰ)
  ∫LocallyRepresentable (Pᴰ , _×ᴰPᴰ) (Γ , Γᴰ) =
    UniversalElementᴰ.∫ue (Γᴰ ×ᴰPᴰ)
      ◁PshIso
      (∫×ᴰ≅× ⋆PshIso ×PshIso (TotalCatYoPshIso Cᴰ) idPshIso)

  -- -- WIP
  -- module _ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  --   private
  --     module P = PresheafNotation P
  --   LRⱽProfᴰ : Profunctorⱽ (Cᴰ ×ᴰ Elements P) Cᴰ _
  --   LRⱽProfᴰ .F-obᴰ {Γ} (Γᴰ , p) = ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
  --   LRⱽProfᴰ .F-homᴰ {f = γ} (γᴰ , γp≡q) =
  --     PshHomᴰ→NatTransᴰ (PshHomEqPshHomᴰ (yoRecᴰ (Cᴰ [-][-, _ ]) γᴰ ×ⱽHom reind-introᴰ (PshHomPathPshHomᴰ reind-π (makePshHomPath (funExt λ Γ → funExt λ p → P.⟨⟩⋆⟨ sym γp≡q ⟩ ∙ (sym $ P.⋆Assoc _ _ _)))))
  --       Eq.refl)
  --   LRⱽProfᴰ .F-idᴰ = makeNatTransPathᴰ _ _ _ λ i → λ Γᴰ f (γᴰ , pᴰ) → (Cᴰ.⋆IdRᴰ γᴰ i) , {!!}
  --   LRⱽProfᴰ .F-seqᴰ = {!!}

  -- This can't be written as simply UniversalElementsⱽ of some
  -- Profunctorⱽ because the definition of Presheafⱽ depends on Γ.
  LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    where module P = PresheafNotation P


module _ {C : Category ℓC ℓC'} where
  LRᴰPresheafᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Categoryᴰ C ℓCᴰ ℓCᴰ'
    → (ℓPᴰ : Level)
    → Type _
  LRᴰPresheafᴰ P Cᴰ ℓPᴰ = Σ (Presheafᴰ (P .fst) Cᴰ ℓPᴰ) (LocallyRepresentableᴰ P)

  LRⱽPresheafᴰ :
    (P : Presheaf C ℓP)
    → Categoryᴰ C ℓCᴰ ℓCᴰ'
    → (ℓPᴰ : Level)
    → Type _
  LRⱽPresheafᴰ P Cᴰ ℓPᴰ = Σ (Presheafᴰ P Cᴰ ℓPᴰ) LocallyRepresentableⱽ
