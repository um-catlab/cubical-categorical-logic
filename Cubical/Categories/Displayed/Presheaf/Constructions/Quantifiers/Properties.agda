module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.NaturalTransformation.More as NT
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functor
open Functorᴰ
open PshHom
open PshHomᴰ
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c : C .Category.ob}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (-×c : BinProductsWith C c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  (F-× : preservesProvidedBinProductsWith F -×c)
  where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    F*Dᴰ = Base.reindex Dᴰ F
    module F*Dᴰ = Fibers F*Dᴰ
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module F-× = preservesProvidedBinProductsWithNotation F -×c -×Fc F-×
    module F⟨-×c⟩ {Γ} =
      BinProductNotation
        (preservesUniversalElement→UniversalElement
          (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

    module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
      module F⟨Γ×c⟩ =
        BinProductNotation
          (preservesUniversalElement→UniversalElement
            (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

  open UniversalElement

  module _
    (π₁*C : ∀ {Γ} →
      (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ -×c.π₁)
    (π₁*D : ∀ {Δ} →
      (Δᴰ : Dᴰ.ob[ Δ ]) → CartesianLift Dᴰ Δᴰ -×Fc.π₁)
    where

    private
      module ∀ⱽCᴰ = UniversalQuantifierPsh -×c π₁*C
      ∀ⱽPshCᴰ = ∀ⱽCᴰ.∀ⱽPsh
      module ∀ⱽDᴰ = UniversalQuantifierPsh -×Fc π₁*D
      ∀ⱽPshDᴰ = ∀ⱽDᴰ.∀ⱽPsh

    module _ {Γ : C.ob}
      (Qⱽ : Presheafⱽ (F ⟅ Γ ⟆ -×Fc.×a) Dᴰ ℓQᴰ)
      (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
      where
      private
        module Qⱽ = PresheafⱽNotation Qⱽ
        module ∀ⱽPshDᴰ =
          PresheafⱽNotation (∀ⱽPshDᴰ Qⱽ)
        module ∀ⱽPshCᴰ =
          PresheafⱽNotation (∀ⱽPshCᴰ (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ))

      Fᴰ-weakening-NatTransᴰ' :
        NatTransᴰ
          {!? ⋆NatTrans ?!}
          Fᴰ
          (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ Fᴰ)
      Fᴰ-weakening-NatTransᴰ' .NatTransᴰ.N-obᴰ xᴰ =
        {!!}
        -- introᴰ (π₁*D (F-obᴰ Fᴰ xᴰ)) (Dᴰ.reind {!!} Dᴰ.idᴰ)
      Fᴰ-weakening-NatTransᴰ' .NatTransᴰ.N-homᴰ = {!!}

      Fᴰ-weakening-NatTransᴰ :
        NatTransᴰ
          (F-×.FNatIso .NT.NatIso.trans)
          (Fᴰ ∘Fᴰ ∀ⱽCᴰ.weakenπFᴰ)
          (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ Fᴰ)
      Fᴰ-weakening-NatTransᴰ =
        {!? ⋆NatTransᴰ ?!}

      -- module _
      --   (Fᴰ-NatIsoᴰ :
      --     NatIsoᴰ F-×.FNatIso
      --       (Fᴰ ∘Fᴰ ∀ⱽCᴰ.weakenπFᴰ)
      --       (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ Fᴰ))
      --   where

      --   reindHet∀PshIsoⱽ :
      --     PshIsoⱽ
      --       (reindHet' (Functor→PshHet F Γ) Fᴰ (∀ⱽPshDᴰ Qⱽ))
      --       (∀ⱽPshCᴰ (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ))
      --   reindHet∀PshIsoⱽ =
      --     reindPshIsoⱽ reindFuncCompIsoⱽ
      --     ⋆PshIsoⱽ reind-seqIsoⱽ _ _ _
      --     ⋆PshIsoⱽ reindPshIsoⱽ (PshIsoᴰ→PshIsoⱽ (NatIsoᴰ→PshIsoᴰ (symNatIsoᴰ the-nat-isoᴰ)))
      --     ⋆PshIsoⱽ reind-seqIsoⱽ _ _ _
      --     ⋆PshIsoⱽ
      --       reindPathIsoⱽ
      --         (makePshHomPath (funExt₂ λ x p →
      --           cong₂ D._⋆_ (D.⋆IdL _ ∙ D.⋆IdR _) refl
      --           ∙ (sym $ F-×.FNatIso .NT.NatIso.trans .NT.NatTrans.N-hom p)))
      --     ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ _ _)
      --     ⋆PshIsoⱽ reindPshIsoⱽ annotateType

      --     where

      --     the-nat-isoᴰ :
      --       NatIsoᴰ _
      --         ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ))
      --         ((Qⱽ ∘Fᴰ (∀ⱽDᴰ.weakenπFᴰ ^opFᴰ)) ∘Fᴰ (Fᴰ ^opFᴰ))
      --     the-nat-isoᴰ =
      --       (symNatIsoᴰ $ CATᴰ⋆Assoc _ _ _)
      --       ⋆NatIsoᴰ (Qⱽ ∘ʳᴰⁱ
      --                   (∘Fᴰ-^opFᴰ-NatIsoᴰ ∀ⱽCᴰ.weakenπFᴰ Fᴰ
      --                   ⋆NatIsoᴰ opNatIsoᴰ (symNatIsoᴰ Fᴰ-NatIsoᴰ)
      --                   ⋆NatIsoᴰ (symNatIsoᴰ $ ∘Fᴰ-^opFᴰ-NatIsoᴰ Fᴰ ∀ⱽDᴰ.weakenπFᴰ)))
      --       ⋆NatIsoᴰ CATᴰ⋆Assoc _ _ _

      --     -- This is needed because there is not enough inference if
      --     -- eqToPshIsoⱽ is just used inline above
      --     annotateType :
      --       PshIsoⱽ
      --         (reind (F-×.preservesProdPshHet ∘ˡ -×c.×aF)
      --           ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ)))
      --         (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ
      --           ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ))
      --     annotateType = eqToPshIsoⱽ (Eq.refl , Eq.refl)
