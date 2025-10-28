module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.UniversalProperty.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
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
open import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.NaturalTransformation.More
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
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.UniversalProperty.ComposeWeakening
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open NatTrans
open Functor
open Functorᴰ
open PshIso
open PshHom
open PshHomᴰ
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {a : C .Category.ob}
  (bp : BinProductsWith C a)
  where

  private
    module bp = BinProductsWithNotation bp
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _
    (π₁* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ bp.π₁)
    where
    open UniversalQuantifierPsh bp π₁*

    module _
      {Γ : C.ob}
      (Pⱽ : Presheafⱽ (Γ bp.×a) Cᴰ ℓPᴰ) where

      private
        module Pⱽ = PresheafⱽNotation Pⱽ

      module ∀ⱽPsh-UMP
        {Q : Presheaf C ℓQ}
        {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
        where
        open ∀ⱽPsh-UMP' bp π₁* Pⱽ

        private
          module Q = PresheafNotation Q
          module Qᴰ = PresheafᴰNotation Qᴰ

        module _
          {α : PshHom Q (C [-, Γ ])}
          (αᴰ : PshHomᴰ α Qᴰ (∀ⱽPsh Pⱽ))
          where

          ∀ⱽPsh-ηᴰ : ∀ⱽPsh-introᴰ Pⱽ (∀ⱽPsh-introᴰ⁻ Pⱽ αᴰ) ≡ αᴰ
          ∀ⱽPsh-ηᴰ =
            cong reind-introᴰ (∀ⱽPsh-ηᴰ' (αᴰ ⋆PshHomᴰ reind-π))
            ∙ reind-ηᴰ αᴰ

        module _
          {α : PshHom Q (C [-, Γ ])}
          (αᴰ : PshHomᴰ (mkProdPshHom Pⱽ α)
                 (reind (π₁ Q (C [-, a ])) Qᴰ) Pⱽ)
          where

          ∀ⱽPsh-βᴰ : ∀ⱽPsh-introᴰ⁻ Pⱽ (∀ⱽPsh-introᴰ Pⱽ αᴰ) ≡ αᴰ
          ∀ⱽPsh-βᴰ =
            cong (∀ⱽPsh-introᴰ⁻' Pⱽ) (reind-βᴰ (∀ⱽPsh-introᴰ' Pⱽ αᴰ))
            ∙ ∀ⱽPsh-βᴰ' αᴰ

        module _ {α : PshHom Q (C [-, Γ ])} where
          ∀Psh-UMPᴰ :
            Iso
              (PshHomᴰ (mkProdPshHom Pⱽ α)
                (reind (π₁ Q (C [-, a ])) Qᴰ) Pⱽ)
              (PshHomᴰ α Qᴰ (∀ⱽPsh Pⱽ))
          ∀Psh-UMPᴰ =
            iso
              (∀ⱽPsh-introᴰ Pⱽ)
              (∀ⱽPsh-introᴰ⁻ Pⱽ)
              ∀ⱽPsh-ηᴰ
              ∀ⱽPsh-βᴰ
