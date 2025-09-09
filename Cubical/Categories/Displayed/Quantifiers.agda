module Cubical.Categories.Displayed.Quantifiers where

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
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

-- The universal/pi and existential/weak sigma type are defined as
-- left and right adjoints to a "weakening" functor
--
-- The weakening functor is defined abstractly by an endofunctor F
-- and natural projection πF : F ⇒ Id such that cartesian lifts of
-- all displayed objects along πF exist
--
-- weakenπF Γᴰ -----> Δᴰ          Γᴰ --------> ∀ Δᴰ
--     -              -           -              -
--     |              |    ≅      |              |
--     v              v           v              v
--    FΓ ----------> FΔ           Γ -----------> Δ
--
-- The endofunctor F generalizes the usual construction
-- of a universal quantifier which takes F to be the binary
-- product and πF to be π₁
open NatTrans
open Functor
open Functorᴰ
module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (F : Functor C C)
  (πF : NatTrans F Id)
  where

  open UniversalElement

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      PshᴰCL.CartesianLift (πF ⟦ Γ ⟧) (Cᴰ [-][-, Γᴰ ]))
    where

    open UniversalElementⱽ

    module _
      {Γ : C.ob}
      (Pⱽ : Presheafⱽ (F ⟅ Γ ⟆) Cᴰ ℓPᴰ) where

      private
        module Pⱽ = PresheafⱽNotation Pⱽ
        weakenπFᴰ = PshᴰCL.weakenπFᴰ F πF πF*

      ∀Pshⱽ : Presheafⱽ Γ Cᴰ ℓPᴰ
      ∀Pshⱽ .F-obᴰ {x = Δ} Δᴰ δ = Pⱽ .F-obᴰ (πF* Δᴰ .vertexⱽ) (F ⟪ δ ⟫)
      ∀Pshⱽ .F-homᴰ {x = Δ} {y = Θ} {f = δ} {xᴰ = Δᴰ} {yᴰ = Θᴰ} δᴰ γ γᴰ =
        Pⱽ.reind (sym $ F .F-seq δ γ) $ (weakenπFᴰ .F-homᴰ δᴰ Pⱽ.⋆ᴰ γᴰ)
      ∀Pshⱽ .F-idᴰ = funExt₂ λ _ _ →
        Pⱽ.rectify $ Pⱽ.≡out $
          (sym $ Pⱽ.reind-filler _ _)
          ∙ Pⱽ.⟨ Cᴰ.≡in $ weakenπFᴰ .F-idᴰ ⟩⋆⟨⟩
          ∙ Pⱽ.⋆IdL _
      ∀Pshⱽ .F-seqᴰ δᴰ θᴰ = funExt₂ λ _ _ →
        Pⱽ.rectify $ Pⱽ.≡out $
          (sym $ Pⱽ.reind-filler _ _)
          ∙ Pⱽ.⟨ Cᴰ.≡in (weakenπFᴰ .F-seqᴰ θᴰ δᴰ) ⟩⋆⟨⟩
          ∙ Pⱽ.⋆Assoc _ _ _
          ∙ Pⱽ.⟨ refl ⟩⋆⟨ Pⱽ.reind-filler _ _ ⟩
          ∙ Pⱽ.reind-filler _ _

    module _ {Γ : C.ob} (Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]) where
      UniversalQuantifierF : Type _
      UniversalQuantifierF = UniversalElementⱽ Cᴰ Γ (∀Pshⱽ (Cᴰ [-][-, Γᴰ ]))

    module UniversalQuantifierFNotation {Γ}{Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]}
      (∀Γᴰ : UniversalQuantifierF Γᴰ) where

      module ∀ueFⱽ = UniversalElementⱽ ∀Γᴰ

      vert : Cᴰ.ob[ Γ ]
      vert = ∀ueFⱽ.vertexⱽ

      app : Cᴰ [ F ⟪ C.id ⟫ ][ vertexⱽ (πF* ∀ueFⱽ.vertexⱽ) , Γᴰ ]
      app = ∀ueFⱽ.elementⱽ

      lda : ∀ {Δ} {Δᴰ : Cᴰ.ob[ Δ ]} {γ} →
        Cᴰ [ F ⟪ γ ⟫ ][ vertexⱽ (πF* Δᴰ) , Γᴰ ] →
        Cᴰ [ γ ][ Δᴰ , vert ]
      lda = ∀ueFⱽ.universalⱽ .fst


-- The usual universal quantifier defined with respect to
-- a binary product
--
-- Cᴰ(x × y) → Cᴰ x
--     |        |
-- x:C , y:C → x:C

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

  module _ (π₁* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → PshᴰCL.CartesianLift bp.π₁ (Cᴰ [-][-, Γᴰ ]))
    {Γ} (Γᴰ : Cᴰ.ob[ Γ bp.×a ]) where
    UniversalQuantifier : Type _
    UniversalQuantifier = UniversalQuantifierF bp.×aF bp.π₁Nat π₁* Γᴰ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  (isFib : isFibration Cᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  UniversalQuantifiers : Type _
  UniversalQuantifiers = ∀ a Γ pᴰ
    → UniversalQuantifier {a = a} (λ c → bp (c , a)) (λ Γᴰ → isFib Γᴰ _) {Γ = Γ} pᴰ
