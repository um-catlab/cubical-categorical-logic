module Cubical.Categories.Displayed.Quantifiers.Base where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.NaturalTransformation as NT

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base

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
open PshHomᴰ
module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where

  open UniversalElement

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module UniversalQuantifierF
    (F : Functor C C)
    (πF : NatTrans F Id)
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      CartesianLift Cᴰ Γᴰ (πF ⟦ Γ ⟧))
    where

    open UniversalQuantifierFPsh F πF πF*

    module _ {Γ : C.ob} (Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]) where
      UniversalQuantifierF : Type _
      UniversalQuantifierF =
        UniversalElementⱽ Cᴰ Γ (∀FⱽPsh (Cᴰ [-][-, Γᴰ ]))

    module UniversalQuantifierFNotation {Γ}{Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]}
      (∀Γᴰ : UniversalQuantifierF Γᴰ) where

      module ∀ueFⱽ = UniversalElementⱽ ∀Γᴰ

      open UniversalElementⱽ

      vert : Cᴰ.ob[ Γ ]
      vert = ∀ueFⱽ.vertexⱽ

      app : Cᴰ [ _ ][ πF* vert .vertexⱽ , Γᴰ ]
      app = ∀ueFⱽ.elementⱽ

      lda : ∀ {Δ} {Δᴰ : Cᴰ.ob[ Δ ]} {γ} →
        Cᴰ [ Functor→PshHet F Γ .PshHom.N-ob Δ γ ][ vertexⱽ (πF* Δᴰ) , Γᴰ ] →
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

  module _ (π₁* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ bp.π₁)
    {Γ} (Γᴰ : Cᴰ.ob[ Γ bp.×a ]) where

    open UniversalQuantifierF bp.×aF bp.π₁Nat π₁*

    UniversalQuantifier : Type _
    UniversalQuantifier = UniversalQuantifierF Γᴰ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  (isFib : isFibration Cᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  UniversalQuantifiers : Type _
  UniversalQuantifiers =
    ∀ a Γ pᴰ →
      UniversalQuantifier {a = a}
        (BinProducts→BinProductsWith C a bp)
        (λ Γᴰ → isFib Γᴰ _) {Γ = Γ} pᴰ
