module Cubical.Categories.Displayed.Quantifiers.Base where

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

    πF-PshHom : ∀ {Γ} → PshHom (C [-, F ⟅ Γ ⟆ ]) (C [-, Γ ])
    πF-PshHom = yoRec _ (N-ob πF _)

    open UniversalElementⱽ


    weakenπFᴰ = PshᴰCL.weakenπFᴰ F πF πF*
    module _ (P : Presheaf C ℓP) where
      private
        module P = PresheafNotation P

      nt : NatTrans (P ∘F (Id ^opF)) (P ∘F (F ^opF))
      nt = P NT.∘ʳ ⇒^opFiso .Iso.fun πF

      selfPshHet : PshHet F P P
      selfPshHet =
        eqToPshHom _ Eq.refl Eq.refl
        ⋆PshHom NatTrans→PshHom nt

      module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
        private
          module Pᴰ = PresheafᴰNotation Pᴰ
        selfPshHetᴰ : PshHetᴰ selfPshHet weakenπFᴰ Pᴰ Pᴰ
        selfPshHetᴰ .N-obᴰ pᴰ =
          Pᴰ.reind (P.⋆Assoc _ _ _ ∙ P.⋆IdL _) $
            πF* _ .elementⱽ Pᴰ.⋆ᴰ pᴰ
        selfPshHetᴰ .N-homᴰ = {!!}

    module _
      {Γ : C.ob}
      (Pⱽ : Presheafⱽ (F ⟅ Γ ⟆) Cᴰ ℓPᴰ) where

      private
        module Pⱽ = PresheafⱽNotation Pⱽ

      ∀FⱽPsh : Presheafⱽ Γ Cᴰ ℓPᴰ
      ∀FⱽPsh = reind (Functor→PshHet F Γ) $ Pⱽ ∘Fᴰ (weakenπFᴰ ^opFᴰ)

    module _ {Γ : C.ob} (Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]) where
      UniversalQuantifierF : Type _
      UniversalQuantifierF = UniversalElementⱽ Cᴰ Γ (∀FⱽPsh (Cᴰ [-][-, Γᴰ ]))

    module UniversalQuantifierFNotation {Γ}{Γᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ]}
      (∀Γᴰ : UniversalQuantifierF Γᴰ) where

      module ∀ueFⱽ = UniversalElementⱽ ∀Γᴰ

      vert : Cᴰ.ob[ Γ ]
      vert = ∀ueFⱽ.vertexⱽ

      app : Cᴰ [ _ ][ vertexⱽ (πF* ∀ueFⱽ.vertexⱽ) , Γᴰ ]
      app = ∀ueFⱽ.elementⱽ

      lda : ∀ {Δ} {Δᴰ : Cᴰ.ob[ Δ ]} {γ} →
        Cᴰ [ _ ][ vertexⱽ (πF* Δᴰ) , Γᴰ ] →
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
    open UniversalQuantifierF
    UniversalQuantifier : Type _
    UniversalQuantifier = UniversalQuantifierF bp.×aF bp.π₁Nat π₁* Γᴰ

    ∀ⱽPsh : Presheafⱽ Γ Cᴰ ℓCᴰ'
    ∀ⱽPsh = ∀FⱽPsh bp.×aF bp.π₁Nat π₁* (Cᴰ [-][-, Γᴰ ])

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
