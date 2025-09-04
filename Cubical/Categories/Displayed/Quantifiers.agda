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
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
import Cubical.Categories.Displayed.Fibration.Base as CatFibration
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

-- The universal/pi and existential/weak sigma type are defined as
-- left and right adjoints to a "weakening" functor
--
-- Cᴰ(x × y) → Cᴰ x
--     |        |
-- x:C , y:C → x:C

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {a : C .Category.ob}
  (bp : BinProductsWith C a)
  (isFib : CatFibration.isFibration Cᴰ)
  where
  private
    module bp = BinProductsWithNotation bp
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module isFib = CatFibration.isFibrationNotation _ isFib

  Cᴰ[-×a] : Categoryᴰ C ℓCᴰ ℓCᴰ'
  Cᴰ[-×a] = reindex Cᴰ bp.×aF

  open Functorᴰ

  weakenⱽ : Functorⱽ Cᴰ Cᴰ[-×a]
  weakenⱽ .F-obᴰ bᴰ = isFib.p*Pᴰ bᴰ bp.π₁
  weakenⱽ .F-homᴰ fᴰ =
    isFib.intro (Cᴰ.reind (sym $ bp.×β₁) (isFib.π Cᴰ.⋆ᴰ fᴰ))
  weakenⱽ .F-idᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.intro≡ (sym (Cᴰ.reind-filler _ _)
      ∙ Cᴰ.⋆IdR _
      ∙ (sym $ Cᴰ.⋆IdL _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
  weakenⱽ .F-seqᴰ fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.intro≡
      (sym (Cᴰ.reind-filler _ _)
      ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.β) ⟩⋆⟨ refl ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.β) ⟩
      ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
      )

  module _ {Γ} (pᴰ : Cᴰ.ob[ Γ bp.×a ]) where
    open Functor
    open Functorᴰ
    UniversalQuantifierPshⱽ : Presheafⱽ Γ Cᴰ ℓCᴰ'
    UniversalQuantifierPshⱽ = RightAdjointProfⱽ weakenⱽ .F-obᴰ pᴰ

    UniversalQuantifier : Type _
    UniversalQuantifier = UniversalElementⱽ Cᴰ Γ UniversalQuantifierPshⱽ

  -- TODO: it may be useful to prove the following:
  -- This definition includes the Beck condition that the quantifier
  -- is preserved by cartesian lifts, i.e., that quantifiers commute
  -- with substitution
  -- Cᴰ [ f ][ Γᴰ , g* (∀ pᴰ) ]
  -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
  -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
  -- ≅ Cᴰ [ (f ⋆ g) × b ][ π₁* Γᴰ , pᴰ ]
  -- ≅ Cᴰ [ (f × b) ⋆ (g × b) ][ π₁* Γᴰ , pᴰ ]
  -- ≅ Cᴰ [ (f × b) ][ π₁* Γᴰ , (g ⋆ b)* pᴰ ]
  -- ≅ Cᴰ [ f ][ Γᴰ , ∀ (g ⋆ b)* pᴰ ]
  module UniversalQuantifierNotation {b}{pᴰ : Cᴰ.ob[ b bp.×a ]}
    (∀pᴰ : UniversalQuantifier pᴰ) where
    module ∀ueⱽ = UniversalElementⱽ ∀pᴰ
    open Functor
    open Functorᴰ

    open CatFibration.isFibrationNotation Cᴰ isFib

    vert : Cᴰ.ob[ b ]
    vert = ∀ueⱽ.vertexᴰ

    app : Cᴰ [ bp.×aF ⟪ C.id ⟫ ][ p*Pᴰ vert bp.π₁ , pᴰ ]
    app = ∀ueⱽ.elementⱽ

    lda : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f} →
      Cᴰ [ bp.×aF ⟪ f ⟫ ][ p*Pᴰ Γᴰ bp.π₁ , pᴰ ]
      → Cᴰ [ f ][ Γᴰ , vert ]
    lda = ∀ueⱽ.universalⱽ .fst

    lda⟨_⟩⟨_⟩ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f g}
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ p*Pᴰ Γᴰ bp.π₁ , pᴰ ]}
      {gᴰ : Cᴰ [ bp.×aF ⟪ g ⟫ ][ p*Pᴰ Γᴰ bp.π₁ , pᴰ ]}
      → f ≡ g
      → Path Cᴰ.Hom[ _ , _ ]
          (_ , fᴰ)
          (_ , gᴰ)
      → Path Cᴰ.Hom[ _ , _ ]
          (_ , lda fᴰ)
          (_ , lda gᴰ)
    lda⟨ f≡g ⟩⟨ fᴰ≡gᴰ ⟩ =
      ∀ueⱽ.∫ue.intro⟨ ΣPathP (f≡g , (Cᴰ.rectify $ Cᴰ.≡out fᴰ≡gᴰ)) ⟩

    ∀β : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f} →
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ p*Pᴰ Γᴰ bp.π₁ , pᴰ ]}
      → Path Cᴰ.Hom[ _ , _ ]
          ((bp.×aF ⟪ f ⟫ C.⋆ bp.×aF ⟪ C.id ⟫) , (weakenⱽ .F-homᴰ (lda fᴰ) Cᴰ.⋆ᴰ app))
          (bp.×aF ⟪ f ⟫ , fᴰ)
    ∀β =
      Cᴰ.reind-filler _ _
      ∙ Cᴰ.reind-filler _ _
      ∙ (Cᴰ.≡in $ ∀ueⱽ.βⱽ)

    ∀η : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f}
      {fᴰ : Cᴰ [ f ][ Γᴰ , vert ]}
      → Path Cᴰ.Hom[ _ , _ ]
          (f , fᴰ)
          (f , lda (Cᴰ.reind (sym (bp.×aF .F-seq _ _) ∙ cong (bp.×aF .F-hom) (C.⋆IdR _))
            (weakenⱽ .F-homᴰ fᴰ Cᴰ.⋆ᴰ app)))
    ∀η = (Cᴰ.≡in $ ∀ueⱽ.ηⱽ)
      ∙ lda⟨ refl ⟩⟨ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.reind-filler _ _ ⟩

    lda≡ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f g}
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ p*Pᴰ Γᴰ bp.π₁ , pᴰ ]}
      {gᴰ : Cᴰ [ g ][ Γᴰ , vert ]}
      → f ≡ g
      → Path Cᴰ.Hom[ _ , _ ]
          (bp.×aF ⟪ f ⟫ , fᴰ)
          ((bp.×aF ⟪ g ⟫ C.⋆ bp.×aF ⟪ C.id ⟫), (weakenⱽ .F-homᴰ gᴰ Cᴰ.⋆ᴰ app))
      → Path Cᴰ.Hom[ _ , _ ]
          (f , lda fᴰ)
          (g , gᴰ)
    lda≡ f≡g fᴰ≡gᴰπ =
      lda⟨ f≡g ⟩⟨ fᴰ≡gᴰπ ∙ Cᴰ.reind-filler _ _ ⟩
      ∙ sym ∀η

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  (isFib : CatFibration.isFibration Cᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  UniversalQuantifiers : Type _
  UniversalQuantifiers = ∀ a Γ pᴰ
    → UniversalQuantifier {a = a} (λ c → bp (c , a)) isFib {Γ = Γ} pᴰ

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
      PshᴰCL.CartesianLift' (πF ⟦ Γ ⟧) (Cᴰ [-][-, Γᴰ ]))
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

  module _ (π₁* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → PshᴰCL.CartesianLift' bp.π₁ (Cᴰ [-][-, Γᴰ ]))
    {Γ} (Γᴰ : Cᴰ.ob[ Γ bp.×a ]) where
    UniversalQuantifier' : Type _
    UniversalQuantifier' = UniversalQuantifierF bp.×aF bp.π₁Nat π₁* Γᴰ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  (isFib : CatFibration.isFibration' Cᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  UniversalQuantifiers' : Type _
  UniversalQuantifiers' = ∀ a Γ pᴰ
    → UniversalQuantifier' {a = a} (λ c → bp (c , a)) (λ Γᴰ → isFib Γᴰ _) {Γ = Γ} pᴰ
