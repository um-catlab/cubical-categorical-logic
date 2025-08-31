module Cubical.Categories.Displayed.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
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
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ : Level

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
  weakenⱽ .F-obᴰ bᴰ = isFib.f*yᴰ bᴰ bp.π₁
  weakenⱽ .F-homᴰ fᴰ =
    isFib.introCL (Cᴰ.reind (sym $ bp.×β₁) (isFib.π Cᴰ.⋆ᴰ fᴰ))
  weakenⱽ .F-idᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.introCL≡ (sym (Cᴰ.reind-filler _ _)
      ∙ Cᴰ.⋆IdR _
      ∙ (sym $ Cᴰ.⋆IdL _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
  weakenⱽ .F-seqᴰ fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.introCL≡
      (sym (Cᴰ.reind-filler _ _)
      ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.βCL) ⟩⋆⟨ refl ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.βCL) ⟩
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

    app : Cᴰ [ bp.×aF ⟪ C.id ⟫ ][ f*yᴰ vert bp.π₁ , pᴰ ]
    app = ∀ueⱽ.elementⱽ

    lda : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f} →
      Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]
      → Cᴰ [ f ][ Γᴰ , vert ]
    lda = ∀ueⱽ.universalⱽ .fst

    lda⟨_⟩⟨_⟩ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f g}
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
      {gᴰ : Cᴰ [ bp.×aF ⟪ g ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
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
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
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
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
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
  (F : Functor (PresheafCategory C ℓC') (PresheafCategory C ℓC'))
  (πF : NatTrans F Id)
  (ueF : (Q : Presheaf C ℓC') → UniversalElement C (F ⟅ Q ⟆))
  where

  open UniversalElement
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    πF-PshHom : ∀ Q → PshHom (F ⟅ Q ⟆) Q
    πF-PshHom Q = NatTrans→PshHom (πF .N-ob Q)

    F-PshHom : ∀ {Q Q' : Presheaf C ℓC'} →
      (α : NatTrans Q Q') →
      PshHom (F ⟅ Q ⟆) (F ⟅ Q' ⟆)
    F-PshHom α = NatTrans→PshHom (F ⟪ α ⟫)

    ＂F_＂ : C.ob → C.ob
    ＂F Γ ＂ = ueF (C [-, Γ ]) .vertex

    ＂F_＂elt : (Γ : C.ob) → _
    ＂F Γ ＂elt = ueF (C [-, Γ ]) .element

    ＂π＂ : {Γ : C.ob} → C [ ＂F Γ ＂ , Γ ]
    ＂π＂ {Γ = Γ} = πF ⟦ C [-, Γ ] ⟧ ⟦ ＂F Γ ＂ ⟧ $ ＂F Γ ＂elt

    -- F extends a functor on C
    FC : Functor C C
    FC = FunctorComprehension (F ∘F YO) (λ Γ → ueF (C [-, Γ ]))

  module _
    (πF*' : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      PshᴰCL.isFibration' (Cᴰ [-][-, Γᴰ ]))
    where

    open UniversalElementⱽ

    private
      πF* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) →
        UniversalElementⱽ Cᴰ ＂F Γ ＂ (reindYo ＂π＂ (Cᴰ [-][-, Γᴰ ]))
      πF* Γᴰ = πF*' Γᴰ ＂π＂

      ＂πF*_＂ : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ.ob[ ＂F Γ ＂ ]
      ＂πF* Γᴰ ＂ = πF* Γᴰ .vertexⱽ

    -- πF-Functorᴰ : Functorᴰ FC Cᴰ Cᴰ
    -- πF-Functorᴰ =
    --   FunctorᴰComprehension
    --     {!!}
    --     (λ Γ Γᴰ → πF* Γᴰ ◁PshIsoⱽᴰ {!!})

    module _
      {P : Presheaf C ℓC'}
      (Pᴰ : Presheafᴰ (F ⟅ P ⟆) Cᴰ ℓPᴰ) where

      private
        module P = PresheafNotation P
        module FP = PresheafNotation (F ⟅ P ⟆)
        module Pᴰ = PresheafᴰNotation Pᴰ

        mkFPElt : ∀ {Γ} → (p : P.p[ Γ ]) →
          FP.p[ ＂F Γ ＂ ]
        mkFPElt {Γ} p =
          (F ⟪ α ⟫) ⟦ ＂F Γ ＂ ⟧ $ ＂F Γ ＂elt
          where
          α : NatTrans (C [-, Γ ]) P
          α = PshHom→NatTrans (yoRec P p)

      -- Define ∀ᴰ Pᴰ such that
      --   (∀ᴰ Pᴰ) [ p ][ Γᴰ ] ≅ Pᴰ [ F p ][ πF* Γᴰ ]
      --
      --     Γᴰ --------> ∀ᴰ Pᴰ
      --     _              _
      --     |              |
      --     v      p       v
      --     Γ -----------> P
      --
      --   πF* Γᴰ --------> Pᴰ
      --     _              _
      --     |              |
      --     v     Fp       v
      --   ＂FΓ＂ --------> F P
      ∀ᴰPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ
      ∀ᴰPshᴰ .F-obᴰ {x = Γ} Γᴰ p = Pᴰ .F-obᴰ ＂πF* Γᴰ ＂ (mkFPElt p)
      -- Homs
      -- Given morphism γᴰ
      --            γᴰ
      --     Δᴰ ----------> Γᴰ
      --     _              _
      --     |              |
      --     v      γ       v
      --     Δ -----------> Γ
      --
      -- and element pᴰ
      --
      --            pᴰ
      --     Γᴰ --------> ∀ᴰ Pᴰ
      --     _              _
      --     |              |
      --     v      p       v
      --     Γ -----------> P
      --
      --            pᴰ
      --   πF* Γᴰ --------> Pᴰ
      --     _              _
      --     |              |
      --     v     Fp       v
      --   ＂FΓ＂ --------> F P
      --
      -- want
      --
      --   πF* Δᴰ --------> Pᴰ
      --     _              _
      --     |              |
      --     v              v
      --   ＂FΔ＂ --------> F P
      --
      -- πF* should have a functorial action on γᴰ
      --
      --         πF* γᴰ
      --   πF* Δᴰ -----> πF* Γᴰ
      --     _              _
      --     |              |
      --     v    ＂Fγ＂    v
      --   ＂FΔ＂ ------> ＂FΓ＂

      ∀ᴰPshᴰ .F-homᴰ {x = Γ}{y = Δ}{f = γ}{xᴰ = Γᴰ}{yᴰ = Δᴰ} γᴰ p pᴰ =
        Pᴰ.reind mkFPElt-natural $ πF*γᴰ Pᴰ.⋆ᴰ pᴰ
          where
          module π*よΓᴰ =
            PresheafⱽNotation (reindYo ＂π＂ (Cᴰ [-][-, Γᴰ ]))
          module π*よΔᴰ =
            PresheafⱽNotation (reindYo ＂π＂ (Cᴰ [-][-, Δᴰ ]))
          module よΓ = PresheafNotation (C [-, Γ ])
          module よΔ = PresheafNotation (C [-, Δ ])

          ＂Fγ＂ : C [ ＂F Δ ＂ , ＂F Γ ＂ ]
          ＂Fγ＂ = FC ⟪ γ ⟫

          πF-natural : ＂π＂ C.⋆ γ ≡ ＂Fγ＂ C.⋆ ＂π＂
          πF-natural =
            {!!}
            ∙ funExt⁻ ((πF ⟦ C [-, Γ ] ⟧) .N-hom ＂Fγ＂) ＂F Γ ＂elt


          δᴰ : π*よΓᴰ.p[ ＂Fγ＂ ][ ＂πF* Δᴰ ＂ ]
          δᴰ = Cᴰ.reind ((cong₂ C._⋆_ (C.⋆IdL _) refl) ∙ πF-natural) $
            πF* Δᴰ .elementⱽ Cᴰ.⋆ᴰ γᴰ

          πF*γᴰ : Cᴰ [ ＂Fγ＂ ][ ＂πF* Δᴰ ＂ , ＂πF* Γᴰ ＂ ]
          πF*γᴰ = introᴰ (πF* Γᴰ) δᴰ

          mkFPElt-natural : ＂Fγ＂ FP.⋆ (mkFPElt p) ≡ mkFPElt (γ P.⋆ p)
          mkFPElt-natural = {!!}

      ∀ᴰPshᴰ .F-idᴰ {xᴰ = Γᴰ} = funExt₂ λ p pᴰ →
        Pᴰ.rectify $ Pᴰ.≡out $
          (sym $ Pᴰ.reind-filler _ _)
          ∙ Pᴰ.⟨
            introᴰ≡ (πF* Γᴰ)
              {!!}
            ⟩⋆⟨⟩
          ∙ Pᴰ.⋆IdL _
          where
          module よΓᴰ =
            PresheafⱽNotation (Cᴰ [-][-, Γᴰ ])
          module π*よΓᴰ =
            PresheafⱽNotation (reindYo ＂π＂ (Cᴰ [-][-, Γᴰ ]))
      ∀ᴰPshᴰ .F-seqᴰ = {!!}

    module _ {Γ : C.ob} {Γᴰ : Cᴰ.ob[ ＂F Γ ＂ ]} where
      ∀ᴰ : Type _
      ∀ᴰ = UniversalElementⱽ Cᴰ Γ
        (∀ᴰPshᴰ (reind α (Cᴰ [-][-, Γᴰ ])))
        where
        α : PshHom (F ⟅ C [-, Γ ] ⟆) (C [-, ＂F Γ ＂ ])
        α = invPshIso {P = C [-, ＂F Γ ＂ ]}{Q = F ⟅ C [-, Γ ] ⟆}
          (UniversalElementNotation.asPshIso (ueF (C [-, Γ ]))) .fst
