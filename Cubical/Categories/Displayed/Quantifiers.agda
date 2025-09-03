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
  (ueF : (Γ : C .Category.ob) → UniversalElement C (F ⟅ C [-, Γ ] ⟆))
  where

  open UniversalElement
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Psh = Category (PresheafCategory C ℓC')

    πF-PshHom : ∀ Q → PshHom (F ⟅ Q ⟆) Q
    πF-PshHom Q = NatTrans→PshHom (πF .N-ob Q)

    ＂F_＂ : C.ob → C.ob
    ＂F Γ ＂ = ueF Γ .vertex

    ＂π＂ : {Γ : C.ob} → C [ ＂F Γ ＂ , Γ ]
    ＂π＂ {Γ = Γ} = πF ⟦ C [-, Γ ] ⟧ ⟦ ＂F Γ ＂ ⟧ $ ueF Γ .element

    -- F extends a functor on C
    FC : Functor C C
    FC = FunctorComprehension (F ∘F YO) (λ Γ → ueF Γ)

    よ＂π＂≡ : (Γ : C.ob) → YO ⟪ ＂π＂ {Γ} ⟫ ≡
       seqTrans (no-no-no (F ⟅ C [-, Γ ] ⟆) (ueF Γ .element))
                (πF ⟦ C [-, Γ ] ⟧)
    よ＂π＂≡ Γ = {!!}

    ＂π＂-natural : ∀ {Γ}{Δ}(γ : C [ Γ , Δ ]) → ＂π＂ C.⋆ γ ≡ FC ⟪ γ ⟫ C.⋆ ＂π＂
    ＂π＂-natural {Γ}{Δ} γ =
      {!!}
      -- isFaithfulYO {C = C} ＂F Γ ＂ Δ _ _ $
      --   YO .F-seq ＂π＂ γ
      --   ∙ cong₂ seqTrans (よ＂π＂≡ Γ) refl
      --   ∙ (Psh.⋆Assoc
      --       (no-no-no (F ⟅ C [-, Γ ] ⟆) (ueF Γ .element))
      --       (πF ⟦ C [-, Γ ] ⟧)
      --       (YO {C = C} ⟪ γ ⟫))
      --   ∙ cong₂ seqTrans refl (sym $ πF .N-hom (no-no-no (C [-, Δ ]) γ))
      --   ∙ (sym $ Psh.⋆Assoc (PshHom→NatTrans (yoRec (F ⟅ C [-, Γ ] ⟆) (ueF Γ .element))) (F ⟪ no-no-no (C [-, Δ ]) γ ⟫) (πF ⟦ C [-, Δ ] ⟧))
      --   ∙ cong₂ seqTrans x refl
      --   ∙ (Psh.⋆Assoc
      --       (YO {C = C} ⟪ FC ⟪ γ ⟫ ⟫)
      --       (no-no-no (F ⟅ C [-, Δ ] ⟆) (ueF Δ .element))
      --       (πF ⟦ C [-, Δ ] ⟧)
      --      )
      --   ∙ cong₂ seqTrans refl (sym $ よ＂π＂≡ Δ)
      --   -- ∙ cong₂ seqTrans {!!} refl
      --   ∙ (sym $ YO {C = C} .F-seq {x = ＂F Γ ＂} {y = ＂F Δ ＂} {z = Δ}
      --             (FC ⟪ γ ⟫) ＂π＂)
       where
       module ueFΓ = UniversalElementNotation (ueF Γ)
       module ueFΔ = UniversalElementNotation (ueF Δ)
       module FΔ = PresheafNotation (F ⟅ C [-, Δ ] ⟆)

       -- x : seqTrans (PshHom→NatTrans (yoRec (F ⟅ C [-, Γ ] ⟆) (ueF Γ .element)))
       --              (F ⟪ PshHom→NatTrans $ yoRec (C [-, Δ ]) γ ⟫)
       --     ≡ seqTrans {G = C [-, ＂F Δ ＂ ]} (PshHom→NatTrans (yoRec (C [-, ＂F Δ ＂ ]) (FC ⟪ γ ⟫)))
       --                (PshHom→NatTrans (yoRec (F ⟅ C [-, Δ ] ⟆) (ueF Δ .element)))
       -- x = {!!}

  module _
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      PshᴰCL.CartesianLift' ＂π＂ (Cᴰ [-][-, Γᴰ ]))
    where

    open UniversalElementⱽ

    ＂πF*_＂ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ.ob[ ＂F Γ ＂ ]
    ＂πF* Γᴰ ＂ = πF* Γᴰ .vertexⱽ

    introπF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , ＂F Γ ＂ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ ＂π＂ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ Δᴰ , ＂πF* Γᴰ ＂ ]
    introπF* {Γᴰ = Γᴰ} γᴰ = introᴰ (πF* Γᴰ) γᴰ

    introπF*⟨_⟩⟨_⟩ :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ Δᴰ' : Cᴰ.ob[ Δ ]}{γ γ' : C [ Δ , ＂F Γ ＂ ]} →
        {Δᴰ≡Δᴰ' : Δᴰ ≡ Δᴰ'} →
        (γ≡γ' : γ ≡ γ') →
        {γᴰ : Cᴰ [ γ C.⋆ ＂π＂ ][ Δᴰ , Γᴰ ]} →
        {γᴰ' : Cᴰ [ γ' C.⋆ ＂π＂ ][ Δᴰ' , Γᴰ ]} →
        γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i C.⋆ ＂π＂ ][ Δᴰ≡Δᴰ' i , Γᴰ ]) ] γᴰ' →
        introπF* γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ≡Δᴰ' i , ＂πF* Γᴰ ＂ ]) ] introπF* γᴰ'
    introπF*⟨ γ≡γ' ⟩⟨ γᴰ≡γᴰ' ⟩ i = introπF* (γᴰ≡γᴰ' i)

    π-πF* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ [ ＂π＂ ][ ＂πF* Γᴰ ＂ , Γᴰ ]
    π-πF* Γᴰ = Cᴰ.reind (C.⋆IdL _) $ πF* Γᴰ .elementⱽ

    β-πF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , ＂F Γ ＂ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ ＂π＂ ][ Δᴰ , Γᴰ ])
      → introπF* γᴰ Cᴰ.⋆ᴰ π-πF* Γᴰ ≡ γᴰ
    β-πF* {Γᴰ = Γᴰ} γᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.≡in (βⱽ (πF* Γᴰ) {pᴰ = γᴰ})

    open PshHomᴰ

    Cᴰ[FC] : Categoryᴰ C ℓCᴰ ℓCᴰ'
    Cᴰ[FC] = reindex Cᴰ FC

    private
      module Cᴰ[FC] = Fibers Cᴰ[FC]

    weakenπF : Functorᴰ FC Cᴰ Cᴰ
    weakenπF .F-obᴰ Γᴰ = πF* Γᴰ .vertexⱽ
    weakenπF .F-homᴰ {f = γ} {xᴰ = Γᴰ} {yᴰ = Δᴰ} γᴰ =
      introπF* (Cᴰ.reind (＂π＂-natural γ) (π-πF* Γᴰ Cᴰ.⋆ᴰ γᴰ))
    weakenπF .F-idᴰ {xᴰ = Γᴰ} =
        introπF*⟨ FC .F-id  ⟩⟨
          Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⋆IdR _
            ∙ (sym $ Cᴰ.reind-filler _ _)
        ⟩
          ▷ (sym $ weak-ηⱽ (πF* Γᴰ))
    weakenπF .F-seqᴰ γᴰ δᴰ =
      introπF*⟨ FC .F-seq _ _ ⟩⟨
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
               ∙ Cᴰ.reind-filler _ _
               ∙ (Cᴰ.≡in $ sym $ β-πF* (Cᴰ.reind (＂π＂-natural _) (π-πF* _ Cᴰ.⋆ᴰ γᴰ)))
               ⟩⋆⟨ refl ⟩
          ∙ (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (πF* _))

    weakenπFⱽ : Functorⱽ Cᴰ Cᴰ[FC]
    weakenπFⱽ = introF Id (reindF' (FC ∘F Id) Eq.refl Eq.refl weakenπF)

    module _ {Γ} (Γᴰ : Cᴰ.ob[ ＂F Γ ＂ ]) where

      ∀Pshⱽ : Presheafⱽ Γ Cᴰ ℓCᴰ'
      ∀Pshⱽ = RightAdjointProfⱽ weakenπFⱽ .F-obᴰ Γᴰ

  -- --   module _
  -- --     {P : Presheaf C ℓC'}
  -- --     (Pᴰ : Presheafᴰ (F ⟅ P ⟆) Cᴰ ℓPᴰ) where

  -- --     private
  -- --       module P = PresheafNotation P
  -- --       module FP = PresheafNotation (F ⟅ P ⟆)
  -- --       module Pᴰ = PresheafᴰNotation Pᴰ

  -- --     -- Trying to do this manually and I
  -- --     -- run into obligations that seem to necessitate
  -- --     -- functorialiaty for πF*
  -- --     -- At the very least, the functoriality of πF* is
  -- --     -- sufficient
  -- --     ∀ᴰPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ
  -- --     ∀ᴰPshᴰ .F-obᴰ Γᴰ p =
  -- --       Pᴰ .F-obᴰ (πF* Γᴰ ＂π＂ .vertexⱽ) (F-elt P p)
  -- --     ∀ᴰPshᴰ .F-homᴰ γᴰ p pᴰ =
  -- --       Pᴰ.reind (sym $ F-elt-natural P p) $
  -- --         πF*-F-homᴰ γᴰ Pᴰ.⋆ᴰ pᴰ
  -- --     ∀ᴰPshᴰ .F-idᴰ = funExt₂ λ p pᴰ →
  -- --       Pᴰ.rectify $ Pᴰ.≡out $
  -- --         (sym $ Pᴰ.reind-filler _ _)
  -- --         ∙ Pᴰ.⟨ Cᴰ.≡in πF*-F-idᴰ ⟩⋆⟨⟩
  -- --         ∙ Pᴰ.⋆IdL _
  -- --     ∀ᴰPshᴰ .F-seqᴰ γᴰ δᴰ = funExt₂ λ p pᴰ →
  -- --       Pᴰ.rectify $ Pᴰ.≡out $
  -- --         (sym $ Pᴰ.reind-filler _ _)
  -- --         ∙ Pᴰ.⟨ Cᴰ.≡in (πF*-F-seqᴰ δᴰ γᴰ) ⟩⋆⟨⟩
  -- --         ∙ Pᴰ.⋆Assoc _ _ _
  -- --         ∙ Pᴰ.⟨ refl ⟩⋆⟨ Pᴰ.reind-filler _ _ ⟩
  -- --         ∙ Pᴰ.reind-filler _ _

  -- --     -- An equivalent definition that directly uses
  -- --     -- functoriality of πF*
  -- --     -- but is a lot slower at least with the above holes
  -- --     -- ∀ᴰPshᴰ' : Presheafᴰ P Cᴰ ℓPᴰ
  -- --     -- ∀ᴰPshᴰ' = reind (F-PshHom P) $
  -- --     --   (Pᴰ ∘Fᴰ (πF*-Functorᴰ ^opFᴰ))

    module _ {Γ : C.ob} (Γᴰ : Cᴰ.ob[ ＂F Γ ＂ ]) where
      UniversalQuantifierF : Type _
      UniversalQuantifierF = UniversalElementⱽ Cᴰ Γ (∀Pshⱽ Γᴰ)

    module UniversalQuantifierFNotation {Γ}{Γᴰ : Cᴰ.ob[ ＂F Γ ＂ ]}
      (∀Γᴰ : UniversalQuantifierF Γᴰ) where

      module ∀ueFⱽ = UniversalElementⱽ ∀Γᴰ

      vert : Cᴰ.ob[ Γ ]
      vert = ∀ueFⱽ.vertexⱽ

      app : Cᴰ [ FC ⟪ C.id ⟫ ][ ＂πF* vert ＂ , Γᴰ ]
      app = ∀ueFⱽ.elementⱽ

      lda : ∀ {Δ} {Δᴰ : Cᴰ.ob[ Δ ]} {γ} →
        Cᴰ [ FC ⟪ γ ⟫ ][ ＂πF* Δᴰ ＂ , Γᴰ ] →
        Cᴰ [ γ ][ Δᴰ , vert ]
      lda = ∀ueFⱽ.universalⱽ .fst

      -- TODO the rest of the interface
