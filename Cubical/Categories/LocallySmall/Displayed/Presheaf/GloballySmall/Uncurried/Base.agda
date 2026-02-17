module Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More


open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Graph.Presheaf.GloballySmall.Base

open Σω
open Liftω
open Functor

module _ where
  open SmallCategoryVariables
  open SmallCategory
  module _
    (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
    (P : Presheaf C ℓP) where
    open SmallCategoryᴰ
    _/_ : SmallCategory _ _
    _/_ = ∫Csmall (Cᴰ ×ᴰsmall Element C P)

  module _
    (P : Presheaf C ℓP)
    (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
    where
    Presheafᴰ : Level → Typeω
    Presheafᴰ = Presheaf (Cᴰ / P)

  module _ (c : C .ob) where
    Presheafⱽ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ' → Level → Typeω
    Presheafⱽ = Presheafᴰ (C [-, c ])

  module PresheafᴰNotation
    -- Cᴰ and P *must* be supplied, Cᴰ for type-checking and P for performance.
    -- revisit this once no-eta-equality for categories is turned on
    (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
    (P : Presheaf C ℓP)
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    where
    private
      module C = SmallCategory C
      module Cᴰ = SmallCategoryᴰ Cᴰ
      module P = PresheafNotation P
      module Pᴰ = PresheafNotation Pᴰ
    p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.obᴰ x → Type ℓPᴰ
    p[ p ][ xᴰ ] = ⟨ Pᴰ .F-ob (liftω (_ , xᴰ , p)) .lowerω ⟩

    isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
    isSetPshᴰ = Pᴰ .F-ob _ .lowerω .snd

    module pReasoning {x}{xᴰ : Cᴰ.obᴰ x} =
      hSetReasoning (P .F-ob (liftω x) .lowerω) p[_][ xᴰ ]
    open pReasoning renaming
      (_P≡[_]_ to _≡[_]_; Prectify to rectify) public

    infixr 9 _⋆ᴰ_
    _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}{p} (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) (pᴰ : p[ p ][ yᴰ .lowerω ])
      → p[ f P.⋆ p ][ xᴰ .lowerω ]
    fᴰ ⋆ᴰ pᴰ = Pᴰ .F-hom (_ , fᴰ , refl) pᴰ

    opaque
      ⋆ᴰ-reind : ∀ {x y xᴰ yᴰ}
        {f : C.Hom[ x , y ]}{p q}
        (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
        (f⋆p≡q : f P.⋆ p ≡ q) (pᴰ : p[ p ][ yᴰ .lowerω ])
        → Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ ≡ reind f⋆p≡q (fᴰ ⋆ᴰ pᴰ)
      ⋆ᴰ-reind {x}{y}{xᴰ}{yᴰ} {f = f}{p}{q} fᴰ f⋆p≡q pᴰ = rectify $ ≡out $ (sym $ ≡in $ lem) ∙ reind-filler f⋆p≡q where
        lem : PathP (λ i → ⟨ Pᴰ .F-ob (liftω (x .lowerω , xᴰ .lowerω , f⋆p≡q i) ) .lowerω ⟩)
          (Pᴰ .F-hom (f , fᴰ , (λ _ → P .F-hom f p)) pᴰ)
          (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
        lem i = Pᴰ .F-hom (f , fᴰ , λ j → f⋆p≡q (i ∧ j)) pᴰ

      ⋆IdLᴰ : ∀ {x}{xᴰ}{p : P.p[ x ]}(pᴰ : p[ p ][ xᴰ ])
        → (Pᴰ .F-hom (C.id , Cᴰ.idᴰ , refl {x = C.id P.⋆ p}) pᴰ) ∫≡ pᴰ
      ⋆IdLᴰ {x}{xᴰ}{p} pᴰ =
        reind-filler _
        ∙ (≡in $ sym $ ⋆ᴰ-reind _ _ _)
        ∙ (≡in $ Pᴰ.⋆IdL _)

      ⋆Assocᴰ : ∀ {x y z}{xᴰ yᴰ zᴰ}{f : C.Hom[ z , y ]}{g : C.Hom[ y , x ]}{p : P.p[ x .lowerω ]}
        (fᴰ : Cᴰ.Hom[ f ][ zᴰ , yᴰ ])
        (gᴰ : Cᴰ.Hom[ g ][ yᴰ , xᴰ ])
        (pᴰ : p[ p ][ xᴰ .lowerω ])
        → ((fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ pᴰ) ∫≡ (fᴰ ⋆ᴰ gᴰ ⋆ᴰ pᴰ)
      ⋆Assocᴰ {x} {y} {z} {xᴰ} {yᴰ} {zᴰ} {f} {g} {p} fᴰ gᴰ pᴰ =
        reind-filler _
        ∙ (≡in $ sym $ ⋆ᴰ-reind _ _ _)
        ∙ (≡in $ Pᴰ.⋆Assoc (f , fᴰ , refl) (g , gᴰ , refl) pᴰ)

module _  where
  open SmallCategoryVariables
  module _
    {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
    {P : Presheaf C ℓP}
    where
    PSHᴰ = PRESHEAF (Cᴰ / P)
    module PSHᴰ = CategoryᴰNotation PSHᴰ
    module PSHISOᴰ = CategoryᴰNotation PSHᴰ.ISOCᴰ

module _  where
  open SmallCategoryᴰVariables
  module _
    {P : Presheaf C ℓP}
    (Pᴰ : Presheafᴰ {C = C} P Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ {C = C} P Cᴰ ℓQᴰ)
    where

    PshHomⱽ : Type _
    PshHomⱽ = PshHom {C = Cᴰ / P} Pᴰ Qᴰ

    PshIsoⱽ : Type _
    PshIsoⱽ = PshIso {C = Cᴰ / P} Pᴰ Qᴰ
