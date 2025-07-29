{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base as Prod
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Adjoint.2Var
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C D : Category ℓC ℓC'

open Category
open isEquiv

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (∀ (e : C .ob) → BinProduct C c e) → Type _
  Exponential c d c×- = RightAdjointAt (BinProductWithF _ c×-) d

  Exponential'Prof : ∀ {c} (c×- : hasAllBinProductWith C c) → Profunctor C C ℓC'
  Exponential'Prof c×- = RightAdjointProf (a×-F C c×-)

  Exponential'Psh :  ∀ {c} (c×- : hasAllBinProductWith C c) → (d : C .ob)
    → Presheaf C ℓC'
  Exponential'Psh c×- d = Exponential'Prof c×- ⟅ d ⟆

  Exponential' : (c d : C .ob) → (c×- : hasAllBinProductWith C c) → Type _
  Exponential' c d c×- = RightAdjointAt (a×-F C c×-) d

  -- TODO: Exponential'' which doesn't rely on the existence of any products
  -- i.e. Exponential'' c d = UniversalElement (YO c 𝓟⇒ YO d)

  module ExponentialNotation {c d} c×- (exp : Exponential c d c×-) where
    open UniversalElementNotation exp public
    open ProdsWithNotation C c×- public
    c⇒d : C .ob
    c⇒d = vertex

    app : C [ a× c⇒d , d ]
    app = element

    lda : ∀ {Γ} → C [ a× Γ , d ] → C [ Γ , c⇒d ]
    lda = intro

    -- this is to test we have the expected definition
    β⇒ : ∀ {Γ} → (f : C [ a× Γ , d ])
      → π₁ ,p (π₂ ⋆⟨ C ⟩ lda f) ⋆⟨ C ⟩ app ≡ f
    β⇒ f = β {p = f}

    η⇒ : ∀ {Γ} → (f : C [ Γ , c⇒d ])
      → f ≡ lda ((π₁ ,p (π₂ ⋆⟨ C ⟩ f)) ⋆⟨ C ⟩ app)
    η⇒ f = η {f = f}

  module _ (bp : BinProducts C) where
    open Notation C bp
    Exponentials : Type _
    Exponentials = RightAdjointL ×Bif

    ExponentialF : Exponentials → Functor ((C ^op) ×C C) C
    ExponentialF exps =
      FunctorComprehension (RightAdjointLProf ×Bif) exps ∘F Prod.Sym
    open UniversalElement

    module ExpsNotation (exp : Exponentials) where
      _⇒_ : C .ob → C .ob → C .ob
      c ⇒ d = exp (d , c) .vertex

      app : ∀ {c d} → C [ (c ⇒ d) × c , d ]
      app {c}{d} = exp (d , c) .element

      lda : ∀ {Γ c d} → C [ Γ × c , d ] → C [ Γ , c ⇒ d ]
      lda  f = exp _ .universal _ .equiv-proof f .fst .fst

      app' : ∀ {Γ c d} → C [ Γ , c ⇒ d ] → C [ Γ , c ] → C [ Γ , d ]
      app' f x = app ∘⟨ C ⟩ (f ,p x)

      ExponentialBif : Bifunctor (C ^op) C C
      ExponentialBif = ExponentialF exp ∘Fb ηBif (C ^op) C
      private
        open Bifunctor
        -- Tests that show the exponential bifunctor has the desirable
        -- definitions
        good : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
            → lda
                (g ∘⟨ C ⟩ (app' π₁ (f ∘⟨ C ⟩ π₂))) ≡ ExponentialBif ⟪ f , g ⟫×
        good f g = refl

        good-f : ∀ {c c' d} (f : C [ c' , c ])
            → lda (app' π₁ (f ∘⟨ C ⟩ π₂)) ≡ ExponentialBif .Bif-homL f d
        good-f f = refl

        good-g : ∀ {c d d'} (g : C [ d , d' ])
            → lda (g ∘⟨ C ⟩ app) ≡ ExponentialBif .Bif-homR c g
        good-g g = refl

-- Preservation of an exponential
module _ (F : Functor C D) {c : C .ob}
  (c×- : hasAllBinProductWith C c)
  (F-pres-c×- : preservesProvidedBinProductsWith F c×-)
  (Fc×- : hasAllBinProductWith D (F ⟅ c ⟆))
  where

  open import Cubical.Data.Sigma
  private
    module F = Functor F
    module C = Category C
    module D = Category D

  -- A bit of a misnomer because exponential is not a limit
  preservesExpCone : ∀ c' → PshHomᴰ F
    (Exponential'Psh C c×- c')
    (Exponential'Psh D Fc×- (F ⟅ c' ⟆))
  preservesExpCone c' .fst Γ f⟨x⟩ = F⟨c×Γ⟩.intro Fc×FΓ.element D.⋆ F ⟪ f⟨x⟩ ⟫
    where
    module F⟨c×Γ⟩ = UniversalElementNotation
      -- NOTE: this has really bad inference :/
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F c Γ)
        (c×- Γ) (F-pres-c×- Γ))
    module Fc×FΓ = UniversalElementNotation
      (Fc×- (F ⟅ Γ ⟆))
  preservesExpCone c' .snd Δ Γ γ f⟨x⟩ =
    D.⟨ refl ⟩⋆⟨ F.F-seq _ _ ⟩
    ∙ (sym $ D.⋆Assoc _ _ _)
    ∙ D.⟨
      F⟨c×Γ⟩.extensionality $
        ΣPathP $
          D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ (sym $ F.F-seq _ _) ∙ cong F.F-hom (cong fst $ c×Γ.β) ⟩
          ∙ (cong fst $ F⟨c×Δ⟩.β)
          ∙ (sym $ cong fst $ Fc×FΓ.β)
          ∙ D.⟨ refl ⟩⋆⟨ sym $ cong fst $ F⟨c×Γ⟩.β ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
          ,
          D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨
            (sym $ F.F-seq _ _)
            ∙ (cong F.F-hom $ cong snd $ c×Γ.β)
            ∙ F.F-seq _ _ ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
          ∙ D.⟨ cong snd $ F⟨c×Δ⟩.β ⟩⋆⟨ refl ⟩
          ∙ (sym $ cong snd $ Fc×FΓ.β)
          ∙ D.⟨ refl ⟩⋆⟨ sym $ cong snd $ F⟨c×Γ⟩.β ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
      ⟩⋆⟨ refl ⟩
    ∙ D.⋆Assoc _ _ _
    where
    module c×Γ = UniversalElementNotation (c×- Γ)
    module F⟨c×Γ⟩ = UniversalElementNotation
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F c Γ) (c×- Γ) ((F-pres-c×- Γ)))
    module F⟨c×Δ⟩ = UniversalElementNotation
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F c Δ) (c×- Δ) ((F-pres-c×- Δ)))
    module Fc×FΓ = UniversalElementNotation
      (Fc×- (F ⟅ Γ ⟆))

  preservesExponential' : {c' : C.ob} → Exponential' C c c' c×- → Type _
  preservesExponential' {c'} = preservesUniversalElement (preservesExpCone c')
