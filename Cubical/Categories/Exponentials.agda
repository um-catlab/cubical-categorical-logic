{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint.2Var
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as Redundant
import Cubical.Categories.Constructions.BinProduct as Separate
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C D : Category ℓC ℓC'

open Category

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (BinProductsWith C c) → Type _
  Exponential c d c×- = RightAdjointAt (BinProductWithF C c×-) d

  -- Profunctor for an object c being exponentiable
  ExponentiableProf : ∀ {c} (c×- : BinProductsWith C c) → Profunctor C C ℓC'
  ExponentiableProf c×- = RightAdjointProf (BinProductWithF _ c×-)

  Exponentiable : ∀ c → (c×- : BinProductsWith C c) → Type _
  Exponentiable c c×- = ∀ d → RightAdjointAt (BinProductWithF _ c×-) d

  module _ (bp : BinProducts C) where
    AllExponentiable : Type _
    AllExponentiable = ∀ c → Exponentiable c λ d → bp (d , c)

    ExponentialsProf : Profunctor ((C ^op) Redundant.×C C) C ℓC'
    ExponentialsProf =
      RightAdjointLProf (BinProductsNotation.×Bif bp) ∘F Redundant.Sym

    ExponentialAt : C .ob → C .ob → Type _
    ExponentialAt c d = UniversalElement C (ExponentialsProf ⟅ c , d ⟆)

    Exponentials : Type _
    Exponentials = UniversalElements ExponentialsProf

    open UniversalElement
    Exponentiable→Exponentials : ∀ {c} → Exponentiable c (λ d → bp (d , c))
      → ∀ {d} → ExponentialAt c d
    Exponentiable→Exponentials {c} c⇒ {d} .vertex = c⇒ d .vertex
    Exponentiable→Exponentials {c} c⇒ {d} .element = c⇒ d .element
    Exponentiable→Exponentials {c} c⇒ {d} .universal = c⇒ d .universal

    Exponentials→Exponentiable : Exponentials → ∀ {c} → Exponentiable c (λ d → bp (d , c))
    Exponentials→Exponentiable allExp {c} d .vertex = allExp (c , d) .vertex
    Exponentials→Exponentiable allExp {c} d .element = allExp (c , d) .element
    Exponentials→Exponentiable allExp {c} d .universal = allExp (c , d) .universal

    AnExponential : Exponentials → ∀ {c d} → Exponential c d λ c₁ → bp (c₁ , c)
    AnExponential exps = Exponentials→Exponentiable exps _

    AllExponentiable→Exponentials : AllExponentiable → Exponentials
    AllExponentiable→Exponentials allExp (c , d) =
      Exponentiable→Exponentials (allExp c)

    Exponentials→AllExponentiable : Exponentials → AllExponentiable
    Exponentials→AllExponentiable exps c = Exponentials→Exponentiable exps

  -- TODO: Exponential'' which doesn't rely on the existence of any products
  -- i.e. Exponential'' c d = UniversalElement (YO c 𝓟⇒ YO d)

module ExponentialNotation {C : Category ℓC ℓC'}{c d} -×c (exp : Exponential C c d -×c) where
  private
    module C = Category C
  module ⇒ue = UniversalElementNotation exp
  open ⇒ue
  open BinProductsWithNotation -×c

  vert : C .ob
  vert = vertex

  app : C [ vert ×a , d ]
  app = element

  app' : ∀ {Γ} → C [ Γ , vert ] → C [ Γ , c ] → C [ Γ , d ]
  app' f x = (f ,p x) C.⋆ app

  lda : ∀ {Γ} → C [ Γ ×a , d ] → C [ Γ , vert ]
  lda = intro

module ExponentiableNotation {C : Category ℓC ℓC'}{c}
  -×c
  (c⇒- : Exponentiable C c -×c) where
  -- open BinProductsNotation bp
  c⇒_ : C .ob → C .ob
  c⇒ d = c⇒- d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation -×c (c⇒- d) hiding (vert; module ⇒ue) public
  module ⇒ue d = ExponentialNotation.⇒ue -×c (c⇒- d)

module ExponentialsNotation {C : Category ℓC ℓC'} (bp : BinProducts C)
  (exps : AllExponentiable C bp) where
  open BinProductsNotation bp
  _⇒_ : C .ob → C .ob → C .ob
  c ⇒ d = exps c d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation (λ d' → bp (d' , c)) (exps c d) hiding (vert; module ⇒ue) public
  module ⇒ue c d = ExponentialNotation.⇒ue (λ d' → bp (d' , c)) (exps c d)

  ExponentialF : Functor ((C ^op) Redundant.×C C) C
  ExponentialF =
    FunctorComprehension
      (ExponentialsProf C bp)
      (AllExponentiable→Exponentials C bp exps)

  ExponentialBif : Bifunctor (C ^op) C C
  ExponentialBif = ExponentialF ∘Fb Redundant.ηBif _ _

  ExponentialF' : Functor ((C ^op) Separate.×C C) C
  ExponentialF' = BifunctorToParFunctor ExponentialBif

  private
    open Bifunctor
    -- Tests that show the exponential bifunctor has the desirable
    -- definitions
    good : ∀ {c c' d d'} (f : C [ c' , c ])(g : C [ d , d' ])
      → lda ((g ∘⟨ C ⟩ app' π₁ (f ∘⟨ C ⟩ π₂))) ≡ ExponentialBif ⟪ f , g ⟫×
    good f g = refl

    good-f : ∀ {c c' d} (f : C [ c' , c ])
      → lda (app' π₁ (f ∘⟨ C ⟩ π₂)) ≡ ExponentialBif .Bif-homL f d
    good-f f = refl

    good-g : ∀ {c d d'} (g : C [ d , d' ])
      → lda (g ∘⟨ C ⟩ app) ≡ ExponentialBif .Bif-homR c g
    good-g g = refl

-- Preservation of an exponential
module _ (F : Functor C D) {c : C .ob}
  (-×c : BinProductsWith C c)
  (F-pres-×c : preservesProvidedBinProductsWith F -×c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  where

  open import Cubical.Data.Sigma
  private
    module F = Functor F
    module C = Category C
    module D = Category D

  -- A bit of a misnomer because exponential is not a limit
  preservesExpCone : ∀ c' → PshHet F
    (ExponentiableProf C -×c ⟅ c' ⟆)
    (ExponentiableProf D -×Fc ⟅ F ⟅ c' ⟆ ⟆)
  preservesExpCone c' .fst Γ f⟨x⟩ = F⟨Γ×c⟩.intro Fc×FΓ.element D.⋆ F ⟪ f⟨x⟩ ⟫
    where
    module F⟨Γ×c⟩ = UniversalElementNotation
      -- NOTE: this has really bad inference :/
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F Γ c)
        (-×c Γ) (F-pres-×c Γ))
    module Fc×FΓ = UniversalElementNotation
      (-×Fc (F ⟅ Γ ⟆))
  preservesExpCone c' .snd Δ Γ γ f⟨x⟩ =
    D.⟨ refl ⟩⋆⟨ F.F-seq _ _ ⟩
    ∙ (sym $ D.⋆Assoc _ _ _)
    ∙ D.⟨
      F⟨Γ×c⟩.extensionality $
        ΣPathP $
          D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ (sym $ F.F-seq _ _)
                         ∙ cong F.F-hom (cong fst $ Γ×c.β)
                         ∙ F.F-seq _ _ ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
          ∙ D.⟨ cong fst $ F⟨Δ×c⟩.β ⟩⋆⟨ refl ⟩
          ∙ (sym $ cong fst $ FΓ×Fc.β)
          ∙ D.⟨ refl ⟩⋆⟨ sym $ cong fst $ F⟨Γ×c⟩.β ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
          ,
          D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨
            (sym $ F.F-seq _ _)
            ∙ (cong F.F-hom $ cong snd $ Γ×c.β)
            ⟩
          ∙ (cong snd $ F⟨Δ×c⟩.β)
          ∙ (sym $ cong snd $ FΓ×Fc.β)
          ∙ D.⟨ refl ⟩⋆⟨ sym $ cong snd $ F⟨Γ×c⟩.β ⟩
          ∙ (sym $ D.⋆Assoc _ _ _)
      ⟩⋆⟨ refl ⟩
    ∙ D.⋆Assoc _ _ _
    where
    module Γ×c = UniversalElementNotation (-×c Γ)
    module F⟨Γ×c⟩ = UniversalElementNotation
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F Γ c) (-×c Γ) ((F-pres-×c Γ)))
    module F⟨Δ×c⟩ = UniversalElementNotation
      (preservesUniversalElement→UniversalElement (preservesBinProdCones F Δ c) (-×c Δ) ((F-pres-×c Δ)))
    module FΓ×Fc = UniversalElementNotation
      (-×Fc (F ⟅ Γ ⟆))

  becomesExponential : {c' : C.ob} →
    (v : C.ob) →
    (e : PresheafNotation.p[ Functor.F-ob (ExponentiableProf C -×c) c' ] v) →
    Type _
  becomesExponential {c'} v e = becomesUniversal (preservesExpCone c') v e

  becomesExponential→Exponential : ∀ {c'}{v e}
    → becomesExponential {c' = c'} v e
    → Exponential D (F.F-ob c) (F.F-ob c') -×Fc
  becomesExponential→Exponential =
    becomesUniversal→UniversalElement (preservesExpCone _)

  preservesExponential : {c' : C.ob} → Exponential C c c' -×c → Type _
  preservesExponential {c'} e = becomesExponential vert app
    where open ExponentialNotation -×c e

-- TODO: preservation of all exponentials
