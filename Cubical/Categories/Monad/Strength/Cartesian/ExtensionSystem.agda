{-
   Strong monads on cartesian categories as extension systems,
   i.e., in terms of unit and bind, deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Monad.Strength.Cartesian.ExtensionSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Comonad.Instances.Environment
open import Cubical.Categories.Monad.ExtensionSystem as Monad
open import Cubical.Categories.Comonad.ExtensionSystem as
  Comonad renaming (pull to comonad-pull)
open import Cubical.Categories.Isomorphism

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} (bp : BinProducts C) where
  open Category
  open Notation C bp
  open EnvNotation bp

  private
    variable
      Γ Δ a b c : C .ob
      γ δ : C [ Δ , Γ ]
      f g : C [ a , b ]
      s t : With Γ [ a , b ]

  -- With is a fibered category over C. With : C → Cat
  -- A Strong extension system is a section of this bundle of categories
  open ExtensionSystemFor
  record StrongExtensionSystem : Type (ℓ-max ℓ ℓ') where
    field
      T : C .ob → C .ob
      systems : ∀ Γ → Monad.ExtensionSystemFor (With Γ) T
      -- η ∘ (γ × id) ≡ η
      η-natural : (γ ^*) ⟪ systems Γ .η {a = a} ⟫ ≡ systems Δ .η
      -- bind f ∘ (γ × id) ≡ bind (f ∘ (γ × id))
      bind-natural :
        (γ ^*) ⟪ systems Γ .bind s ⟫ ≡ systems Δ .bind ((γ ^*) ⟪ s ⟫)

  -- | TODO: resulting η, bind are natural in all arguments
  -- If C further has a terminal object we get an "underlying monad"
  -- on C because Envs 𝟙 ≅ Id
  module _ (term : Terminal C) (SE : StrongExtensionSystem) where
    open StrongExtensionSystem SE
    open TerminalNotation C term
    open CartesianCategoryNotation (C , term , bp)
    open isIso
    -- This follows abstractly from showing (𝟙 ×-) is equivalent to
    -- the identity monad
    -- we'll just be explicit here

    E1 = systems 𝟙
    -- f ∘ π₂
    toWith1 : C [ a , b ] → With 𝟙 [ a , b ]
    toWith1 = C ._⋆_ (unitor-l .fst)

    -- f ∘ (! , id)
    fromWith1 : With 𝟙 [ a , b ] → C [ a , b ]
    fromWith1 = C ._⋆_ (unitor-l .snd .inv)

    fromTo : fromWith1 (toWith1 f) ≡ f
    fromTo =
      sym (C .⋆Assoc _ _ _) ∙
      cong₂ (comp' C) refl (unitor-l .snd .sec) ∙ C .⋆IdL _

    toFrom : toWith1 (fromWith1 f) ≡ f
    toFrom =
      sym (C .⋆Assoc _ _ _) ∙
      cong₂ (comp' C) refl (unitor-l .snd .ret) ∙ C .⋆IdL _

    -- TODO: recover a monad on the original category
    -- General principle would be that you can transport a monad
    -- along an equivalence of categories...
    global-ESF : Monad.ExtensionSystemFor C T
    global-ESF .η = fromWith1 (E1 .η)
    global-ESF .bind s = fromWith1 (E1 .bind (toWith1 s))
    global-ESF .bind-r =
      cong fromWith1 (cong (E1 .bind) toFrom) ∙
      cong fromWith1 (E1 .bind-r) ∙ ×β₂
    global-ESF .bind-l {f = f} =
      -- (f o π₂)^+ ∘ (!,id) ∘ η ∘ (!, id)
      -- (f o π₂)^+ ∘ (!,η) ∘ η ∘ (!, id)
      ((C .⋆Assoc _ _ _) ∙ cong₂ (seq' C) refl
        (sym (C .⋆Assoc _ _ _) ∙
        cong₂ (seq' C)
              (,p-natural ∙ cong₂ _,p_ (𝟙η' {g = π₁}) (C .⋆IdR _)) refl ∙
              E1 .bind-l {f = (toWith1 f)} ))
      ∙ sym (C .⋆Assoc _ _ _) ∙ cong₂ (comp' C) refl ×β₂ ∙ C .⋆IdL _
    -- ((f ∘ π₂)^+ ∘ (! , id)) ∘ ((g ∘ π₂)^+ ∘ (! , id))
    global-ESF .bind-comp {f = f}{g = g} =
    -- ((f ∘ π₂)^+ ∘ (! , id)) ∘ ((g ∘ π₂)^+ ∘ (! , id))
      lem -- f ∘𝟙 g = f^+
    -- ((f ∘ π₂)^+ ∘ (π₁ , (g ∘ π₂)^+)) ∘ (! , id)
      ∙ cong₂ (seq' C) refl (cong₂ (comp' C) refl
        (,p-natural ∙ cong₂ _,p_ (𝟙η' {g = π₁}) (C .⋆IdR _)) ∙ E1 .bind-comp)
      ∙ cong₂ (seq' C) refl (cong (E1 .bind)
              -- (E1 .bind (toWith1 f)) ∘ (π₁ , (g ∘ π₂))
              -- ≡ (E1 .bind (toWith f) ∘ g ∘ π₂)
              ((cong₂ (comp' C) refl (cong₂ _,p_ 𝟙η' (sym (C .⋆IdR _)) ∙
              sym ,p-natural) ∙ C .⋆Assoc _ _ _) ∙ C .⋆Assoc _ _ _))
    -- (((f ∘ π₂)^+ ∘ (! , id) ∘ g) ∘ π₂)^+ ∘ (! , id)
      where
        lem : comp' C (fromWith1 (E1 .bind (toWith1 f)))
              (fromWith1 (E1 .bind (toWith1 g))) ≡
              ((E1 .bind (toWith1 f)) ∘⟨ C ⟩
                ((!t ,p C .id) ∘⟨ C ⟩ E1 .bind (toWith1 g))) ∘⟨ C ⟩
                  ((!t ,p C .id))
        lem = solveCat! C
    StrongMonad→Monad : Monad.ExtensionSystem C
    StrongMonad→Monad = T , global-ESF

    -- TODO: once we establish that T is a functor,
    -- we can show the following is natural
    σ : C [ Γ × T a , T (Γ × a) ]
    σ {Γ = Γ} = systems Γ .bind (fromWith1 (E1 .η))
module StrongMonadNotation {C : Category ℓ ℓ'}
  (bp : BinProducts C) (SE : StrongExtensionSystem bp) where
  open Category
  open Notation C bp
  open EnvNotation bp
  open StrongExtensionSystem SE public
  private
    variable
      Γ Δ a b c : C .ob
      γ δ : C [ Δ , Γ ]
      f g : C [ a , b ]
      s t : With Γ [ a , b ]

  open Functor

  PKleisli : C .ob → Category _ _
  PKleisli Γ = Monad.Kleisli (With Γ) (T , systems Γ)

  PG : (Γ : C .ob) → Functor (PKleisli Γ) (With Γ)
  PG Γ = Monad.G ((With Γ)) ((T , systems Γ))

  bindP : PKleisli Γ [ a , b ] → With Γ [ T a , T b ]
  bindP {Γ = Γ} = PG Γ .F-hom

  retP : PKleisli Γ [ a , a ]
  retP {Γ} = PKleisli Γ .id

  bindP-comp : bindP f ∘⟨ With Γ ⟩ bindP g ≡ bindP (bindP f ∘⟨ With Γ ⟩ g)
  bindP-comp {Γ = Γ} = ExtensionSystemFor.bind-comp (systems Γ)

  bindP-l : bindP f ∘⟨ With Γ ⟩ retP ≡ f
  bindP-l {Γ = Γ} = ExtensionSystemFor.bind-l (systems Γ)

  bindP-r : bindP (retP {a = a}) ≡ With Γ .id
  bindP-r {Γ = Γ} = ExtensionSystemFor.bind-r (systems Γ)

  open Functor

  pull : (γ : C [ Δ , Γ ]) → Functor (PKleisli Γ) (PKleisli Δ)
  pull γ .F-ob = λ z → z
  pull γ .F-hom f = (γ ^*) ⟪ f ⟫
  pull γ .F-id = η-natural
  pull {Δ = Δ} γ .F-seq f g =
    (γ ^*) .F-seq _ _ ∙ cong₂ (seq' (With Δ)) refl bind-natural
