{-# OPTIONS --safe #-}
{-

  Given a displayed category Cᴰ over C, and any object x in C, we can
  construct the fiber category over x whose objects are the Cᴰ.ob[ x ]
  and whose morphisms are those that are over the identity.

-}

module Cubical.Categories.Constructions.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv hiding (fiber)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Constructions.HomPropertyOver
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.ChangeOfObjects
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Endo as Endo
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ (C : Category ℓC ℓC') (x : C .ob) where
  isId : Categoryᴰ (Endo C x) ℓ-zero ℓC'
  isId = HomPropertyOver→Catᴰ isIdDef where
    open HomPropertyOver
    isIdDef : HomPropertyOver (Endo C x) _
    isIdDef .Hom[_][-,-] = C .id ≡_
    isIdDef .isPropHomᴰ = λ _ → C .isSetHom _ _
    isIdDef .idᴰ = refl
    isIdDef ._⋆ᴰ_ f g f≡id g≡id =
      sym (C .⋆IdL _) ∙ cong₂ (C ._⋆_) f≡id g≡id

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  fiber : C .ob → Category ℓCᴰ (ℓ-max ℓC' ℓCᴰ')
  fiber x = ChangeOfObjects {X = Cᴰ.ob[ x ]}
    (∫C {C = Endo C x} (isId C x ×ᴰ reindex Cᴰ (Endo.π C x)))
    λ xᴰ → tt , (tt , xᴰ)

  private
    hom-test : ∀ x xᴰ yᴰ →
      fiber x [ xᴰ , yᴰ ]
      ≡ (Σ[ f ∈ C [ x , x ] ] (C .id ≡ f) × Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
    hom-test x xᴰ yᴰ = refl

  -- Homᴰ : ∀ {x y} → (f : C [ x , y ]) → fiber x o-[ _ ]-* fiber y
  -- Homᴰ f = mkBifunctorSep F where
  --   open BifunctorSep
  --   F : BifunctorSep _ _ _
  --   F .Bif-ob xᴰ yᴰ = (Σ[ f' ∈  singl f ] Cᴰ.Hom[ f' .fst ][ xᴰ , yᴰ ])
  --     , isSetΣ (isProp→isSet (isContr→isProp (isContrSingl _))) λ _
  --     → Cᴰ.isSetHomᴰ
  --   F .Bif-homL {c = xᴰ} = λ (id' , id≡id' , vᴰ) yᴰ ((f' , f≡f'), fᴰ) →
  --     (id' ⋆⟨ C ⟩ f' , sym (C .⋆IdL _) ∙ cong₂ (C ._⋆_) id≡id' f≡f')
  --     , (vᴰ Cᴰ.⋆ᴰ fᴰ)
  --   F .Bif-L-id = funExt
  --   (λ ((f' , f≡f'), fᴰ) → ΣPathP ((ΣPathP ((C .⋆IdL f') , {!!})) , {!!}))
  --   F .Bif-L-seq = {!!}
  --   F .Bif-homR {d' = yᴰ} = λ xᴰ (id' , id≡id' , vᴰ) ((f' , f≡f') , fᴰ) →
  --     ((f' ⋆⟨ C ⟩ id')
  --     , (sym (C .⋆IdR _) ∙ cong₂ (C ._⋆_) f≡f' id≡id'))
  --     , (fᴰ Cᴰ.⋆ᴰ vᴰ)
  --   F .Bif-R-id = {!!}
  --   F .Bif-R-seq = {!!}
  --   F .SepBif-RL-commute = {!!}
