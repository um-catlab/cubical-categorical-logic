{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More


open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Functor.Constant

open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Instances.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ
open Σω
open Liftω


module _
  {C : Category Cob CHom-ℓ}
  {Cobᴰ}{CHom-ℓᴰ}
  (Cᴰ : GloballySmallCategoryᴰ C Cobᴰ CHom-ℓᴰ)
  {Dᴰ-ℓ}{Dobᴰ}{DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ C Dᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    Cᴰ×Dᴰ = Cᴰ ×ᴰ Dᴰ
    module Cᴰ×Dᴰ = Categoryᴰ Cᴰ×Dᴰ
    module ∫Cᴰ×Dᴰ = Category Cᴰ×Dᴰ.∫C
  module _
    (obᴰᴰ-ℓ : (c : Cob) → Cobᴰ c → Level)
    (obᴰᴰ : ∀ (ccᴰdᴰ : ∫Cᴰ×Dᴰ.Ob) → Type (obᴰᴰ-ℓ (ccᴰdᴰ .fst) (ccᴰdᴰ .snd .fst)))
    (Hom-ℓᴰᴰ : (c c' : Cob) → (cᴰ : Cobᴰ c) → (cᴰ' : Cobᴰ c') → Level)
    where

    SmallFibersᴰCategoryᴰ : Typeω
    SmallFibersᴰCategoryᴰ =
      SmallFibersCategoryᴰ (∫C (Cᴰ ×ᴰ Dᴰ)) _
        obᴰᴰ
        (λ ccᴰd ccᴰd' →
          Hom-ℓᴰᴰ (ccᴰd .fst) (ccᴰd' .fst)
                  (ccᴰd .snd .fst) (ccᴰd' .snd .fst))

module _
  (C : Category Cob CHom-ℓ)
  {Cobᴰ}{CHom-ℓᴰ}
  (Cᴰ : GloballySmallCategoryᴰ C Cobᴰ CHom-ℓᴰ)
  {Dᴰ-ℓ}{Dobᴰ}{DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ C Dᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Cᴰ×Dᴰ = Categoryᴰ (Cᴰ ×ᴰ Dᴰ)
    module ∫Cᴰ×Dᴰ = Category Cᴰ×Dᴰ.∫C
  module _
    {obᴰᴰ-ℓ : (c : Cob) → Cobᴰ c → Level}
    {obᴰᴰ : ∀ (ccᴰdᴰ : ∫Cᴰ×Dᴰ.Ob) → Type (obᴰᴰ-ℓ (ccᴰdᴰ .fst) (ccᴰdᴰ .snd .fst))}
    {Hom-ℓᴰᴰ : (c c' : Cob) → (cᴰ : Cobᴰ c) → (cᴰ' : Cobᴰ c') → Level}
    where

    module _ (Cᴰᴰ : SmallFibersᴰCategoryᴰ Cᴰ Dᴰ obᴰᴰ-ℓ obᴰᴰ Hom-ℓᴰᴰ) where
      private
        module Cᴰᴰ = CategoryᴰNotation Cᴰᴰ
      module _ (c : Cob) (cᴰ : Cobᴰ c) where
        open Functor
        open Functorᴰ
        private
          open Section

          T : Section {D = Dᴰ.v[ c ]} (Constant c) Cᴰ
          T .F-obᴰ = λ d → cᴰ
          T .F-homᴰ = λ f → Cᴰ.idᴰ
          T .F-idᴰ = refl
          T .F-seqᴰ = λ _ _ → sym $ Cᴰ.⋆IdLᴰ _

          S : Section {D = Dᴰ.v[ c ]} (Constant c) (Cᴰ ×ᴰ Dᴰ)
          S = introS (Constant c) T (ConstantSection c)

          F : Functor Dᴰ.v[ c ] Cᴰ×Dᴰ.∫C
          F = intro S

        fibᴰF = F

        fibᴰ : Categoryᴰ Dᴰ.v[ c ] _ _
        fibᴰ = reindex F Cᴰᴰ

      module _ (c : Cob) (cᴰ : Cobᴰ c) where
        open Functor
        open Functorᴰ
        open Section
        module _
          (C-⋆ : ∀ {x} → C.id C.⋆ C.id Eq.≡ C.id {x = x}) where

          fibᴰEqF = fibᴰF c cᴰ ∘F fibEq→fib Dᴰ C-⋆ c

          module _
            (F-seq' :
              {x y z : Liftω (Dobᴰ c)} (f : Hom[ fibEq Dᴰ C-⋆ c , x ] y)
              (g : Hom[ fibEq Dᴰ C-⋆ c , y ] z) →
              (Cᴰ×Dᴰ.∫C ⋆ F-hom fibᴰEqF f) (F-hom fibᴰEqF g) Eq.≡
                F-hom fibᴰEqF ((fibEq Dᴰ C-⋆ c ⋆ f) g)) where

            fibᴰEq : Categoryᴰ (fibEq Dᴰ C-⋆ c) _ _
            fibᴰEq = reindexEq fibᴰEqF Cᴰᴰ (λ {x} → Eq.refl) F-seq'

module SmallFibersᴰNotation
  {C : Category Cob CHom-ℓ}
  {Cobᴰ}{CHom-ℓᴰ}
  {Cᴰ : GloballySmallCategoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ-ℓ}{Dobᴰ}{DHom-ℓᴰ}
  {Dᴰ : SmallFibersCategoryᴰ C Dᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {obᴰᴰ-ℓ obᴰᴰ Hom-ℓᴰᴰ}
  (Cᴰᴰ : SmallFibersᴰCategoryᴰ Cᴰ Dᴰ obᴰᴰ-ℓ obᴰᴰ Hom-ℓᴰᴰ)
  where
  private
    module Dᴰ = CategoryᴰNotation Dᴰ
  module _ (c : Cob) (cᴰ : Cobᴰ c) where
    vᴰ[_][_] : Categoryᴰ Dᴰ.v[ c ] _ _
    vᴰ[_][_] = fibᴰ C Cᴰ Dᴰ Cᴰᴰ c cᴰ

  open CategoryᴰNotation Cᴰᴰ public
