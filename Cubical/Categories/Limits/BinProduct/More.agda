{-# OPTIONS --safe --lossy-unification #-}
{-

  This is one of several possible definitions of the binary product.
  It turns out to be the best.

-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Bifunctor as R hiding (Fst; Snd)

open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' : Level

  _⊗_ = R._×C_

open Category
open Functor

module _ (C : Category ℓ ℓ') where
  BinProductProf' : Bifunctor C C (PresheafCategory C (ℓ-max ℓ' ℓ'))
  BinProductProf' = PshProd ∘Flr (YO , YO)

  BinProductProf : Profunctor (C ⊗ C) C ℓ'
  BinProductProf = R.rec _ _ BinProductProf'

  BinProduct : ∀ (cc' : (C ⊗ C) .ob) → Type _
  BinProduct cc' = UniversalElement C (BinProductProf ⟅ cc' ⟆)

  BinProducts : Type _
  BinProducts = UniversalElements BinProductProf

  -- Product with a fixed object
  module _ (c : C .ob) where
    ProdWithAProf : Profunctor C C ℓ'
    ProdWithAProf = appR BinProductProf' c

    BinProductsWith : Type (ℓ-max ℓ ℓ')
    BinProductsWith = UniversalElements ProdWithAProf

  module _ (bp : BinProducts) where
    BinProductF : Functor (C R.×C C) C
    BinProductF = FunctorComprehension BinProductProf bp

    BinProductBif : Bifunctor C C C
    BinProductBif = R.Functor→Bifunctor BinProductF

    BinProductF' : Functor (C ×C C) C
    BinProductF' = BifunctorToParFunctor BinProductBif

  module _ {a} (bp : BinProductsWith a) where
    BinProductWithF : Functor C C
    BinProductWithF = FunctorComprehension (ProdWithAProf a) bp

module BinProductNotation {C : Category ℓ ℓ'} {a b} (bp : BinProduct C (a , b)) where
  private
    module C = Category C
  module ×ue = UniversalElementNotation bp
  open ×ue
  vert = vertex

  π₁ : C [ vert , a ]
  π₁ = element .fst

  π₂ : C [ vert , b ]
  π₂ = element .snd

  infixr 4 _,p_
  _,p_ : ∀ {Γ} → C [ Γ , a ] → C [ Γ , b ] → C [ Γ , vert ]
  f₁ ,p f₂ = intro (f₁ , f₂)

  opaque
    ⟨_⟩,p⟨_⟩ :
      ∀ {Γ}
        {f f' : C [ Γ , a ]}
        {g g' : C [ Γ , b ]}
      → f ≡ f'
      → g ≡ g'
      → (f ,p g) ≡ (f' ,p g')
    ⟨ f≡f' ⟩,p⟨ g≡g' ⟩ = intro⟨ ΣPathP (f≡f' , g≡g') ⟩

    ,p≡ : ∀ {Γ} {f₁ : C [ Γ , a ]} {f₂ : C [ Γ , b ]} {g}
      → (f₁ ≡ g C.⋆ π₁)
      → (f₂ ≡ g C.⋆ π₂)
      → (f₁ ,p f₂) ≡ g
    ,p≡ f1≡ f2≡ = intro≡ (ΣPathP (f1≡ , f2≡))

    ,p-extensionality : ∀ {Γ} {f g : C [ Γ , vert ]}
      → (f C.⋆ π₁ ≡ g C.⋆ π₁)
      → (f C.⋆ π₂ ≡ g C.⋆ π₂)
      → f ≡ g
    ,p-extensionality f≡g1 f≡g2 = extensionality (ΣPathP (f≡g1 , f≡g2))

    ×β₁ : ∀ {Γ}{f : C [ Γ , a ]}{g} → (f ,p g) C.⋆ π₁ ≡ f
    ×β₁ = cong fst β

    ×β₂ : ∀ {Γ}{f : C [ Γ , a ]}{g} → (f ,p g) C.⋆ π₂ ≡ g
    ×β₂ = cong snd β

module BinProductsNotation {C : Category ℓ ℓ'} (bp : BinProducts C) where
  private
    module C = Category C
  _×_ : C .ob → C .ob → C .ob
  a × b = BinProductNotation.vert  (bp (a , b))
  module _ {a b : C .ob} where
    open BinProductNotation (bp (a , b)) hiding (vert; module ×ue) public
  module ×ue (a b : C .ob) = BinProductNotation.×ue (bp (a , b))

  ×F' : Functor (C R.×C C) C
  ×F' = BinProductF C bp

  ×Bif : Bifunctor C C C
  ×Bif = BinProductBif C bp

  ×F : Functor (C ×C C) C
  ×F = BifunctorToParFunctor ×Bif

  _×p_ : ∀ {a b c d} → C [ a , b ] → C [ c , d ] → C [ a × c , b × d ]
  f ×p g = ×Bif ⟪ f , g ⟫×

  π₁Nat : BinProductF' C bp ⇒ Fst C C
  π₁Nat .NatTrans.N-ob _ = π₁
  π₁Nat .NatTrans.N-hom _ = ×β₁

module BinProductsWithNotation {C : Category ℓ ℓ'}{a} (bp : BinProductsWith C a) where
  _×a : C .ob → C .ob
  b ×a  = BinProductNotation.vert (bp b)
  module _ {b : C .ob} where
    open BinProductNotation (bp b) hiding (vert) public

  ×aF : Functor C C
  ×aF = BinProductWithF C bp

private
  variable
    C D : Category ℓ ℓ'
module _ (F : Functor C D) where
  preservesBinProdCones : ∀ c c'
    → PshHomᴰ F (BinProductProf C ⟅ c , c' ⟆)
                (BinProductProf D ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
  preservesBinProdCones c c' .fst Γ (f , f') = F ⟪ f ⟫ , F ⟪ f' ⟫
  preservesBinProdCones c c' .snd Δ Γ γ (f , f') = ΣPathP ((F .F-seq γ f) , (F .F-seq γ f'))

  preservesBinProduct : ∀ {c c'} → BinProduct C (c , c') → Type _
  preservesBinProduct = preservesUniversalElement (preservesBinProdCones _ _)

  -- If you have all BinProductsWith, you should probably use the next
  -- one instead
  preservesBinProductsWith : ∀ (c : C .ob) → Type _
  preservesBinProductsWith c = ∀ c'
    → preservesUniversalElements (preservesBinProdCones c c')

  -- In practice this definition is usually nicer to work with than
  -- the previous.
  preservesProvidedBinProductsWith :
    ∀ {c : C .ob} → (-×c : BinProductsWith C c) → Type _
  preservesProvidedBinProductsWith -×c = ∀ c'
    → preservesUniversalElement (preservesBinProdCones c' _) (-×c c')

  preservesProvidedBinProducts :
    BinProducts C → Type _
  preservesProvidedBinProducts bp =
    ∀ c c'
    → preservesUniversalElement
        (preservesBinProdCones c c')
        (bp (c , c'))
