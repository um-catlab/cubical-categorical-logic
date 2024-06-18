{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Redundant as R

open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' : Level

  _⊗_ = R._×C_

open Iso
open UniversalElement
open BinProduct
open Category
open Functor
open Bifunctor
open isEquiv

module _ (C : Category ℓ ℓ') where
  BinProduct' = RightAdjointAt' _ _ (Δ C)
  BinProducts' = RightAdjoint' _ _ (Δ C)

  private
    -- This definition looks promising at first, but doesn't give the
    -- right behavior for BinProductWithF ⟪_⟫
    BadBinProductProf : Profunctor (C R.×C C) C ℓ'
    BadBinProductProf =
      (precomposeF _ (Δ C ^opF) ∘F YO) ∘F R.RedundantToProd C C

  BinProductProf : Profunctor (C ⊗ C) C ℓ'
  BinProductProf = R.rec _ _ (PshProd ∘Flr (YO , YO))

  -- Product with a fixed object
  ProdWithAProf : C .ob → Profunctor C C ℓ'
  ProdWithAProf a = BinProductProf ∘F R.ob-× C C a

  BinProductToRepresentable : ∀ {a b} → BinProduct C a b
    → UniversalElement C (BinProductProf ⟅ a , b ⟆)
  BinProductToRepresentable bp .vertex = bp .binProdOb
  BinProductToRepresentable bp .element = (bp .binProdPr₁) , (bp .binProdPr₂)
  BinProductToRepresentable bp .universal A .equiv-proof (f1 , f2) .fst .fst =
    bp .univProp f1 f2 .fst .fst
  BinProductToRepresentable bp .universal A .equiv-proof (f1 , f2) .fst .snd =
    cong₂ _,_ (bp .univProp f1 f2 .fst .snd .fst)
              ((bp .univProp f1 f2 .fst .snd .snd))
  BinProductToRepresentable bp .universal A .equiv-proof (f1 , f2) .snd y =
    Σ≡Prop (λ _ → isSet× (isSetHom C) (isSetHom C) _ _)
      (cong fst (bp .univProp f1 f2 .snd ((y .fst) , PathPΣ (y .snd))))

  module _ (bp : BinProducts C) where
    BinProductsToUnivElts : UniversalElements BinProductProf
    BinProductsToUnivElts c = BinProductToRepresentable (bp (c .fst) (c .snd))

    BinProductF : Functor (C R.×C C) C
    BinProductF = FunctorComprehension BinProductsToUnivElts

    BinProductBif : Bifunctor C C C
    BinProductBif = R.Functor→Bifunctor BinProductF

  private
    variable
      a b c d : C .ob
      f g h : C [ a , b ]


  module _ {a} (bp : ∀ b → BinProduct C a b) where
    BinProductWithToRepresentable : UniversalElements (ProdWithAProf a)
    BinProductWithToRepresentable b = BinProductToRepresentable (bp b)

    BinProductWithF =
      FunctorComprehension BinProductWithToRepresentable

    -- test definitional behavior
    _ : ∀ {b b'}(f : C [ b , b' ]) →
        BinProductWithF ⟪ f ⟫ ≡
          bp b' .univProp (bp b .binProdPr₁)
            (f ∘⟨ C ⟩ bp b .binProdPr₂) .fst .fst
    _ = λ f → refl
    module ProdsWithNotation where
      open UniversalElementNotation {C = C}
      private
        ues = BinProductWithToRepresentable
      a×_ : C .ob → C .ob
      a× b = ues b .vertex

      π₁ : C [ a× b , a ]
      π₁ {b} = ues b .element .fst

      π₂ : C [ a× b , b ]
      π₂ {b} = ues b .element .snd

      _,p_ : C [ c , a ] → C [ c , b ] → C [ c , a× b ]
      f ,p g = ues _ .universal _ .equiv-proof (f , g) .fst .fst

      ×pF = BinProductWithF
      ×p_ : C [ b , c ] → C [ a× b , a× c ]
      ×p_ = BinProductWithF .F-hom

      ×β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
      ×β₁ = cong fst (ues _ .universal _ .equiv-proof _ .fst .snd)

      ×β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
      ×β₂ = cong snd (ues _ .universal _ .equiv-proof _ .fst .snd)

      ×η : f ≡ ((π₁ ∘⟨ C ⟩ f) ,p (π₂ ∘⟨ C ⟩ f))
      ×η = η (ues _)

      ×η' : C .id {x = a× b} ≡ (π₁ ,p π₂)
      ×η' = weak-η (ues _)

      ,p-natural : ( f ,p g ) ∘⟨ C ⟩ h ≡ ((f ∘⟨ C ⟩ h) ,p (g ∘⟨ C ⟩ h))
      ,p-natural = intro-natural (ues _)

      ×-extensionality : π₁ ∘⟨ C ⟩ f ≡
                         π₁ ∘⟨ C ⟩ g → π₂ ∘⟨ C ⟩ f ≡ π₂ ∘⟨ C ⟩ g → f ≡ g
      ×-extensionality p1 p2 = extensionality (ues _) (ΣPathP (p1 , p2))
  module Notation (bp : BinProducts C) where
    private
      ues = BinProductsToUnivElts bp
    open UniversalElementNotation {C = C}

    _×_ : C .ob → C .ob → C .ob
    a × b = bp a b .binProdOb

    -- TODO: π₁, π₂ are natural transformations as well,
    -- which should follow by general fact that universal elements are natural

    π₁ : C [ a × b , a ]
    π₁ {a}{b} = bp a b .binProdPr₁

    π₂ : C [ a × b , b ]
    π₂ {a}{b} = bp a b .binProdPr₂

    _,p_ : C [ c , a ] → C [ c , b ] → C [ c , a × b ]
    f ,p g = bp _ _ . univProp f g .fst .fst

    ×pF = BinProductF bp

    ×Bif : R.Bifunctor C C C
    ×Bif = BinProductBif bp

    _×p_ : C [ a , b ] → C [ c , d ] → C [ a × c , b × d ]
    f ×p g = ×Bif ⟪ f , g ⟫×
    private
      open R.Bifunctor
      -- Demonstrating the definitional behavior of ×Bif
      _ : ((f ∘⟨ C ⟩ π₁) ,p (g ∘⟨ C ⟩ π₂)) ≡ (×Bif ⟪ f , g ⟫×)
      _ = refl

      _ : ((f ∘⟨ C ⟩ π₁) ,p π₂) ≡ (Bif-homL ×Bif f d)
      _ = refl

      _ : (π₁ ,p (g ∘⟨ C ⟩ π₂)) ≡ (Bif-homR ×Bif c g)
      _ = refl

    ×β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
    ×β₁ {f = f}{g = g} = cong fst (β (ues _))

    ×β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
    ×β₂ {f = f}{g = g} = cong snd (β (ues _))

    ×η : f ≡ ((π₁ ∘⟨ C ⟩ f) ,p (π₂ ∘⟨ C ⟩ f))
    ×η {f = f} = η (ues _)

    ×η' : C .id {a × b} ≡ (π₁ ,p π₂)
    ×η' = weak-η (ues _)

    ,p-natural : ( f ,p g ) ∘⟨ C ⟩ h ≡ ((f ∘⟨ C ⟩ h) ,p (g ∘⟨ C ⟩ h))
    ,p-natural {f = f}{g = g}{h = h} = intro-natural (ues _)

    -- this has the benefit of always applying
    ×-extensionality : π₁ ∘⟨ C ⟩ f ≡ π₁ ∘⟨ C ⟩ g
                     → π₂ ∘⟨ C ⟩ f ≡ π₂ ∘⟨ C ⟩ g
                     → f ≡ g
    ×-extensionality p1 p2 = extensionality (ues _) (ΣPathP (p1 , p2))

    module _ (Γ : C .ob) where
      module PWN = ProdsWithNotation (bp Γ)
      ×pF-with-agrees : ×Bif ⟪ C .id , f ⟫× ≡ PWN.×pF ⟪ f ⟫
      ×pF-with-agrees = sym (×Bif .Bif-R×-agree _)

module _ {C : Category ℓ ℓ'} where
  -- meant to be used as `module c×c' = Binproduct'Notation prod`
  module BinProduct'Notation {c c' : C .ob}
    (prod : BinProduct' C (c , c')) where
    vert : C .ob
    vert = prod .vertex
    π₁ : C [ vert , c ]
    π₁ = prod .element .fst
    π₂ : C [ vert , c' ]
    π₂ = prod .element .snd
    ⟨_,_⟩ : ∀{z} → C [ z , c ] → C [ z , c' ] → C [ z , vert ]
    ⟨_,_⟩ {z} f g = invIsEq (prod .universal z) (f , g)
    β : ∀{z f g} → (⟨ f , g ⟩ ⋆⟨ C ⟩ π₁ , ⟨ f , g ⟩ ⋆⟨ C ⟩ π₂) ≡ (f , g)
    β {z} {f} {g} = secIsEq (prod .universal z) (f , g)
    η : ∀{z}{h : C [ z , (prod .vertex) ]} →
      ⟨ h ⋆⟨ C ⟩ π₁ , h ⋆⟨ C ⟩ π₂ ⟩ ≡ h
    η {z} {h} = retIsEq (prod .universal z) h

  module BinProducts'Notation (prods : BinProducts' C) where
    private module c×c' = BinProduct'Notation
    _×_ : (x y : C .ob) → C .ob
    x × y = c×c'.vert (prods (x , y))
    π₁ : ∀{x y} → C [ x × y , x ]
    π₁ {x} {y} = c×c'.π₁ (prods (x , y))
    π₂ : ∀{x y} → C [ x × y , y ]
    π₂ {x} {y} = c×c'.π₂ (prods (x , y))
    ⟨_,_⟩ : ∀{z x y} → C [ z , x ] → C [ z , y ] → C [ z , x × y ]
    ⟨_,_⟩ {z} {x} {y} f g = c×c'.⟨_,_⟩ (prods (x , y)) f g
    β : ∀{z x y f g} → (⟨ f , g ⟩ ⋆⟨ C ⟩ π₁ , ⟨ f , g ⟩ ⋆⟨ C ⟩ π₂) ≡ (f , g)
    β {z} {x} {y} {f} {g} = secIsEq (prods (x , y) .universal z) (f , g)
    η : ∀{z x y}{h : C [ z , (prods (x , y) .vertex) ]} →
      ⟨ h ⋆⟨ C ⟩ π₁ , h ⋆⟨ C ⟩ π₂ ⟩ ≡ h
    η {z} {x} {y} {h} = retIsEq (prods (x , y) .universal z) h

  module _ (prods : BinProducts' C) where
    open BinProducts'Notation prods
    BinProducts'→BinProducts : BinProducts C
    BinProducts'→BinProducts x y .binProdOb = prods (x , y) .vertex
    BinProducts'→BinProducts x y .binProdPr₁ = π₁
    BinProducts'→BinProducts x y .binProdPr₂ = π₂
    BinProducts'→BinProducts x y .univProp {z = z} f g =
      uniqueExists ⟨ f , g ⟩
      (congS fst β , congS snd β)
      (λ _ _ _ → ≡-× (C .isSetHom _ _ _ _) (C .isSetHom _ _ _ _))
      λ _ p → (sym η ∙
        congS (λ (x , y) → ⟨ x , y ⟩) β ∙
        congS (λ x → ⟨ x , _ ⟩) (sym (p .fst)) ∙
        congS (λ x → ⟨ _ , x ⟩) (sym (p .snd))) ∙
        η
