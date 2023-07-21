{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
import Cubical.Categories.Constructions.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Redundant as R

open import Cubical.Categories.Presheaf.More

private
  variable
    ℓ ℓ' : Level

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

  BinProductToRepresentable : ∀ {a b} → BinProduct C a b →
                              RightAdjointAt _ _ (Δ C) (a , b)
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
    BinProductsToUnivElts : RightAdjoint C (C ×C C) (Δ C)
    BinProductsToUnivElts c = BinProductToRepresentable (bp (c .fst) (c .snd))

    ProdProf : C o-[ ℓ' ]-* (C ×C C)
    ProdProf = Functor→Profo-* C (C ×C C) (Δ C)

    ProdProf' : C o-[ (ℓ-max ℓ ℓ') ]-* (C R.×C C)
    ProdProf' = Functor→Profo-* C (C R.×C C) (R.ProdToRedundant C C ∘F Δ C)

    BinProductF : Functor (C ×C C) C
    BinProductF = FunctorComprehension _ _ _ BinProductsToUnivElts .fst

  private
    variable
      a b c d : C .ob
      f g h : C [ a , b ]

  module _ {a} (bp : ∀ b → BinProduct C a b) where
    -- ProdAProf [ c , b ] = C [ c , a ] × C [ c , b ]
    ProdAProf : C o-[ ℓ' ]-* C
    ProdAProf = _o×_ {C = C} (appR (HomBif C) a) (HomBif C)

    BinProductWithToRepresentable : UniversalElements C C ProdAProf
    BinProductWithToRepresentable b .vertex = bp b .binProdOb
    BinProductWithToRepresentable b .element .fst = bp b .binProdPr₁
    BinProductWithToRepresentable b .element .snd = bp b .binProdPr₂
    BinProductWithToRepresentable b .universal c .equiv-proof (f1 , f2)
      .fst .fst = bp b .univProp f1 f2 .fst .fst
    BinProductWithToRepresentable b .universal c .equiv-proof (f1 , f2)
      .fst .snd =
      cong₂ _,_ (bp b .univProp f1 f2 .fst .snd .fst)
                (bp b .univProp f1 f2 .fst .snd .snd)
    BinProductWithToRepresentable b .universal c .equiv-proof (f1 , f2) .snd y =
      Σ≡Prop
      (λ x → isSet× (isSetHom C) (isSetHom C) _ _)
      (cong fst ( bp b .univProp f1 f2 .snd ((y .fst) , PathPΣ (y .snd))))

    BinProductWithF =
      FunctorComprehension _ _ _ BinProductWithToRepresentable .fst

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

      -- TODO: π₁, π₂ are natural transformations as well,
      -- which should follow by general fact that universal elements are natural

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
      ues : RightAdjointAt C (C ×C C) (Δ C) (a , b)
      ues = BinProductsToUnivElts bp _
    open UniversalElementNotation {C = C}

    _×_ : C .ob → C .ob → C .ob
    a × b = bp a b .binProdOb

    π₁ : C [ a × b , a ]
    π₁ {a}{b} = bp a b .binProdPr₁

    π₂ : C [ a × b , b ]
    π₂ {a}{b} = bp a b .binProdPr₂

    _,p_ : C [ c , a ] → C [ c , b ] → C [ c , a × b ]
    f ,p g = bp _ _ . univProp f g .fst .fst

    ×pF = BinProductF bp

    _×p_ : C [ a , b ] → C [ c , d ] → C [ a × c , b × d ]
    f ×p g = (f ∘⟨ C ⟩ π₁) ,p (g ∘⟨ C ⟩ π₂)

    ×Bif : R.Bifunctor C C C
    ×Bif = R.mkBifunctorParAx B where
      open R.BifunctorParAx
      B : R.BifunctorParAx C C C
      B .Bif-ob = _×_
      B .Bif-homL f d = (f ∘⟨ C ⟩ π₁) ,p π₂
      B .Bif-homR c g = π₁ ,p (g ∘⟨ C ⟩ π₂)
      B .Bif-hom× = _×p_
      B .Bif-×-id = ×pF .F-id
      B .Bif-×-seq f f' g g' = ×pF .F-seq (f , g) (f' , g')
      B .Bif-L×-agree f = cong₂ _,p_ refl (sym (C .⋆IdR _))
      B .Bif-R×-agree g = cong₂ _,p_ (sym (C .⋆IdR _)) refl

    private
      open R.Bifunctor
      -- Demonstrating the definitional behavior of ×Bif
      _ : ((f ∘⟨ C ⟩ π₁) ,p (g ∘⟨ C ⟩ π₂)) ≡ (Bif-hom× ×Bif f g)
      _ = refl

      _ : ((f ∘⟨ C ⟩ π₁) ,p π₂) ≡ (Bif-homL ×Bif f d)
      _ = refl

      _ : (π₁ ,p (g ∘⟨ C ⟩ π₂)) ≡ (Bif-homR ×Bif c g)
      _ = refl

    ×β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
    ×β₁ {f = f}{g = g} = cong fst (β ues)

    ×β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
    ×β₂ {f = f}{g = g} = cong snd (β ues)

    ×η : f ≡ ((π₁ ∘⟨ C ⟩ f) ,p (π₂ ∘⟨ C ⟩ f))
    ×η {f = f} = η ues

    ×η' : C .id {a × b} ≡ (π₁ ,p π₂)
    ×η' = weak-η ues

    ,p-natural : ( f ,p g ) ∘⟨ C ⟩ h ≡ ((f ∘⟨ C ⟩ h) ,p (g ∘⟨ C ⟩ h))
    ,p-natural {f = f}{g = g}{h = h} = intro-natural ues

    -- this has the benefit of always applying
    ×-extensionality : π₁ ∘⟨ C ⟩ f ≡
                       π₁ ∘⟨ C ⟩ g → π₂ ∘⟨ C ⟩ f ≡ π₂ ∘⟨ C ⟩ g → f ≡ g
    ×-extensionality p1 p2 = extensionality ues (ΣPathP (p1 , p2))

    module _ (Γ : C .ob) where
      module PWN = ProdsWithNotation (bp Γ)
      ×pF-with-agrees : ×pF ⟪ C .id , f ⟫ ≡ PWN.×pF ⟪ f ⟫
      ×pF-with-agrees = cong₂ _,p_ (C .⋆IdR _) refl
