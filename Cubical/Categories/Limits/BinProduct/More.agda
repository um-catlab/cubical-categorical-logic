{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor.Base

private
  variable
    ℓ ℓ' : Level

open Iso
open UnivElt
open isUniversal
open BinProduct
open Category
open Functor

module _ (C : Category ℓ ℓ') where
  BinProductToRepresentable : ∀ {a b} → BinProduct C a b →
                              RightAdjointAt _ _ (Δ C) (a , b)
  BinProductToRepresentable bp .vertex = bp .binProdOb
  BinProductToRepresentable bp .element = (bp .binProdPr₁) , (bp .binProdPr₂)
  BinProductToRepresentable bp .universal .coinduction (f1 , f2) =
    bp .univProp f1 f2 .fst .fst
  BinProductToRepresentable bp .universal .commutes (f1 , f2) =
    cong₂ _,_ (up .fst .snd .fst) (up .fst .snd .snd)
    where up = bp .univProp f1 f2
  BinProductToRepresentable bp .universal .is-uniq (f1 , f2) fp commutes =
    cong fst
      (sym (bp .univProp f1 f2 .snd
        (fp , cong fst commutes , cong snd commutes)))

  module _ (bp : BinProducts C) where
    BinProductsToUnivElts : RightAdjoint C (C ×C C) (Δ C)
    BinProductsToUnivElts c = BinProductToRepresentable (bp (c .fst) (c .snd))

    ProdProf : C o-[ ℓ' ]-* (C ×C C)
    ProdProf = Functor→Profo-* C (C ×C C) (Δ C)

    BinProductF : Functor (C ×C C) C
    BinProductF = ParamUnivElt→Functor _ _ _ BinProductsToUnivElts

  private
    variable
      a b c d : C .ob
      f g h : C [ a , b ]

  module _ {a} (bp : ∀ b → BinProduct C a b) where
    -- ProdAProf [ c , b ] = C^2 [ (c , c) , (a , b) ]
    ProdAProf : C o-[ ℓ' ]-* C
    ProdAProf = _o×_ {C = C} (pAppR (HomBif C) a) (HomBif C)

    BinProductWithToRepresentable : ParamUnivElt C C ProdAProf
    BinProductWithToRepresentable b .vertex = bp b .binProdOb
    BinProductWithToRepresentable b .element .fst = bp b .binProdPr₁
    BinProductWithToRepresentable b .element .snd = bp b .binProdPr₂
    BinProductWithToRepresentable b .universal .coinduction (f1 , f2) =
      bp b .univProp f1 f2 .fst .fst
    BinProductWithToRepresentable b .universal .commutes (f1 , f2) =
      cong₂ _,_ (up .fst .snd .fst) (up .fst .snd .snd)
      where up = bp b .univProp f1 f2
    BinProductWithToRepresentable b .universal .is-uniq (f1 , f2) fp commutes =
      cong fst (sym (bp b .univProp f1 f2 .snd
        (fp , cong fst commutes , cong snd commutes)))

    BinProductWithF = ParamUnivElt→Functor _ _ _ BinProductWithToRepresentable

    _ : ∀ {b b'}(f : C [ b , b' ]) →
        BinProductWithF ⟪ f ⟫ ≡
          bp b' .univProp (bp b .binProdPr₁)
            (f ∘⟨ C ⟩ bp b .binProdPr₂) .fst .fst
    _ = λ f → refl
    module ProdsWithNotation where
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
      f ,p g = ues _ .universal .coinduction (f , g)

      ×pF = BinProductWithF
      ×p_ : C [ b , c ] → C [ a× b , a× c ]
      ×p_ = BinProductWithF .F-hom

      ×β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
      ×β₁ = cong fst (ues _ .universal .commutes _)

      ×β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
      ×β₂ = cong snd (ues _ .universal .commutes _)

      ×η : f ≡ ((π₁ ∘⟨ C ⟩ f) ,p (π₂ ∘⟨ C ⟩ f))
      ×η = η-expansion (ues _ .universal) _

      ×η' : C .id {x = a× b} ≡ (π₁ ,p π₂)
      ×η' = coinduction-elt (ues _ .universal)

      ,p-natural : ( f ,p g ) ∘⟨ C ⟩ h ≡ ((f ∘⟨ C ⟩ h) ,p (g ∘⟨ C ⟩ h))
      ,p-natural = coinduction-natural (ues _ .universal) _ _

      ×-extensionality : π₁ ∘⟨ C ⟩ f ≡
                         π₁ ∘⟨ C ⟩ g → π₂ ∘⟨ C ⟩ f ≡ π₂ ∘⟨ C ⟩ g → f ≡ g
      ×-extensionality p1 p2 =
        determined-by-elt (ues _ .universal) (cong₂ _,_ p1 p2)

  module Notation (bp : BinProducts C) where
    private
      ues : RightAdjointAt C (C ×C C) (Δ C) (a , b)
      ues = BinProductsToUnivElts bp _

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

    -- Demonstrating the definitional behavior of BinProductF
    _ : (f ∘⟨ C ⟩ π₁) ,p (g ∘⟨ C ⟩ π₂) ≡ BinProductF bp ⟪ f , g ⟫
    _ = refl

    ×β₁ : π₁ ∘⟨ C ⟩ (f ,p g) ≡ f
    ×β₁ {f = f}{g = g} = bp _ _ .univProp f g .fst .snd .fst

    ×β₂ : π₂ ∘⟨ C ⟩ (f ,p g) ≡ g
    ×β₂ {f = f}{g = g} = bp _ _ .univProp f g .fst .snd .snd

    ×η : f ≡ ((π₁ ∘⟨ C ⟩ f) ,p (π₂ ∘⟨ C ⟩ f))
    ×η {f = f} = η-expansion (ues .universal) f

    ×η' : C .id {a × b} ≡ (π₁ ,p π₂)
    ×η' = coinduction-elt (ues .universal)

    ,p-natural : ( f ,p g ) ∘⟨ C ⟩ h ≡ ((f ∘⟨ C ⟩ h) ,p (g ∘⟨ C ⟩ h))
    ,p-natural {f = f}{g = g}{h = h} =
      coinduction-natural (ues .universal) (f , g) h

    -- this has the benefit of always applying
    ×-extensionality : π₁ ∘⟨ C ⟩ f ≡
                       π₁ ∘⟨ C ⟩ g → π₂ ∘⟨ C ⟩ f ≡ π₂ ∘⟨ C ⟩ g → f ≡ g
    ×-extensionality p1 p2 =
      determined-by-elt (ues .universal) (cong₂ _,_ p1 p2)

    module _ (Γ : C .ob) where
      module PWN = ProdsWithNotation (bp Γ)
      ×pF-with-agrees : ×pF ⟪ C .id , f ⟫ ≡ PWN.×pF ⟪ f ⟫
      ×pF-with-agrees = cong₂ _,p_ (C .⋆IdR _) refl
