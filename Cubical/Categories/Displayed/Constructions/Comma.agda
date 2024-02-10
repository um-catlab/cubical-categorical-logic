{-

  The comma category of two functors viewed as a displayed category
  over one or both of the projections.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Comma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Constructions.BinProduct as BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More as Displayed
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Constructions.Graph

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' : Level

open Category
open Categoryᴰ
open Preorderᴰ
open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         (F : Functor C E) (G : Functor D E) where

  Commaᴰ : Preorderᴰ (C ×C D) ℓE' ℓE'
  Commaᴰ = Graph {C = C} (HomBif E ∘Fl (F ^opF) ∘Fr G)

  -- Universal Property: a functor into the comma category is
  -- equivalent to a natural transformation
  Comma : Category _ _
  Comma = ∫C (Preorderᴰ→Catᴰ Commaᴰ)

  π1 : Functor Comma C
  π1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = Preorderᴰ→Catᴰ Commaᴰ}

  π2 : Functor Comma D
  π2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = Preorderᴰ→Catᴰ Commaᴰ}

  π⇒ : NatTrans (F ∘F π1) (G ∘F π2)
  π⇒ .N-ob  = snd
  π⇒ .N-hom = snd

  IsoCommaᴰ' : Preorderᴰ Comma ℓE' ℓ-zero
  IsoCommaᴰ' .ob[_] ((c , d) , f)= isIso E f
  IsoCommaᴰ' .Hom[_][_,_] _ _ _ = Unit
  IsoCommaᴰ' .idᴰ = tt
  IsoCommaᴰ' ._⋆ᴰ_ _ _ = tt
  IsoCommaᴰ' .isPropHomᴰ = isPropUnit

  IsoCommaᴰ : Categoryᴰ (C ×C D) (ℓ-max ℓE' ℓE') ℓE'
  IsoCommaᴰ =
    ∫Cᴰ (Preorderᴰ→Catᴰ Commaᴰ)
        (Preorderᴰ→Catᴰ IsoCommaᴰ')

  IsoComma : Category _ _
  IsoComma = ∫C IsoCommaᴰ

  πⁱ1 : Functor IsoComma C
  πⁱ1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  πⁱ2 : Functor IsoComma D
  πⁱ2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  π≅ : NatIso (F ∘F πⁱ1) (G ∘F πⁱ2)
  π≅ .NatIso.trans .N-ob (_ , f , _) = f
  π≅ .NatIso.trans .N-hom (_ , sq , _) = sq
  π≅ .NatIso.nIso (_ , _ , isIso) = isIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         {F : Functor C E} {G : Functor D E}
         {B : Category ℓB ℓB'}
         (H : Functor B C)
         (K : Functor B D)
         (α : NatTrans (F ∘F H) (G ∘F K))
         where
  mkCommaFunctor : Functor B (Comma F G)
  mkCommaFunctor .F-ob b = (H ⟅ b ⟆ , K ⟅ b ⟆) , α ⟦ b ⟧
  mkCommaFunctor .F-hom f = ((H ⟪ f ⟫) , (K ⟪ f ⟫)) , (α .N-hom f)
  mkCommaFunctor .F-id = Σ≡Prop (λ _ → E .isSetHom _ _) (≡-× (H .F-id) (K .F-id))
  mkCommaFunctor .F-seq f g = Σ≡Prop (λ _ → E .isSetHom _ _) (≡-× (H .F-seq f g) (K .F-seq f g))
