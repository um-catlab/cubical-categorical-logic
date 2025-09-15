module Cubical.Categories.Displayed.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functorᴰ
open NatTrans
open NatTransᴰ
module _
  {B : Category ℓB ℓB'}
  {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  {G H : Functor B C}
  {Gᴰ : Functorᴰ G Bᴰ Cᴰ}
  {Hᴰ : Functorᴰ H Bᴰ Cᴰ}
  {α : NatTrans G H}
  (αᴰ : NatTransᴰ α Gᴰ Hᴰ)
  where
  private
    module Bᴰ = Fibers Bᴰ
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    module D = Category D

  _∘ʳᴰ_ : NatTransᴰ (F ∘ʳ α) (Fᴰ ∘Fᴰ Gᴰ) (Fᴰ ∘Fᴰ Hᴰ)
  _∘ʳᴰ_ .N-obᴰ bᴰ = Fᴰ .F-homᴰ (αᴰ .N-obᴰ bᴰ)
  _∘ʳᴰ_ .N-homᴰ {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $
      Dᴰ.≡in (symP (Fᴰ .F-seqᴰ _ _))
      ∙ Dᴰ.≡in (congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .N-homᴰ fᴰ))
      ∙ Dᴰ.≡in (Fᴰ .F-seqᴰ _ _)

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F G : Functor C D}
  {α : NatTrans F G}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  (αᴰ : NatTransᴰ α Fᴰ Gᴰ)
  where
  opNatTransᴰ : NatTransᴰ (opNatTrans α) (Gᴰ ^opFᴰ) (Fᴰ ^opFᴰ)
  opNatTransᴰ .N-obᴰ = αᴰ .N-obᴰ
  opNatTransᴰ .N-homᴰ fᴰ = symP (αᴰ .N-homᴰ fᴰ)
