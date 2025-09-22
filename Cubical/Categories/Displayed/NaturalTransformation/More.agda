module Cubical.Categories.Displayed.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalIsomorphism

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
  where
  private
    module Bᴰ = Fibers Bᴰ
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    module D = Category D

  module _
    {α : NatTrans G H}
    (αᴰ : NatTransᴰ α Gᴰ Hᴰ) where
    _∘ʳᴰ_ : NatTransᴰ (F ∘ʳ α) (Fᴰ ∘Fᴰ Gᴰ) (Fᴰ ∘Fᴰ Hᴰ)
    _∘ʳᴰ_ .N-obᴰ bᴰ = Fᴰ .F-homᴰ (αᴰ .N-obᴰ bᴰ)
    _∘ʳᴰ_ .N-homᴰ {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP (Fᴰ .F-seqᴰ _ _))
        ∙ Dᴰ.≡in (congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .N-homᴰ fᴰ))
        ∙ Dᴰ.≡in (Fᴰ .F-seqᴰ _ _)

  module _
    {α : NatIso G H}
    (αᴰ : NatIsoᴰ α Gᴰ Hᴰ) where
    -- TODO there is already a nondispalyed ∘ʳⁱ in the library
    -- under ∘ʳi
    _∘ʳᴰⁱ_ : NatIsoᴰ (F ∘ʳⁱ α) (Fᴰ ∘Fᴰ Gᴰ) (Fᴰ ∘Fᴰ Hᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.transᴰ = _∘ʳᴰ_ (αᴰ .NatIsoᴰ.transᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.invᴰ =
      F-homᴰ Fᴰ (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.invᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.secᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP $ Fᴰ .F-seqᴰ _ _)
        ∙ (Dᴰ.≡in $ congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.secᴰ))
        ∙ (Dᴰ.≡in $ Fᴰ .F-idᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.retᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP $ Fᴰ .F-seqᴰ _ _)
        ∙ (Dᴰ.≡in $ congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.retᴰ))
        ∙ (Dᴰ.≡in $ Fᴰ .F-idᴰ)

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

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F G : Functor C D}
  {α : NatIso F G}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  (αᴰ : NatIsoᴰ α Fᴰ Gᴰ)
  where
  opNatIsoᴰ : NatIsoᴰ (opNatIso α) (Gᴰ ^opFᴰ) (Fᴰ ^opFᴰ)
  opNatIsoᴰ .NatIsoᴰ.transᴰ = opNatTransᴰ (αᴰ .NatIsoᴰ.transᴰ)
  opNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ =
    isisoᴰ (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ)
           (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ)
           (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ)

  symNatIsoᴰ : NatIsoᴰ (symNatIso α) Gᴰ Fᴰ
  symNatIsoᴰ .NatIsoᴰ.transᴰ .N-obᴰ xᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ
  symNatIsoᴰ .NatIsoᴰ.transᴰ .N-homᴰ fᴰ = NatIsoᴰ.sqLLᴰ αᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ =
    αᴰ .NatIsoᴰ.transᴰ .N-obᴰ xᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ
