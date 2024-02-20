{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.DisplayOverProjections where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Base.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

-- Given a displayed category over a product of two categories,
-- we can project out the two categories and
-- then display over them.
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
  where
  open Category

  private
    module Cᴰ = Categoryᴰ Cᴰ

  -- s for "simple" because D is not dependent on C
  -- r for "right" because D is on the right of the product
  ∫Cᴰsr : Categoryᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫Cᴰsr .ob[_] c = Σ[ d ∈ D .ob ] Cᴰ.ob[ c , d ]
  ∫Cᴰsr .Hom[_][_,_] f (d , cᴰ) (d' , cᴰ') =
    Σ[ g ∈ D [ d , d' ] ] Cᴰ.Hom[ f , g ][ cᴰ , cᴰ' ]
  ∫Cᴰsr .idᴰ = (D .id) , Cᴰ.idᴰ
  ∫Cᴰsr ._⋆ᴰ_ (f , fᴰ) (g , gᴰ) = (f ⋆⟨ D ⟩ g) , (fᴰ Cᴰ.⋆ᴰ gᴰ)
  ∫Cᴰsr .⋆IdLᴰ (f , fᴰ) = ΣPathP (_ , Cᴰ.⋆IdLᴰ _)
  ∫Cᴰsr .⋆IdRᴰ _ = ΣPathP (_ , Cᴰ.⋆IdRᴰ _)
  ∫Cᴰsr .⋆Assocᴰ _ _ _ = ΣPathP (_ , Cᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰsr .isSetHomᴰ = isSetΣ (D .isSetHom) (λ _ → Cᴰ .isSetHomᴰ)

  Fstᴰsr : Functorᴰ Id ∫Cᴰsr (weaken C D)
  Fstᴰsr .Functorᴰ.F-obᴰ = fst
  Fstᴰsr .Functorᴰ.F-homᴰ = fst
  Fstᴰsr .Functorᴰ.F-idᴰ = refl
  Fstᴰsr .Functorᴰ.F-seqᴰ = λ fᴰ gᴰ → refl

  -- s for "simple" because C is not dependent on D
  -- l for "left" because C is on the left of the product
  ∫Cᴰsl : Categoryᴰ D (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫Cᴰsl .ob[_] d = Σ[ c ∈ C .ob ] Cᴰ.ob[ c , d ]
  ∫Cᴰsl .Hom[_][_,_] g (c , cᴰ) (c' , cᴰ') =
    Σ[ f ∈ C [ c , c' ] ] Cᴰ.Hom[ f , g ][ cᴰ , cᴰ' ]
  ∫Cᴰsl .idᴰ = (C .id) , Cᴰ.idᴰ
  ∫Cᴰsl ._⋆ᴰ_ (f , fᴰ) (g , gᴰ) = (f ⋆⟨ C ⟩ g) , (fᴰ Cᴰ.⋆ᴰ gᴰ)
  ∫Cᴰsl .⋆IdLᴰ (f , fᴰ) = ΣPathP (_ , Cᴰ.⋆IdLᴰ _)
  ∫Cᴰsl .⋆IdRᴰ _ = ΣPathP (_ , Cᴰ.⋆IdRᴰ _)
  ∫Cᴰsl .⋆Assocᴰ _ _ _ = ΣPathP (_ , Cᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰsl .isSetHomᴰ = isSetΣ (C .isSetHom) (λ _ → Cᴰ .isSetHomᴰ)

  Fstᴰsl : Functorᴰ Id ∫Cᴰsl (weaken D C)
  Fstᴰsl .Functorᴰ.F-obᴰ = fst
  Fstᴰsl .Functorᴰ.F-homᴰ = fst
  Fstᴰsl .Functorᴰ.F-idᴰ = refl
  Fstᴰsl .Functorᴰ.F-seqᴰ = λ _ _ → refl

  module _
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
    (Fᴰ : Functorᴰ F Eᴰ (weaken C D))
    (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ)
    where
    -- Can build a functor into ∫Cᴰsr with the above data provided
    -- as arguments to the module
    -- One might hope to build a functor into ∫Cᴰsl as well, but
    -- there is some extra bookkeeping to be had when doing so because
    -- of having to displayed a functor over a composition involving the
    -- swap functor C ×C D → D ×C C
    -- I'd recommend just using the swap functor up front and beginning
    -- with a category over D ×C C instead of C ×C D and reinstantiating
    -- this module with that in place of ∫Cᴰ

    open Functorᴰ

    mk∫ᴰsrFunctorᴰ : Functorᴰ F Eᴰ ∫Cᴰsr
    mk∫ᴰsrFunctorᴰ .F-obᴰ xᴰ = (Fᴰ .F-obᴰ xᴰ) , (Gᴰ .F-obᴰ _ )
    mk∫ᴰsrFunctorᴰ .F-homᴰ fᴰ = Fᴰ .F-homᴰ fᴰ , Gᴰ .F-homᴰ _
    mk∫ᴰsrFunctorᴰ .F-idᴰ = ΣPathP ((Fᴰ .F-idᴰ) , (Gᴰ .F-idᴰ))
    mk∫ᴰsrFunctorᴰ .F-seqᴰ fᴰ gᴰ =
      ΣPathP ((Fᴰ .F-seqᴰ fᴰ gᴰ) , (Gᴰ .F-seqᴰ _ _))

  Assocᴰsr : Functorᴰ (FstBP C D) Cᴰ ∫Cᴰsr
  Assocᴰsr = mk∫ᴰsrFunctorᴰ _ Π2 Π3 where
    open Functorᴰ
    Π2 : Functorᴰ (FstBP C D) Cᴰ (weaken C D)
    Π2 .F-obᴰ {x}        _ = x .snd
    Π2 .F-homᴰ {_}{_}{f} _ = f .snd
    Π2 .F-idᴰ       = refl
    Π2 .F-seqᴰ _ _  = refl

    Π3 : Functorᴰ (∫F Π2) (Unitᴰ (∫C Cᴰ)) Cᴰ
    Π3 .F-obᴰ {x}        _ = x .snd
    Π3 .F-homᴰ {_}{_}{f} _ = f .snd
    Π3 .F-idᴰ      = refl
    Π3 .F-seqᴰ _ _ = refl

  Assoc-sr⁻ : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)
  Assoc-sr⁻ = mk∫Functor Assc Assc' where
    open Functor
    open Functorᴰ
    -- Might want this at the top level
    Assc : Functor (∫C ∫Cᴰsr) (C ×C D)
    Assc .F-ob (c , (d , _)) = c , d
    Assc .F-hom (f , (g , _)) = f , g
    Assc .F-id = refl
    Assc .F-seq _ _ = refl

    Assc' : Functorᴰ Assc _ Cᴰ
    Assc' .F-obᴰ {x}        _ = x .snd .snd
    Assc' .F-homᴰ {_}{_}{f} _ = f .snd .snd
    Assc' .F-idᴰ = refl
    Assc' .F-seqᴰ _ _ = refl
