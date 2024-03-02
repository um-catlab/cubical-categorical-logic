{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.DisplayOverProjections where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Base.More

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

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

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
  where
  open Category

  private
    module Cᴰ = Categoryᴰ Cᴰ

  private
    -- can't use reindex bc transport hell
    Cᴰ' : Categoryᴰ (D ×C C) _ _
    ob[ Cᴰ' ] (d , c) = Cᴰ.ob[ c , d ]
    Cᴰ' .Hom[_][_,_] (g , f) cᴰ cᴰ' = Cᴰ.Hom[ f , g ][ cᴰ , cᴰ' ]
    Cᴰ' .idᴰ = Cᴰ.idᴰ
    Cᴰ' ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
    Cᴰ' .⋆IdLᴰ = Cᴰ.⋆IdLᴰ
    Cᴰ' .⋆IdRᴰ = Cᴰ.⋆IdRᴰ
    Cᴰ' .⋆Assocᴰ = Cᴰ.⋆Assocᴰ
    Cᴰ' .isSetHomᴰ = Cᴰ.isSetHomᴰ

  -- s for "simple" because C is not dependent on D
  -- l for "left" because C is on the left of the product
  ∫Cᴰsl : Categoryᴰ D (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫Cᴰsl = ∫Cᴰsr {D = C} Cᴰ'

  Fstᴰsl : Functorᴰ Id ∫Cᴰsl (weaken D C)
  Fstᴰsl = Fstᴰsr Cᴰ'

  module _
    {E : Category ℓE ℓE'}
    (F : Functor E D)
    {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
    (Fᴰ : Functorᴰ F Eᴰ (weaken D C))
    (Gᴰ : Functorᴰ (Sym {C = D}{D = C} ∘F ∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ)
    where

    mk∫ᴰslFunctorᴰ : Functorᴰ F Eᴰ ∫Cᴰsl
    mk∫ᴰslFunctorᴰ = mk∫ᴰsrFunctorᴰ Cᴰ' F Fᴰ Gᴰ' where
      module Gᴰ = Functorᴰ Gᴰ
      Gᴰ' : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ'
      Gᴰ' .Functorᴰ.F-obᴰ  _ = Gᴰ.F-obᴰ _
      Gᴰ' .Functorᴰ.F-homᴰ _ = Gᴰ.F-homᴰ _
      Gᴰ' .Functorᴰ.F-idᴰ {x}{xᴰ} = ≡[]-rectify Cᴰ Gᴰ.F-idᴰ
      Gᴰ' .Functorᴰ.F-seqᴰ _ _ = ≡[]-rectify Cᴰ (Gᴰ.F-seqᴰ _ _)
  Assoc-sl⁻ : Functor (∫C ∫Cᴰsl) (∫C Cᴰ)
  Assoc-sl⁻ = mk∫Functor Assc Assc' where
    open Functor
    open Functorᴰ
    -- Might want this at the top level
    Assc : Functor (∫C ∫Cᴰsl) (C ×C D)
    Assc .F-ob (d , (c , _)) = c , d
    Assc .F-hom (g , (f , _)) = f , g
    Assc .F-id = refl
    Assc .F-seq _ _ = refl

    Assc' : Functorᴰ Assc _ Cᴰ
    Assc' .F-obᴰ {x}        _ = x .snd .snd
    Assc' .F-homᴰ {_}{_}{f} _ = f .snd .snd
    Assc' .F-idᴰ = refl
    Assc' .F-seqᴰ _ _ = refl

module _
  {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  {Bᴰ : Categoryᴰ (B ×C D) ℓBᴰ ℓBᴰ'}
  {Cᴰ : Categoryᴰ (C ×C E) ℓCᴰ ℓCᴰ'}
  {F : Functor D E}
  {G : Functor B C}
  (FGᴰ : Functorᴰ (G ×F F) Bᴰ Cᴰ)
  where
  private
    module G = Functor G
    module FGᴰ = Functorᴰ FGᴰ
  -- ideally this would be implemented using mk∫ᴰslFunctorᴰ
  ∫ᴰslF : Functorᴰ F (∫Cᴰsl {C = B}{D = D} Bᴰ) (∫Cᴰsl {C = C}{D = E} Cᴰ)
  ∫ᴰslF .Functorᴰ.F-obᴰ {d} (b , bᴰ) = (G ⟅ b ⟆) , (FGᴰ.F-obᴰ bᴰ)
  ∫ᴰslF .Functorᴰ.F-homᴰ {g} (f , fᴰ) = (G ⟪ f ⟫) , (FGᴰ.F-homᴰ fᴰ)
  ∫ᴰslF .Functorᴰ.F-idᴰ = ΣPathP (G.F-id , (≡[]-rectify Cᴰ FGᴰ.F-idᴰ))
  ∫ᴰslF .Functorᴰ.F-seqᴰ _ _ =
    ΣPathP ((G.F-seq _ _) , (≡[]-rectify Cᴰ (FGᴰ.F-seqᴰ _ _)))
