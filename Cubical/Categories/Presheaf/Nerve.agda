{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Nerve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open PshHomStrict

-- The nerve functor along F : Functor C D
-- Maps d ∈ D to the presheaf c ↦ D [ F c , d ]
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where

  Nerve : Functor D (PRESHEAF C ℓD')
  Nerve = reindPshFStrict F ∘F YOStrict

  -- The nerve functor always preserves binary products because
  -- presheaf limits are computed pointwise:
  -- D [ F c , A × B ] ≅ D [ F c , A ] × D [ F c , B ]
  module _ (bps : BinProducts D) where
    Nerve-pres-bp : preservesProvidedBinProducts Nerve bps
    Nerve-pres-bp A B Γ = isoToIsEquiv the-iso
      where
      open Iso
      module bp = BinProductNotation (bps (A , B))

      pairHom : PshHomStrict Γ (Nerve ⟅ A ⟆) → PshHomStrict Γ (Nerve ⟅ B ⟆)
              → PshHomStrict Γ (Nerve ⟅ bp.vert ⟆)
      pairHom α β .N-ob c x = α .N-ob c x bp.,p β .N-ob c x
      pairHom α β .N-hom c c' f x' x eq =
        sym (bp.,p≡
          (sym (α .N-hom c c' f x' x eq)
           ∙ cong (λ g → F ⟪ f ⟫ ⋆⟨ D ⟩ g) (sym bp.×β₁)
           ∙ sym (D .⋆Assoc _ _ _))
          (sym (β .N-hom c c' f x' x eq)
           ∙ cong (λ g → F ⟪ f ⟫ ⋆⟨ D ⟩ g) (sym bp.×β₂)
           ∙ sym (D .⋆Assoc _ _ _)))

      the-iso : Iso (PshHomStrict Γ (Nerve ⟅ bp.vert ⟆))
                    (PshHomStrict Γ (Nerve ⟅ A ⟆) × PshHomStrict Γ (Nerve ⟅ B ⟆))
      the-iso .fun f = f ⋆PshHomStrict Nerve ⟪ bp.π₁ ⟫ , f ⋆PshHomStrict Nerve ⟪ bp.π₂ ⟫
      the-iso .inv (α , β) = pairHom α β
      the-iso .sec (α , β) = ΣPathP
        ( makePshHomStrictPath (funExt₂ λ c x → bp.×β₁)
        , makePshHomStrictPath (funExt₂ λ c x → bp.×β₂))
      the-iso .ret f = makePshHomStrictPath (funExt₂ λ c x →
        bp.,p-extensionality bp.×β₁ bp.×β₂)

-- YOStrict preserves binary products (special case of Nerve-pres-bp
-- with the identity functor, since Nerve Id ≡ YOStrict by computation)
module _ {C : Category ℓC ℓC'} (bps : BinProducts C) where
  YOStrict-pres-bp : preservesProvidedBinProducts (YOStrict {C = C}) bps
  YOStrict-pres-bp A B Γ = isoToIsEquiv the-iso
    where
    open Iso
    module bp = BinProductNotation (bps (A , B))

    pairHom : PshHomStrict Γ (YOStrict ⟅ A ⟆) → PshHomStrict Γ (YOStrict ⟅ B ⟆)
            → PshHomStrict Γ (YOStrict ⟅ bp.vert ⟆)
    pairHom α β .N-ob c x = α .N-ob c x bp.,p β .N-ob c x
    pairHom α β .N-hom c c' f x' x eq =
      sym (bp.,p≡
        (sym (α .N-hom c c' f x' x eq)
         ∙ cong (λ g → f ⋆⟨ C ⟩ g) (sym bp.×β₁)
         ∙ sym (C .⋆Assoc _ _ _))
        (sym (β .N-hom c c' f x' x eq)
         ∙ cong (λ g → f ⋆⟨ C ⟩ g) (sym bp.×β₂)
         ∙ sym (C .⋆Assoc _ _ _)))

    the-iso : Iso (PshHomStrict Γ (YOStrict ⟅ bp.vert ⟆))
                  (PshHomStrict Γ (YOStrict ⟅ A ⟆) × PshHomStrict Γ (YOStrict ⟅ B ⟆))
    the-iso .fun f = f ⋆PshHomStrict YOStrict ⟪ bp.π₁ ⟫ , f ⋆PshHomStrict YOStrict ⟪ bp.π₂ ⟫
    the-iso .inv (α , β) = pairHom α β
    the-iso .sec (α , β) = ΣPathP
      ( makePshHomStrictPath (funExt₂ λ c x → bp.×β₁)
      , makePshHomStrictPath (funExt₂ λ c x → bp.×β₂))
    the-iso .ret f = makePshHomStrictPath (funExt₂ λ c x →
      bp.,p-extensionality bp.×β₁ bp.×β₂)

-- When D is a cartesian category, the nerve is a cartesian functor
module _ {C : Category ℓC ℓC'} {D : CartesianCategory ℓD ℓD'} (F : Functor C (D .CartesianCategory.C)) where
  private
    module D = CartesianCategory D

  CartesianNerve : CartesianFunctor D (PRESHEAF C ℓD')
  CartesianNerve = Nerve F , Nerve-pres-bp F D.bp
