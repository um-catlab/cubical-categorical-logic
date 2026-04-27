-- A much simpler approach than the one using a presented
-- category. All we need are extra identities thrown in, not the full
-- free category construction.

module Cubical.Categories.Instances.BinProduct.Redundant.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
import Cubical.Categories.Instances.BinProduct as BP
open import Cubical.Categories.Instances.ExtraId
open import Cubical.Categories.Bifunctor as Bif hiding (Sym)

private
  variable
    ℓb ℓb' ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓ ℓ' : Level

open Category
open Functor

_×C_ : (C : Category ℓc ℓc') (D : Category ℓd ℓd') → Category (ℓ-max ℓc ℓd) (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd'))
C ×C D = ExtraId C BP.×C ExtraId D

module _  {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  ηBif : Bifunctor C D (C ×C D)
  ηBif = ParFunctorToBifunctor Id ∘Flr ((σ C) , (σ D))

  module _ {E : Category ℓ ℓ'} (F : Bifunctor C D E) where
    module F = Bifunctor F
    rec-F-hom : ∀ {c d} c' (f : ExtraId C [ c , c' ]) d' (g : ExtraId D [ d , d' ])
      → E [ F.Bif-ob c d , F.Bif-ob c' d' ]
    rec-F-hom = elim C (elim D
      -- f ≡ id, g ≡ id
      (E .id)
      -- f ≡ id
      (F.Bif-homR _)
      (sym F.Bif-R-id))
      (λ f → elim D
        (F.Bif-homL f _)
        (F.Bif-hom× f)
        (F.Bif-L×-agree f))
      (funExt₂ (elimProp D (λ f → E .isSetHom _ _)
      F.Bif-R×-agree))

    rec-F-seq : ∀ {c d}
      c' (f : ExtraId C [ c , c' ])
      c'' (f' : ExtraId C [ c' , c'' ])
      d' (g : ExtraId D [ d , d' ])
      d'' (g' : ExtraId D [ d' , d'' ])
      → rec-F-hom _ (f ⋆⟨ ExtraId C ⟩ f') _ (g ⋆⟨ ExtraId D ⟩ g' )
        ≡ rec-F-hom _ f _ g ⋆⟨ E ⟩ rec-F-hom _ f' _ g'
    rec-F-seq = elimProp2 C (λ _ _ → isPropΠ4 (λ _ _ _ _ → E .isSetHom _ _))
      (λ f f' → elimProp2 D (λ _ _ → E .isSetHom _ _)
      (λ g g' → F.Bif-×-seq f f' g g'))

    rec : Functor (C ×C D) E
    rec .F-ob = uncurry F.Bif-ob
    rec .F-hom x = rec-F-hom _ (x .fst) _ (x .snd)
    rec .F-id = refl
    rec .F-seq f g = rec-F-seq _ (f .fst) _ (g .fst) _ (f .snd) _ (g .snd)

    -- This is refl on objects and morphisms(!)
    η⋆rec : rec ∘Fb ηBif ≡ F
    η⋆rec i .Bifunctor.Bif-ob = F.Bif-ob
    η⋆rec i .Bifunctor.Bif-homL = F.Bif-homL
    η⋆rec i .Bifunctor.Bif-homR = F.Bif-homR
    η⋆rec i .Bifunctor.Bif-hom× = F.Bif-hom×
    η⋆rec i .Bifunctor.Bif-L-id = {!!}
    η⋆rec i .Bifunctor.Bif-L-seq = {!!}
    η⋆rec i .Bifunctor.Bif-R-id = {!!}
    η⋆rec i .Bifunctor.Bif-R-seq = {!!}
    η⋆rec i .Bifunctor.Bif-×-id = {!!}
    η⋆rec i .Bifunctor.Bif-×-seq = {!!}
    η⋆rec i .Bifunctor.Bif-L×-agree = {!!}
    η⋆rec i .Bifunctor.Bif-R×-agree = {!!}
    η⋆rec i .Bifunctor.Bif-LR-fuse = {!!}
    η⋆rec i .Bifunctor.Bif-RL-fuse = {!!}

  -- using elimPropBoth for emphasis that all 4 cases are refl
  recη≡Id : rec ηBif ≡ Id
  recη≡Id = Functor≡ (λ _ → refl) λ f → lem _ (f .fst) _ (f .snd) where
    lem : ∀ {c d} c' (f : ExtraId C [ c , c' ]) d' (g : ExtraId D [ d , d' ])
      → rec-F-hom ηBif _ f _ g ≡ (f , g)
    lem = elimPropBoth C (λ _ → isPropΠ2 (λ _ _ → (C ×C D) .isSetHom _ _))
      (elimPropBoth D (λ _ → (C ×C D) .isSetHom _ _) refl (λ _ → refl))
      (λ f → elimPropBoth D (λ _ → (C ×C D) .isSetHom _ _) refl (λ _ → refl))
