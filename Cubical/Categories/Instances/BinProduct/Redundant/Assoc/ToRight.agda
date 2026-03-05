{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Instances.BinProduct.Redundant.Assoc.ToRight where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors.Redundant
open import Cubical.Categories.Instances.Functors.Redundant.Bifunctor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.BinProduct.Redundant.Base as BP
open import Cubical.Categories.Instances.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Instances.Presented as Presented
open import Cubical.Categories.Bifunctor

private
  variable
    ℓc ℓc' ℓd ℓd' ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open Axioms
open Bifunctor
open BifunctorParAx

private
  variable
    ℓe ℓe' ℓf ℓf' : Level

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         {E : Category ℓe ℓe'} where
  Assoc : Functor ((C ×C D) ×C E) (C ×C (D ×C E))
  Assoc = rec (C ×C D) E (uncurry (rec C D (mkBifunctorParAx Assoc'))) where
    Assoc' : BifunctorParAx C D (FUNCTOR E (C ×C (D ×C E)))
    Assoc' .Bif-ob c d .F-ob e = c , d , e
    Assoc' .Bif-ob c d .F-hom h = ηBif _ _ ⟪ ηBif _ _ ⟪ h ⟫r ⟫r
    Assoc' .Bif-ob c d .F-id =
      cong (ηBif C (D ×C E) .Bif-homR c) (ηBif D E .Bif-R-id)
      ∙ ηBif C (D ×C E) .Bif-R-id
    Assoc' .Bif-ob c d .F-seq h h' = cong (ηBif C (D ×C E) .Bif-homR c)
      (ηBif D E .Bif-R-seq h h')
      ∙ ηBif C (D ×C E) .Bif-R-seq (ηBif _ _ ⟪ h ⟫r) (ηBif _ _ ⟪ h' ⟫r)
    Assoc' .Bif-homL f d .fst .N-ob e = ηBif _ _ ⟪ f ⟫l
    Assoc' .Bif-homL f d .fst .N-hom h =
      Bif-RL-commute (ηBif _ _) f (ηBif _ _ ⟪ h ⟫r)
    Assoc' .Bif-homL f d .snd .fst h = ηBif _ _ ⟪ f , ηBif _ _ ⟪ h ⟫r ⟫×
    Assoc' .Bif-homL f d .snd .snd h =
      sym (ηBif _ _ .Bif-LR-fuse f (ηBif _ _ ⟪ h ⟫r))
    Assoc' .Bif-homR c g .fst .N-ob e = ηBif _ _ ⟪ ηBif _ _ ⟪ g ⟫l ⟫r
    Assoc' .Bif-homR c g .fst .N-hom h =
      sym (ηBif _ _ .Bif-R-seq _ _)
      ∙ cong (ηBif _ _ .Bif-homR c) (Bif-RL-commute (ηBif _ _) g h)
      ∙ ηBif _ _ .Bif-R-seq _ _
    Assoc' .Bif-homR c g .snd .fst h = ηBif _ _ ⟪ ηBif _ _ ⟪ g , h ⟫× ⟫r
    Assoc' .Bif-homR c g .snd .snd h =
      cong (ηBif _ _ .Bif-homR c) (sym (ηBif _ _ .Bif-LR-fuse g h))
      ∙ ηBif _ _ .Bif-R-seq _ _
    Assoc' .Bif-hom× f g .fst .N-ob e = ηBif _ _ ⟪ f , ηBif _ _ ⟪ g ⟫l ⟫×
    Assoc' .Bif-hom× f g .fst .N-hom h =
    -- η ⟪ η ⟪ h ⟫r ⟫r ⋆ η ⟪ f , η ⟪ g ⟫l ⟫×
      Bif-R×-fuse (ηBif _ _) f (ηBif _ _ ⟪ h ⟫r) (ηBif _ _ ⟪ g ⟫l)
    -- ≡ η ⟪ f , η ⟪ h ⟫r ⋆ η ⟪ g ⟫l ⟫×
      ∙ cong₂ (ηBif _ _ .Bif-hom×) refl (Bif-RL-commute (ηBif _ _) g h)
    -- ≡ η ⟪ f , η ⟪ g ⟫l ⋆ η ⟪ h ⟫r ⟫×
      ∙ sym (Bif-×R-fuse ((ηBif _ _) ) f
        ((ηBif _ _ ⟪ g ⟫l)) ((ηBif _ _ ⟪ h ⟫r)))
    -- ≡ η ⟪ f , η ⟪ g ⟫l ⟫× ⋆ η ⟪ η ⟪ h ⟫r ⟫r
    Assoc' .Bif-hom× f g .snd .fst h = ηBif _ _ ⟪ f , ηBif _ _ ⟪ g , h ⟫× ⟫×
    Assoc' .Bif-hom× f g .snd .snd h =
    -- η ⟪ f , η ⟪ g , h ⟫× ⟫×
      cong₂ (ηBif _ _ .Bif-hom×) refl (sym (ηBif _ _ .Bif-LR-fuse g h))
    -- η ⟪ f , (η ⟪ g ⟫l ⋆ η ⟪ h ⟫r) ⟫×
      ∙ sym (Bif-×R-fuse (ηBif _ _) f (ηBif _ _ ⟪ g ⟫l) (ηBif _ _ ⟪ h ⟫r))
    -- ≡ η ⟪ f , η ⟪ g ⟫l ⟫x ⋆ η ⟪ η ⟪ h ⟫r ⟫r
    Assoc' .Bif-×-id {c}{d} = RedundNatTrans≡ (funExt λ e →
      cong₂ (ηBif _ _ .Bif-hom×) refl (ηBif _ _ .Bif-L-id)
      ∙ ηBif _ _ .Bif-×-id)
    Assoc' .Bif-×-seq f f' g g' = RedundNatTrans≡ (funExt (λ e →
      cong₂ (ηBif _ _ .Bif-hom×) refl (ηBif _ _ .Bif-L-seq g g')
      ∙ ηBif _ _ .Bif-×-seq f f' (ηBif _ _ ⟪ g ⟫l) (ηBif _ _ ⟪ g' ⟫l)))
    Assoc' .Bif-L×-agree f = RedundNatTrans≡ (funExt (λ e →
      ηBif _ _ .Bif-L×-agree f
      ∙ cong₂ (ηBif _ _ .Bif-hom×) refl (sym (ηBif _ _ .Bif-L-id))))
    Assoc' .Bif-R×-agree g = RedundNatTrans≡ (funExt (λ e →
      ηBif _ _ .Bif-R×-agree (ηBif _ _ ⟪ g ⟫l)))
