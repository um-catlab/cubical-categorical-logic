{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Constructions.BinProduct.Redundant.Assoc.ToLeft where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors.Redundant
open import Cubical.Categories.Instances.Functors.Redundant.Bifunctor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma

open import Cubical.Categories.Constructions.BinProduct.Redundant.Base as BP
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Constructions.Presented as Presented hiding (rec)
open import Cubical.Categories.Bifunctor.Redundant as Bif

private
  variable
    ℓc ℓc' ℓd ℓd' ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open Quiver
open Interpᴰ
open Axioms
open Bifunctor
open BifunctorParAx

private
  variable
    ℓe ℓe' ℓf ℓf' : Level

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         {E : Category ℓe ℓe'} where
  Assoc : Functor (C ×C (D ×C E)) ((C ×C D) ×C E)
  Assoc = rec C (D ×C E)
          (Bif.Sym (uncurry (rec D E (mkBifunctorParAx Assoc')))) where
    Assoc' : BifunctorParAx D E (FUNCTOR C ((C ×C D) ×C E))
    Assoc' .Bif-ob d e .F-ob c = (c , d) , e
    Assoc' .Bif-ob d e .F-hom f = ηBif _ _ ⟪ ηBif _ _ ⟪ f ⟫l ⟫l
    Assoc' .Bif-homL g e .fst .N-ob c = ηBif _ _ ⟪ ηBif _ _ ⟪ g ⟫r ⟫l
    Assoc' .Bif-homR d h .fst .N-ob c = ηBif _ _ ⟪ h ⟫r
    Assoc' .Bif-homL g e .snd .fst f = ηBif _ _ ⟪ ηBif _ _ ⟪ f , g ⟫× ⟫l
    Assoc' .Bif-homR d h .snd .fst f = ηBif _ _ ⟪ ηBif _ _ ⟪ f ⟫l , h ⟫×
    Assoc' .Bif-hom× g h .fst .N-ob c = ηBif _ _ ⟪ ηBif _ _ ⟪ g ⟫r , h ⟫×
    Assoc' .Bif-hom× g h .snd .fst f = ηBif _ _ ⟪ ηBif _ _ ⟪ f , g ⟫× , h ⟫×
    Assoc' .Bif-ob d e .F-id =
      cong₂ (ηBif (C ×C D) E .Bif-homL) (ηBif C D .Bif-L-id) refl
      ∙ ηBif (C ×C D) E .Bif-L-id
    Assoc' .Bif-ob d e .F-seq f f' =
      cong₂ (ηBif (C ×C D) E .Bif-homL) (ηBif C D .Bif-L-seq f f') refl
      ∙ ηBif (C ×C D) E .Bif-L-seq (ηBif _ _ ⟪ f ⟫l) (ηBif _ _ ⟪ f' ⟫l)
    Assoc' .Bif-homL g e .fst .N-hom f =
      sym (ηBif _ _ .Bif-L-seq _ _)
      ∙ (λ i → ηBif _ _ ⟪ Bif-RL-commute (ηBif _ _) f g (~ i) ⟫l)
      ∙ (ηBif _ _ .Bif-L-seq _ _)
    Assoc' .Bif-homL g e .snd .snd f =
      (λ i → ηBif _ _ ⟪ ηBif _ _ .Bif-RL-fuse f g (~ i) ⟫l)
      ∙ ηBif _ _ .Bif-L-seq (ηBif _ _ ⟪ g ⟫r) (ηBif _ _ ⟪ f ⟫l)
    Assoc' .Bif-homR d h .fst .N-hom f =
      sym (Bif-RL-commute (ηBif _ _) (ηBif _ _ ⟪ f ⟫l) h)
    Assoc' .Bif-homR d h .snd .snd f =
       sym (ηBif _ _ .Bif-RL-fuse ((ηBif _ _ ⟪ f ⟫l)) h)
    Assoc' .Bif-hom× g h .fst .N-hom f =
      Bif-L×-fuse ((ηBif (C ×C D) E)) (ηBif C D ⟪ f ⟫l) (ηBif C D ⟪ g ⟫r) h
      ∙ cong₂ (ηBif (C ×C D) E .Bif-hom×)
              (sym (Bif-RL-commute (ηBif C D) f g)) refl
      ∙ sym (Bif-×L-fuse (ηBif (C ×C D) E)
            (ηBif C D ⟪ g ⟫r) (ηBif C D ⟪ f ⟫l) h)
    Assoc' .Bif-hom× g h .snd .snd f =
      (λ i → ηBif _ _ ⟪ ηBif _ _ .Bif-RL-fuse f g (~ i) , h ⟫×)
      ∙ sym (Bif-×L-fuse (ηBif _ _) (ηBif _ _ ⟪ g ⟫r) (ηBif _ _ ⟪ f ⟫l) h)
    Assoc' .Bif-×-id {d}{e} = RedundNatTrans≡ (funExt λ c →
      cong₂ (ηBif _ _ .Bif-hom×) (ηBif _ _ .Bif-R-id) refl ∙ ηBif _ _ .Bif-×-id)
    Assoc' .Bif-×-seq g g' h h' = RedundNatTrans≡ (funExt (λ c →
      cong₂ (ηBif _ _ .Bif-hom×) (ηBif C D .Bif-R-seq g g') refl
      ∙ ηBif _ _ .Bif-×-seq (ηBif _ _ ⟪ g ⟫r) (ηBif _ _ ⟪ g' ⟫r) h h'))
    Assoc' .Bif-L×-agree g = RedundNatTrans≡ (funExt (λ c →
      ηBif (C ×C D) E .Bif-L×-agree (ηBif C D ⟪ g ⟫r)))
    Assoc' .Bif-R×-agree h = RedundNatTrans≡ (funExt (λ c →
      ηBif (C ×C D) E .Bif-R×-agree h
      ∙ cong₂ (ηBif (C ×C D) E .Bif-hom×) (sym (ηBif C D .Bif-R-id)) refl))
