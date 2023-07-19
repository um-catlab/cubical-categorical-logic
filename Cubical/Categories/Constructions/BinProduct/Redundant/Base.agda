{-# OPTIONS --safe #-}

{- The universal category C ⊗ D with a redundant bifunctor C , D → C ⊗ D -}
{- Isomorphic (but not definitionally) to the cartesian product -}

module Cubical.Categories.Constructions.BinProduct.Redundant.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.Sigma

import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec)
open import Cubical.Categories.Constructions.Presented as Presented hiding (rec)
open import Cubical.Categories.Bifunctor.Redundant

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓ ℓ' : Level

open Category
open Functor
open Quiver
open Interpᴰ
open Axioms

module _ (C : Category ℓc ℓc') (D : Category ℓd ℓd') where
  private
    data ProdGenerator : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
      homR : ∀ (c : C .ob) {d d' : D .ob} (g : D [ d , d' ]) → ProdGenerator
      homL : ∀ {c c' : C .ob} (f : C [ c , c' ]) (d : D .ob) → ProdGenerator
      hom× : ∀ {c c' : C .ob}
               {d d' : D .ob}
               (f : C [ c , c' ]) (g : D [ d , d' ]) → ProdGenerator

    -- For axioms, we'll use the Parallel action axioms as they're the concicest
    data ProdAx : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
      ×-id : (c : C .ob)(d : D .ob) → ProdAx
      ×-seq : ∀ {c c' c''}{d d' d''}
             (f : C [ c , c' ])(f' : C [ c' , c'' ])
             (g : D [ d , d' ])(g' : D [ d' , d'' ]) → ProdAx
      L×-agree : ∀ {c c'} (f : C [ c , c' ]) (d : D .ob) → ProdAx
      R×-agree : ∀ {d d'} (c : C .ob) (g : D [ d , d' ]) → ProdAx

    Q : Quiver (ℓ-max ℓc ℓd) (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd'))
    Q .ob = C .ob × D .ob
    Q .mor = ProdGenerator
    Q .dom (homR c {d = d} g) = c , d
    Q .cod (homR c {d' = d'} g) = c , d'
    Q .dom (homL {c = c} f d) = c , d
    Q .cod (homL {c' = c'} f d) = c' , d
    Q .dom (hom× {c = c}{d = d} f g) = c , d
    Q .cod (hom× {c' = c'}{d' = d'} f g) = c' , d'

    Ax : Axioms Q (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd'))
    Ax = mkAx Q ProdAx λ
      { (×-id c d) → _ , _ ,
        η Q .I-hom (hom× (C .id {c}) (D .id {d}))
        , FreeCat Q .id
      ; (×-seq f f' g g') → _ , _ ,
        η Q .I-hom (hom× (f ⋆⟨ C ⟩ f') (g ⋆⟨ D ⟩ g'))
        , ((η Q .I-hom (hom× f g)) ⋆⟨ FreeCat Q ⟩ (η Q .I-hom (hom× f' g')))
      ; (L×-agree f d) → _ , _ ,
        η Q .I-hom (homL f d) , η Q .I-hom (hom× f (D .id {d}))
      ; (R×-agree c g) → _ , _ ,
        η Q .I-hom (homR c g) , η Q .I-hom (hom× (C .id {c}) g) }
  _×C_ : Category (ℓ-max ℓc ℓd) (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd'))
  _×C_ = PresentedCat Q Ax

  open Bifunctor

  -- This provides a much better interface than the raw presented category
  -- The universal bifunctor
  ηBif : Bifunctor C D _×C_
  ηBif = mkBifunctorParAx η' where
      open BifunctorParAx
      η' : BifunctorParAx C D _×C_
      η' .Bif-ob = _,_
      η' .Bif-homL f d = ηP Q Ax .I-hom (homL f d)
      η' .Bif-homR c g = ηP Q Ax .I-hom (homR c g)
      η' .Bif-hom× f g = ηP Q Ax .I-hom (hom× f g)
      η' .Bif-×-id = ηEq Q Ax (×-id _ _)
      η' .Bif-×-seq f f' g g' = ηEq Q Ax (×-seq f f' g g')
      η' .Bif-L×-agree f = ηEq Q Ax (L×-agree f _)
      η' .Bif-R×-agree g = ηEq Q Ax (R×-agree _ g)

  rec : {E : Category ℓ ℓ'}
        → Bifunctor C D E
        → Functor _×C_ E
  rec {E = E} G = Presented.rec Q Ax E ı λ
      { (×-id c d) → G .Bif-×-id
      ; (×-seq f f' g g') → G .Bif-×-seq f f' g g'
      ; (L×-agree f d) → G .Bif-L×-agree f
      ; (R×-agree c g) → G .Bif-R×-agree g } where
      ı : Interp Q E
      ı .I-ob (c , d) = G ⟅ c , d ⟆b
      ı .I-hom (homR c g) = G ⟪ g ⟫r
      ı .I-hom (homL f d) = G ⟪ f ⟫l
      ı .I-hom (hom× f g) = G ⟪ f , g ⟫×

  ProdToRedundant : Functor (C BP.×C D) _×C_
  ProdToRedundant .F-ob (c , d) = c , d
  ProdToRedundant .F-hom (f , g) = ηBif ⟪ f , g ⟫×
  ProdToRedundant .F-id = ηBif .Bif-×-id
  ProdToRedundant .F-seq (f , g) (f' , g') = ηBif .Bif-×-seq f f' g g'

  ob-× : (c : C .ob) → Functor D _×C_
  ob-× c .F-ob d = c , d
  ob-× c .F-hom g = ηBif ⟪ g ⟫r
  ob-× c .F-id = ηBif .Bif-R-id
  ob-× c .F-seq g g' = ηBif .Bif-R-seq g g'

  ×-ob : (d : D .ob) → Functor C _×C_
  ×-ob d .F-ob c = c , d
  ×-ob d .F-hom f = ηBif ⟪ f ⟫l
  ×-ob d .F-id = ηBif .Bif-L-id
  ×-ob d .F-seq f f' = ηBif .Bif-L-seq f f'

Functor→Bifunctor : {C : Category ℓc ℓc'}
                    {D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
                    → Functor (C ×C D) E → Bifunctor C D E
Functor→Bifunctor G = G ∘Fb ηBif _ _

×-op-commute : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
             → Functor ((C ×C D) ^op) ((C ^op) ×C (D ^op))
×-op-commute {C = C}{D = D} = rec C D (mkBifunctorParAx G) ^opF where
  open Bifunctor
  open BifunctorParAx
  G : BifunctorParAx C D (((C ^op) ×C (D ^op)) ^op)
  G .Bif-ob c d = c , d
  G .Bif-homL f d = ηBif (C ^op) (D ^op) ⟪ f ⟫l
  G .Bif-homR c g = ηBif (C ^op) (D ^op) ⟪ g ⟫r
  G .Bif-hom× f g = ηBif (C ^op) (D ^op) ⟪ f , g ⟫×
  G .Bif-×-id = ηBif (C ^op) (D ^op) .Bif-×-id
  G .Bif-×-seq f f' g g' = ηBif (C ^op) (D ^op) .Bif-×-seq f' f g' g
  G .Bif-L×-agree f = ηBif (C ^op) (D ^op) .Bif-L×-agree f
  G .Bif-R×-agree g = ηBif (C ^op) (D ^op) .Bif-R×-agree g

×-op-commute⁻ : {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
             → Functor ((C ^op) ×C (D ^op)) ((C ×C D) ^op)
×-op-commute⁻ {C = C}{D = D} = rec (C ^op) (D ^op) (mkBifunctorParAx G) where
  open Bifunctor
  open BifunctorParAx
  G : BifunctorParAx (C ^op) (D ^op) ((C ×C D) ^op)
  G .Bif-ob c d = c , d
  G .Bif-homL f d = ηBif C D ⟪ f ⟫l
  G .Bif-homR c g = ηBif C D ⟪ g ⟫r
  G .Bif-hom× f g = ηBif C D ⟪ f , g ⟫×
  G .Bif-×-id = ηBif C D .Bif-×-id
  G .Bif-×-seq f f' g g' = ηBif C D .Bif-×-seq f' f g' g
  G .Bif-L×-agree f = ηBif C D .Bif-L×-agree f
  G .Bif-R×-agree g = ηBif C D .Bif-R×-agree g
