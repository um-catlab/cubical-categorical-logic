-- Functors that are definitonally unital and associative.
-- Spiritually similar to the usage of PshHom over NatTrans
--
-- Should this be the default notion of functor?
-- It does rely on eta-equality
module Cubical.Categories.Functors.Strict.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Morphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

module _ (C : Category ℓc ℓc') (D : Category ℓd ℓd') where
  private
    module C = Category C
    module D = Category D
  record StrictFunctor : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    open Category
    field
      F-ob  : C .ob → D .ob
      F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]
      F-id  : {x : C .ob} (f : C [ x , x ])
        → C .id ≡ f
        → F-hom f ≡ D .id
      F-seq : {x y z : C .ob}
        (f : C [ x , y ]) (g : C [ y , z ]) (h : C [ x , z ])
            → f C.⋆ g ≡ h
            → F-hom h ≡ F-hom f D.⋆ F-hom g

open StrictFunctor
open Bifunctor
open BifunctorSepAx


SId : ∀ {C : Category ℓc ℓc'} → StrictFunctor C C
SId .F-ob = λ z → z
SId .F-hom = λ z → z
SId .F-id = λ f e → sym e
SId .F-seq = λ f g h e → sym e

module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} {E : Category ℓe ℓe'} where
  private
    module E = Category E
  _S∘_ : StrictFunctor D E → StrictFunctor C D → StrictFunctor C E
  (G S∘ F) .F-ob = λ z → G .F-ob (F .F-ob z)
  (G S∘ F) .F-hom = λ z → G .F-hom (F .F-hom z)
  (G S∘ F) .F-id f e = G .F-id (F .F-hom f) (sym $ F .F-id f e)
  (G S∘ F) .F-seq f g h e =
    G .F-seq (F .F-hom f) (F .F-hom g) (F .F-hom h) (sym $ F .F-seq f g h e)

module _ (C : Category ℓc ℓc') (D : Category ℓd ℓd') where
  test-lUnit : (F : StrictFunctor C D) → (SId S∘ F) ≡ F
  test-lUnit F = refl

  test-rUnit : (F : StrictFunctor C D) → (F S∘ SId) ≡ F
  test-rUnit F = refl

module _ {B : Category ℓc ℓc'} {C : Category ℓd ℓd'}
         {D : Category ℓe ℓe'} {E : Category ℓc ℓe'}
         where
  test-Assoc : (F : StrictFunctor B C) (G : StrictFunctor C D) (H : StrictFunctor D E)
             → ((H S∘ G) S∘ F) ≡ (H S∘ (G S∘ F))
  test-Assoc F G H = refl

Strict→Fun : ∀ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'}
           → StrictFunctor C D → Functor C D
Strict→Fun F .Functor.F-ob   = F .F-ob
Strict→Fun F .Functor.F-hom  = F .F-hom
Strict→Fun F .Functor.F-id   = F .F-id _ refl
Strict→Fun F .Functor.F-seq f g = F .F-seq f g _ refl

Fun→Strict : ∀ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'}
           → Functor C D → StrictFunctor C D
Fun→Strict F .F-ob = F .Functor.F-ob
Fun→Strict F .F-hom = F .Functor.F-hom
Fun→Strict F .F-id f e =
  cong (F .Functor.F-hom) (sym e) ∙ F .Functor.F-id
Fun→Strict F .F-seq f g h e =
  cong (F .Functor.F-hom) (sym e) ∙ F .Functor.F-seq f g

-- Everything below here was written by Claude to
-- port a sufficient amount of theory for
-- completing Double.Instances.Prof
_^opS : ∀ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'}
      → StrictFunctor C D → StrictFunctor (C ^op) (D ^op)
(F ^opS) .F-ob = F .F-ob
(F ^opS) .F-hom = F .F-hom
(F ^opS) .F-id f e = F .F-id f e
(F ^opS) .F-seq f g h e = F .F-seq g f h e

compLS : ∀ {ℓc ℓc' ℓc'' ℓc''' ℓd ℓd' ℓe ℓe' : Level}
       → {C  : Category ℓc  ℓc'}
         {C' : Category ℓc'' ℓc'''}
         {D  : Category ℓd  ℓd'}
         {E  : Category ℓe  ℓe'}
       → Bifunctor C' D E → StrictFunctor C C' → Bifunctor C D E
compLS {C = C}{D = D}{E = E} F G = mkBifunctorSepAx B where
  B : BifunctorSepAx C D E
  B .Bif-ob c d = F ⟅ G .F-ob c , d ⟆b
  B .Bif-homL f d = F ⟪ G .F-hom f ⟫l
  B .Bif-L-id {c}{d} = (λ i → F ⟪ G .F-id (Category.id C) refl i ⟫l) ∙ F .Bif-L-id
  B .Bif-L-seq {d = d} f f' =
    (λ i → F ⟪ G .F-seq f f' _ refl i ⟫l) ∙ F .Bif-L-seq _ _
  B .Bif-homR c g = F ⟪ g ⟫r
  B .Bif-R-id = F .Bif-R-id
  B .Bif-R-seq = F .Bif-R-seq
  B .Bif-hom× f g = F ⟪ G .F-hom f , g ⟫×
  B .Bif-LR-fuse f g = F .Bif-LR-fuse (G .F-hom f) g
  B .Bif-RL-fuse f g = F .Bif-RL-fuse (G .F-hom f) g

compRS : ∀ {ℓc ℓc' ℓd ℓd' ℓd'' ℓd''' ℓe ℓe' : Level}
       → {C  : Category ℓc  ℓc'}
         {D  : Category ℓd  ℓd'}
         {D' : Category ℓd'' ℓd'''}
         {E  : Category ℓe  ℓe'}
       → Bifunctor C D' E → StrictFunctor D D' → Bifunctor C D E
compRS {C = C}{D = D}{E = E} F H = mkBifunctorSepAx B where
  B : BifunctorSepAx C D E
  B .Bif-ob c d = F ⟅ c , H .F-ob d ⟆b
  B .Bif-homL f d = F ⟪ f ⟫l
  B .Bif-L-id = F .Bif-L-id
  B .Bif-L-seq = F .Bif-L-seq
  B .Bif-homR c g = F ⟪ H .F-hom g ⟫r
  B .Bif-R-id {c}{d} = (λ i → F ⟪ H .F-id (Category.id D) refl i ⟫r) ∙ F .Bif-R-id
  B .Bif-R-seq g g' =
    (λ i → F ⟪ H .F-seq g g' _ refl i ⟫r) ∙ F .Bif-R-seq _ _
  B .Bif-hom× f g = F ⟪ f , H .F-hom g ⟫×
  B .Bif-LR-fuse f g = F .Bif-LR-fuse f (H .F-hom g)
  B .Bif-RL-fuse f g = F .Bif-RL-fuse f (H .F-hom g)

compLRS : ∀ {ℓc ℓc' ℓc'' ℓc''' ℓd ℓd' ℓd'' ℓd''' ℓe ℓe' : Level}
        → {C  : Category ℓc  ℓc'}
          {C' : Category ℓc'' ℓc'''}
          {D  : Category ℓd  ℓd'}
          {D' : Category ℓd'' ℓd'''}
          {E  : Category ℓe  ℓe'}
        → Bifunctor C' D' E
        → StrictFunctor C C' → StrictFunctor D D'
        → Bifunctor C D E
compLRS F G H = compLS (compRS F H) G
