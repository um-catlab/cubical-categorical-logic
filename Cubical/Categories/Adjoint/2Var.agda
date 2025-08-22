{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Adjoint.2Var where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base as Prod
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Constructions.BinProduct.Redundant.Assoc

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category

-- Given a Bifunctor F : C , D → E
-- a Right Adjoint valued in D would be
-- -=[F]=>- : C ^op , E → D
-- a Right Adjoint valued in C would be
-- -<=[F]=- : E , D ^op → C
--
-- satisfying
-- E [ F ⟅ c , d ⟆ , e ]
-- =~ C [ c , e <=[ F ]= d ]
-- =~ D [ d , c =[ F ]=> e ]
--
-- with universal elements of the form
-- E [ F ⟅ c , c =[ F ]=> e ⟆ , e ]
-- E [ F ⟅ e <=[ F ]= d , d ⟆ , e ]

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'}
         (F : Bifunctor C D E)
         where
  RightAdjointRProf : Profunctor ((C ^op) ×C E) D ℓE'
  RightAdjointRProf =
    CurryBifunctor (assoc-bif⁻
      (assoc-bif (HomBif E ∘Fl rec (C ^op) (D ^op) (F ^opBif))
      ∘Fr Prod.Sym))

  RightAdjointR : Type _
  RightAdjointR = UniversalElements RightAdjointRProf

  RightAdjointLProf : Profunctor (E ×C (D ^op)) C ℓE'
  RightAdjointLProf =
    CurryBifunctor (assoc-bif⁻ (Bif.Sym
      (HomBif E ∘Fl rec (D ^op) (C ^op) (Bif.Sym (F ^opBif)))))

  RightAdjointL : Type _
  RightAdjointL = UniversalElements RightAdjointLProf
