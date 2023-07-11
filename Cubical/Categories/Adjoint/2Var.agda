{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Categories.Adjoint.2Var where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Constructions.BinProduct.Redundant.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Constructions.BinProduct.Redundant.Assoc

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category

-- Given a Bifunctor F : C , D → E
-- A Right Adjoint in C would be a
-- Bifunctor
-- -<=[F]=- : E , D ^op → C
-- -=[F]=>- : C ^op , E → D
--
-- satisfying
-- E [ F ⟅ c , d ⟆ , e ]
-- =~ C [ c , d <=[ F ]= e ]
-- =~ D [ d , c =[ F ]=> e ]

2VarRightAdjointR : (C : Category ℓC ℓC')
               (D : Category ℓD ℓD')
               (E : Category ℓE ℓE')
               (F : Bifunctor C D E) → Type _
2VarRightAdjointR C D E F =
  UniversalElements ((C ^op) ×C E) D
    (assoc-bif (HomBif E ∘Fl
      (rec D C (Sym F) ^opF) ∘F
      ×-op-commute⁻ {C = D}{D = C}))

2VarRightAdjointL : (C : Category ℓC ℓC')
               (D : Category ℓD ℓD')
               (E : Category ℓE ℓE')
               (F : Bifunctor C D E) → Type _
2VarRightAdjointL C D E F =
  UniversalElements ((D ^op) ×C E) C
    (assoc-bif (HomBif E ∘Fl
      (rec C D F ^opF) ∘F
      ×-op-commute⁻ {C = C}{D = D}))
