{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Double.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality as Eq
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Pullback
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
open import Cubical.Categories.Displayed.BinProduct

private
  variable
    ℓv ℓv' ℓsq ℓsq' : Level

record LocallyThinDoubleCategory ℓv ℓv' ℓsq ℓsq'
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓv') (ℓ-max ℓsq ℓsq'))) where
  field
    V  : Category ℓv ℓv'
    Sq : Categoryᴰ (V ×C V) ℓsq ℓsq'
    Refl  : GlobalSection Sq
    Trans : Functorᴰ Id (_×pbᴰ_ {C = V}{D = V}{E = V} Sq Sq) Sq
    isPropSq : hasPropHoms Sq

-- TODO: non-thin would need IdL, IdR, Assoc

-- Alternate, "curried" formulation
record DoubleCategory ℓv ℓv' ℓsq ℓsq'
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓv ℓv') (ℓ-max ℓsq ℓsq'))) where
  field
    OB  : Category ℓv ℓv'
    HOM : Categoryᴰ (OB ×C OB) ℓsq ℓsq'
    ID : GlobalSection HOM
  COMP-CTX : Category _ _
  COMP-CTX = ∫C {C = (OB ×C OB) ×C OB}
    (  EqReindex.reindex HOM ((BP.Fst OB OB ∘F BP.Fst (OB ×C OB) OB) ,F BP.Snd (OB ×C OB) OB)
       Eq.refl (λ _ _ → Eq.refl)
    ×ᴰ EqReindex.reindex HOM (BP.Snd (OB ×C OB) OB ,F (BP.Snd OB OB ∘F BP.Fst (OB ×C OB) OB))
       Eq.refl (λ _ _ → Eq.refl))
  field
    COMP : Section {D = COMP-CTX}(BP.Fst (OB ×C OB) OB ∘F TotalCat.Fst) HOM
