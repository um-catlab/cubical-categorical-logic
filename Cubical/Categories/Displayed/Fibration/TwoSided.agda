module Cubical.Categories.Displayed.Fibration.TwoSided where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓP' : Level

open Category
open Functorᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (P : Categoryᴰ (C ×C D) ℓP ℓP') where
  private
    module P = Categoryᴰ P
  record WeakLeftCartesianLift {c c' d}
    (p : P.ob[ c' , d ]) (f : C [ c , c' ])
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓP ℓP')))
    where
    field
      f*p : P.ob[ c , d ]
      π : P.Hom[ f , D .id ][ f*p , p ]
      wkUniversal : ∀ {c'' d''}
        {p'' : P.ob[ c'' , d'' ]}
        {g : C [ c'' , c ]}{h : D [ d'' , d ]}
        → P.Hom[ (g ⋆⟨ C ⟩ f , h) ][ p'' , p ]
        → P.Hom[ g , h ][ p'' , f*p ]


  record WeakRightOpCartesianLift {c d d'}
    (p : P.ob[ c , d' ]) (f : D [ d' , d ])
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓP ℓP')))
    where
    field
      pf* : P.ob[ c , d ]
      σ : P.Hom[ C .id , f ][ p , pf* ]
      wkUniversal : ∀ {c'' d''}
        {p'' : P.ob[ c'' , d'' ]}
        {g : C [ c , c'' ]}{h : D [ d , d'' ]}
        → P.Hom[ g , f ⋆⟨ D ⟩ h ][ p , p'' ]
        → P.Hom[ g , h ][ pf* , p'' ]

  record isTwoSidedWeakFibration
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓP ℓP'))) where
    field
      leftLifts : ∀ {c c' d} (p : P.ob[ c' , d ]) (f : C [ c , c' ])
        → WeakLeftCartesianLift p f
      rightLifts : ∀ {c d d'} (p : P.ob[ c , d' ]) (f : D [ d' , d ])
        → WeakRightOpCartesianLift p f
  record isTwoSidedWeakIsoFibration
    : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓP ℓP'))) where
    field
      leftLifts : ∀ {c c' d} (p : P.ob[ c' , d ]) (f : CatIso C c c')
        → WeakLeftCartesianLift p (f .fst)
      rightLifts : ∀ {c d d'} (p : P.ob[ c , d' ]) (f : CatIso D d' d)
        → WeakRightOpCartesianLift p (f .fst)

