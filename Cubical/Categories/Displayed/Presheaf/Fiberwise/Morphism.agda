{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Fiberwise.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties

open import Cubical.Categories.Displayed.Presheaf.Fiberwise.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ
open Iso
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{isFibCᴰ : isFibration Cᴰ}
  (α : PshHom P Q)
  (Pᶠ : Presheafᶠ P (Cᴰ , isFibCᴰ) ℓPᴰ)
  (Qᶠ : Presheafᶠ Q (Cᴰ , isFibCᴰ) ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᶠ = Presheafᶠ Pᶠ
    module Qᶠ = Presheafᶠ Qᶠ
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFibCᴰ = FibrationNotation isFibCᴰ

  record PshHomᶠ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓQ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC ℓCᴰ') where
    no-eta-equality
    constructor pshhomᶠ
    field
      N-obᶠ  : ∀ {x} (p : P.p[ x ]) → PshHom (Pᶠ.P-obᶠ p) (Qᶠ.P-obᶠ (α .N-ob x p))
      N-homᶠ : ∀ {x y xᴰ}(f : C [ y , x ])(p : P.p[ x ]) (pᴰ : Pᶠ.p[ p ][ xᴰ ])
        → restrictPshHom (f isFibCᴰ.*F) (N-obᶠ (f P.⋆ p)) .N-ob _ (f Pᶠ.* pᴰ)
            Qᶠ.∫≡
          (f Qᶠ.* N-obᶠ p .N-ob xᴰ pᴰ)

module _ {C : Category ℓC ℓC'} {x} where
  -- this is kind of tedious, is there a simpler argument?
  _[-,_]ᶠ : ∀ ((Cᴰ , isFibCᴰ) : Fibration C ℓCᴰ ℓCᴰ') (xᴰ : Cᴰ .Categoryᴰ.ob[_] x)
    → Presheafᶠ (C [-, x ]) ((Cᴰ , isFibCᴰ)) ℓCᴰ'
  (Cᴰ , isFibCᴰ) [-, xᴰ ]ᶠ = presheafᶠ
    (λ f → Cᴰ.v[ _ ] [-, f isFibCᴰ.* xᴰ ])
    -- PshHom (Cᴰ.v [-, f * xᴰ ]) (restrictPsh (g *F) Cᴰ.v [-, (g C.⋆ f) * xᴰ ])
    (λ g f → pshhom (λ yᴰ fⱽ → isFibCᴰ.introⱽ (isFibCᴰ.π Cᴰ.⋆ᴰ (fⱽ Cᴰ.⋆ⱽᴰ isFibCᴰ.π)))
      {!!})
    {!!}
    {!!}
    where
      module Cᴰ = Fibers Cᴰ
      module isFibCᴰ = FibrationNotation isFibCᴰ

  module _ ((Cᴰ , isFibCᴰ) : Fibration C ℓCᴰ ℓCᴰ') where
    private
      module Cᴰ = Fibers Cᴰ
      module isFibCᴰ = FibrationNotation isFibCᴰ
    module _ {xᴰ : Cᴰ.ob[ x ]}{P : Presheaf C ℓP} (Pᶠ : Presheafᶠ P (Cᴰ , isFibCᴰ) ℓPᴰ) where
      private
        module P = PresheafNotation P
        module Pᶠ = Presheafᶠ Pᶠ
      yoRecᶠ : {p : P.p[ x ]} 
        → Pᶠ.p[ p ][ xᴰ ]
        → PshHomᶠ (yoRec P p) ((Cᴰ , isFibCᴰ) [-, xᴰ ]ᶠ) Pᶠ
      yoRecᶠ pᴰ .PshHomᶠ.N-obᶠ f .N-ob yᴰ fⱽ = {!!}
      yoRecᶠ pᴰ .PshHomᶠ.N-obᶠ f .N-hom = {!!}
      yoRecᶠ pᴰ .PshHomᶠ.N-homᶠ = {!!}
