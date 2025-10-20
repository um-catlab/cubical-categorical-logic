{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus.

  Definition 9 in https://arxiv.org/abs/1904.00827

-}
module Cubical.Categories.WithFamilies.Simple.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.General

open Category

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
SCwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
SCwF ℓC ℓC' ℓT ℓT' =
  Σ[ C ∈ Category ℓC ℓC' ]
  Σ[ Ty ∈ hSet ℓT ]
  Σ[ Tm ∈ (⟨ Ty ⟩ → Presheaf C ℓT') ]
  Terminal' C ×
  -- "Simple comprehension"
  (∀ A → LocallyRepresentable (Tm A))

module ExtendContextF
  ((C , Ty , Tm , term , ext) : SCwF ℓC ℓC' ℓT ℓT') where
  -- Using the discrete category over the groupoid truncation
  -- of types allows us to describe context extension functorially
  --
  -- Because presheaves form a groupoid, we can define
  -- terms as a functor from TY to presheaves.
  -- Then we can state the context extension operation
  -- as a profunctor that has all universal elements,
  -- thereby defining a functor on contexts that extends
  -- with respect to a fixed type

  -- TODO make ty a set
  TY : Category ℓT ℓT
  TY = DiscreteCategory (⟨ Ty ⟩ , (isSet→isGroupoid (Ty .snd)))

  TM : Functor TY (PresheafCategory C ℓT')
  TM = DiscFunc $ Tm

  open Bifunctor
  ExtendContextBif : Bifunctor C TY (PresheafCategory C (ℓ-max ℓC' ℓT'))
  ExtendContextBif  =
    -- At least some of these annotations are needed for performance
    compLR'
      {C' = PresheafCategory C ℓC'}
      {D' = PresheafCategory C ℓT'}
      {E = PresheafCategory C (ℓ-max ℓC' ℓT')}
      {C = C} {D = TY}
    PshProd (YO , TM)

  module _ (A : ⟨ Ty ⟩) where

    ExtendContextProf : Profunctor C C (ℓ-max ℓC' ℓT')
    ExtendContextProf = appR ExtendContextBif A

    open Functor
    open UniversalElement
    private
      module ext Γ = UniversalElementNotation (ext A Γ)
      module C = Category C

    ExtendContext : Functor C C
    ExtendContext = FunctorComprehension ExtendContextProf (ext A)

  _,,_ : C .ob → ⟨ Ty ⟩ → C .ob
  Γ ,, A = ExtendContext A ⟅ Γ ⟆

module ContinuationPresheaf
  ((C , Ty , Tm , term , ext) : SCwF ℓC ℓC' ℓT ℓT') where
  open ExtendContextF (C , Ty , Tm , term , ext)
  module _ (A B : ⟨ Ty ⟩) where
    open Functor

    opaque
      Cont : Presheaf C ℓT'
      Cont = Tm B ∘F ((ExtendContext A) ^opF)
