{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso

-- What are the fundamental constructions on uncurried displayed presheaves?
--
-- 0. Change of base/reindexing by functors and by natural transformations
-- 1. Vertical Products (Unit, ×ⱽ)
-- 2. Exponentials
-- 3. Universal Quantifiers
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf D ℓP}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ)
  where
  reindPshᴰFunctor : Presheafᴰ (reindPsh F P) Cᴰ ℓPᴰ
  reindPshᴰFunctor = reindPsh (Fᴰ /Fᴰ idPshHom) Pᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  reindPshᴰNatTrans : Presheafᴰ P Cᴰ ℓQᴰ
  reindPshᴰNatTrans = reindPsh (Idᴰ /Fⱽ α) Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  where
  LiftPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → (ℓPᴰ' : Level) → Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓPᴰ')
  LiftPshᴰ Pᴰ ℓPᴰ' = LiftF {ℓ' = ℓPᴰ'} ∘F Pᴰ

  UnitPshᴰ : Presheafᴰ P Cᴰ ℓ-zero
  UnitPshᴰ = UnitPsh
  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
    _×ⱽPsh_ : Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
    _×ⱽPsh_ = Pᴰ ×Psh Qᴰ

    _⇒ⱽPshLarge_ : Presheafᴰ P Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ) ℓQᴰ)
    _⇒ⱽPshLarge_ = Pᴰ ⇒PshLarge Qᴰ

    -- -- Does LocallyRepresentableⱽ Pᴰ allow us to construct a functor from Cᴰ / P to Cᴰ / P ? Yes.
    -- -- it maps (Γ , Γᴰ , p) to (Γ , Γᴰ ×ⱽ p *Pᴰ , p)
    -- _⇒ⱽPshSmall_ : Presheafᴰ P Cᴰ ℓQᴰ
    -- _⇒ⱽPshSmall_ = reindPsh {!!} Qᴰ
      -- on objects (Pᴰ ⇒ⱽPshSmall Qᴰ) (Γ , Γᴰ , p) = Qᴰ (Γ , Γᴰ ×ⱽ p*Pᴰ , p)


  -- UMP of ∀PshLarge is
  -- R |-ⱽ ∀PshLarge PQᴰ
  -- ≅ π₁ * R |-ⱽ PQᴰ

  -- so given (Γ , Γᴰ , p)
  -- (∀PshLarge PQᴰ) (Γ , Γᴰ , p)
  -- ≅[Yoneda] Yo(Γ,Γᴰ,p) ⊢ⱽ ∀PshLarge PQᴰ
  -- ≅ π₁* Yo(Γ,Γᴰ,p) ⊢ⱽ PQᴰ

  -- So to do this definition we need
  -- 1. [X] PshHomⱽ is a profunctor
  -- 2. π₁* : Pshⱽ P → Pshⱽ (P × Q) is a functor
  ∀PshLarge : (Q : Presheaf C ℓQ)
    → Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ
    → Presheafᴰ P Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓQ) ℓPᴰ)
  ∀PshLarge Q PQᴰ = reindPsh (precomposeF (SET (ℓ-max ℓC' (ℓ-max ℓCᴰ' ℓP))) ((Idᴰ /Fⱽ π₁ P Q) ^opF) ∘F YO) (PshHomPsh PQᴰ)

  -- -- To make a ∀PshSmall, we need the presheaf Q being quantified
  -- -- over to be LocallyRepresentable _×Q and for Cᴰ to have
  -- -- cartesian lifts of π₁ of Γ ×Q.

  -- -- if that's established then we can make a functor ×Q : Cᴰ / P → Cᴰ / P × Q
  -- -- that sends (Γ , Γᴰ , p) to (Γ ×Q , π₁* Γᴰ , p ×Q)
  --
  -- -- And then ∀PshSmall Q PQᴰ = reindPsh ×Q PQᴰ

  -- ∀PshSmall : ((Q , _×Q) : LRPresheaf C ℓQ)
  --   → isFibration Cᴰ
  --   → Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ
  --   → Presheafᴰ P Cᴰ ℓPᴰ
  -- ∀PshSmall (Q , _×Q) isFibCᴰ PQᴰ = reindPsh {!!} PQᴰ
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (F : Functor (Dᴰ / Q) (Cᴰ / P))
  where
  UnitPshᴰ-reindPsh :
    PshIsoⱽ (reindPsh F UnitPshᴰ)
            UnitPshᴰ
  UnitPshᴰ-reindPsh = pathToPshIso $ sym $
    Constant-natural (SET ℓ-zero) (Unit , isSetUnit) (F ^opF)

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor (Dᴰ / Q) (Cᴰ / P)}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
  where
  ×ⱽPsh-reindPsh :
    PshIsoⱽ (reindPsh F (Pᴰ ×ⱽPsh Qᴰ))
            (reindPsh F Pᴰ ×ⱽPsh reindPsh F Qᴰ)
  ×ⱽPsh-reindPsh = pathToPshIso $
    (×Sets ∘F (Pᴰ ,F Qᴰ)) ∘F (F ^opF)
      ≡⟨ (sym $ F-assoc) ⟩
    ×Sets ∘F (Pᴰ ,F Qᴰ) ∘F (F ^opF)
      ≡⟨ cong (×Sets ∘F_) ,F-natural ⟩
    ×Sets ∘F (reindPsh F Pᴰ ,F reindPsh F Qᴰ)
      ∎
