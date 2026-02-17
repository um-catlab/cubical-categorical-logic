{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom.Quantifiers where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.FunctorComprehension.Base

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
--   (∀PshLarge)
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom

open Category
open Categoryᴰ
open Functor
open Iso
open NatIso
open NatTrans
open PshHomStrict
open PshIsoStrict

private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

-- Helper: precomposing with a PshIsoStrict gives an Iso on hom sets
module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR}
  (isoᴾᴼ : PshIsoStrict P Q)
  where
  private
    f = isoᴾᴼ .trans
    g = invPshIsoStrict isoᴾᴼ .trans
    sec' : ∀ c q → f .N-ob c (g .N-ob c q) ≡ q
    sec' c = isoᴾᴼ .nIso c .snd .fst
    ret' : ∀ c p → g .N-ob c (f .N-ob c p) ≡ p
    ret' c = isoᴾᴼ .nIso c .snd .snd

  precompPshIsoStrict : Iso (PshHomStrict Q R) (PshHomStrict P R)
  precompPshIsoStrict .fun β = f ⋆PshHomStrict β
  precompPshIsoStrict .inv γ = g ⋆PshHomStrict γ
  precompPshIsoStrict .sec γ = makePshHomStrictPath
    (funExt₂ λ c p → cong (γ .N-ob c) (ret' c p))
  precompPshIsoStrict .ret β = makePshHomStrictPath
    (funExt₂ λ c q → cong (β .N-ob c) (sec' c q))

-- Pullback squares in the strict setting
module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHomStrict P R)
  (β : PshHomStrict Q R)
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module R = PresheafNotation R

  module _ {S : Presheaf C ℓS}
    (α' : PshHomStrict S Q) (β' : PshHomStrict S P)
    where
    private
      module S = PresheafNotation S

    -- A pullback square:
    --   S --α'--> Q
    --   |         |
    --   β'        β
    --   |         |
    --   v         v
    --   P --α---> R
    isPullbackSqStrict : Type _
    isPullbackSqStrict =
      Σ[ comm ∈ (α' ⋆PshHomStrict β) ≡ (β' ⋆PshHomStrict α) ]
      (∀ Γ (q : Q.p[ Γ ]) →
        isIso {A = Σ[ s ∈ S.p[ Γ ] ] q ≡ α' .N-ob Γ s}
              {B = Σ[ p ∈ P.p[ Γ ] ] β .N-ob Γ q ≡ α .N-ob Γ p}
        λ (s , α's≡q) → (β' .N-ob Γ s) ,
          cong (β .N-ob Γ) α's≡q ∙ funExt₂⁻ (cong N-ob comm) Γ s)

    module _ ((comm , ispb) : isPullbackSqStrict)
      {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
      where
      private
        module Pᴰ = PresheafᴰNotation Pᴰ

      BeckChevalleyStrict-ptwise : ∀ Γ Γᴰ (q : Q.p[ Γ ])
        → Iso (Σ[ s ∈ S.p[ Γ ] ] Pᴰ.p[ β' .N-ob Γ s ][ Γᴰ ] × PathEq q (α' .N-ob Γ s))
              (Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × PathEq (β .N-ob Γ q) (α .N-ob Γ p))
      BeckChevalleyStrict-ptwise Γ Γᴰ q .fun (s , pᴰ , q≡α's) =
        (β' .N-ob Γ s)
        , pᴰ
        , inl (cong (β .N-ob Γ) (PathEq→Path Q.isSetPsh q≡α's)
               ∙ funExt₂⁻ (cong N-ob comm) Γ s)
      BeckChevalleyStrict-ptwise Γ Γᴰ q .inv (p , pᴰ , βq≡αp) =
        let (s , q≡α's) = ispb Γ q .fst (p , PathEq→Path R.isSetPsh βq≡αp)
            p≡β's = sym (cong fst (ispb Γ q .snd .fst (p , PathEq→Path R.isSetPsh βq≡αp)))
        in s , Pᴰ.reind p≡β's pᴰ , inl q≡α's
      BeckChevalleyStrict-ptwise Γ Γᴰ q .sec (p , pᴰ , βq≡αp) =
        let secPath = cong fst (ispb Γ q .snd .fst (p , PathEq→Path R.isSetPsh βq≡αp))
        in ΣPathP (secPath
               , ΣPathPProp (λ _ → isPropPathEq R.isSetPsh)
                 (Pᴰ.rectifyOut $ Pᴰ.reind-filler⁻ _))
      BeckChevalleyStrict-ptwise Γ Γᴰ q .ret (s , pᴰ , q≡α's) =
        let retPath = cong fst (ispb Γ q .snd .snd (s , PathEq→Path Q.isSetPsh q≡α's))
        in ΣPathP (retPath
               , ΣPathPProp (λ _ → isPropPathEq Q.isSetPsh)
                 (Pᴰ.rectifyOut $ Pᴰ.reind-filler⁻ _))

      BeckChevalleyStrict-natural :
        ∀ (Δ,Δᴰ,q : (Cᴰ / Q) .ob) (Γ,Γᴰ,q' : (Cᴰ / Q) .ob)
        (f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ])
        (x : ⟨ PushPsh α' (β' *Strict Pᴰ) .F-ob Γ,Γᴰ,q' ⟩)
        → fun (BeckChevalleyStrict-ptwise (Δ,Δᴰ,q .fst) (Δ,Δᴰ,q .snd .fst) (Δ,Δᴰ,q .snd .snd))
              (PushPsh α' (β' *Strict Pᴰ) .F-hom f x)
          ≡ (β *Strict (PushPsh α Pᴰ)) .F-hom f
              (fun (BeckChevalleyStrict-ptwise (Γ,Γᴰ,q' .fst) (Γ,Γᴰ,q' .snd .fst) (Γ,Γᴰ,q' .snd .snd)) x)
      BeckChevalleyStrict-natural (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q'≡q) (s , pᴰ , q'≡α's) =
        ΣPathP (sym (β' .N-hom _ _ _ _ _ refl) ,
          (ΣPathPProp (λ _ → isPropPathEq R.isSetPsh)
          (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _)))

      -- -- push α' (β'* Pᴰ) ≅ β* (push α Pᴰ)
      BeckChevalleyStrict : PshIsoStrict (PushPsh α' (β' *Strict Pᴰ)) (β *Strict (PushPsh α Pᴰ))
      BeckChevalleyStrict = Isos→PshIsoStrict
        (λ (Γ , Γᴰ , q) → BeckChevalleyStrict-ptwise Γ Γᴰ q)
        BeckChevalleyStrict-natural

-- Universal quantifier (dependent product) over Q
-- For PQᴰ : Presheafᴰ (P ×Psh Q) Cᴰ, we get ∀PshLargeStrict Q PQᴰ : Presheafᴰ P Cᴰ
-- Universal property: Hom(Rᴰ, ∀Q PQᴰ) ≅ Hom(wk Q Rᴰ, PQᴰ)
-- where wk Q Rᴰ = π₁* Rᴰ is weakening (pullback along π₁)

-- Weakening functor: pullback along π₁
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (P : Presheaf C ℓP) (Q : Presheaf C ℓQ)
  where

  wkPshᴰStrict : Presheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ
  wkPshᴰStrict Pᴰ = π₁ P Q *Strict Pᴰ

-- Universal quantifier with explicit definition
-- For PQᴰ : Presheafᴰ (P ×Psh Q) Cᴰ, we define ∀Q PQᴰ : Presheafᴰ P Cᴰ
-- Elements at (Γ, Γᴰ, p) are "dependent functions" that for any
-- (Δ, Δᴰ, δ : C[Δ,Γ], q : Q[Δ]) give an element of PQᴰ[δ⋆p, q][Δᴰ]
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Q : Presheaf C ℓQ)
  (PQᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ)
  where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module PQ = PresheafNotation (P ×Psh Q)
    module PQᴰ = PresheafᴰNotation PQᴰ
    module Cᴰ = Fibers Cᴰ

  -- The type of "section" functions for the universal quantifier
  -- A section at (Γ, Γᴰ, p) assigns to each (Δ, Δᴰ, δ, q) an element of PQᴰ
  ∀Psh-SecTy : (Γ : C.ob) (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) → Type _
  ∀Psh-SecTy Γ Γᴰ p =
    (Δ : C.ob) (Δᴰ : Cᴰ.ob[ Δ ]) (δ : C [ Δ , Γ ]) (q : Q.p[ Δ ])
    → PQᴰ.p[ δ P.⋆ p , q ][ Δᴰ ]

  -- Naturality condition for sections
  -- When we have ε : C[Θ, Δ] and εᴰ : Cᴰ[ε][Θᴰ, Δᴰ], we need
  -- εᴰ ⋆ᴰ sec(Δ, δ, q) ≡ sec(Θ, ε⋆δ, ε⋆q) (up to reindexing)
  ∀Psh-NatTy : (Γ : C.ob) (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → ∀Psh-SecTy Γ Γᴰ p → Type _
  ∀Psh-NatTy Γ Γᴰ p sec =
    (Δ : C.ob) (Δᴰ : Cᴰ.ob[ Δ ]) (δ : C [ Δ , Γ ]) (q : Q.p[ Δ ])
    (Θ : C.ob) (Θᴰ : Cᴰ.ob[ Θ ]) (ε : C [ Θ , Δ ]) (εᴰ : Cᴰ.Hom[ ε ][ Θᴰ , Δᴰ ])
    → εᴰ PQᴰ.⋆ᴰ sec Δ Δᴰ δ q
      ≡ PQᴰ.reind (ΣPathP (P.⋆Assoc _ _ _ , refl))
          (sec Θ Θᴰ (ε C.⋆ δ) (ε Q.⋆ q))

  isProp-∀Psh-NatTy : ∀ Γ Γᴰ p sec → isProp (∀Psh-NatTy Γ Γᴰ p sec)
  isProp-∀Psh-NatTy _ _ _ _ = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
    isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → PQᴰ.isSetPshᴰ _ _

  -- The universal quantifier ∀Q PQᴰ is a presheaf over P
  ∀PshLargeStrict : Presheafᴰ P Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') (ℓ-max ℓQ ℓPᴰ))
  ∀PshLargeStrict .F-ob (Γ , Γᴰ , p) .fst =
    Σ[ sec ∈ ∀Psh-SecTy Γ Γᴰ p ] ∀Psh-NatTy Γ Γᴰ p sec
  ∀PshLargeStrict .F-ob (Γ , Γᴰ , p) .snd =
    isSetΣ (isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → PQᴰ.isSetPshᴰ)
      (λ _ → isProp→isSet (isProp-∀Psh-NatTy _ _ _ _))
  -- F-hom: given a morphism (γ, γᴰ, γ⋆p'≡p) : (Θ, Θᴰ, p) → (Γ, Γᴰ, p') in Cᴰ/P
  -- and (sec, nat) : ∀PshLargeStrict.F-ob(Γ, Γᴰ, p')
  -- we need to produce an element of ∀PshLargeStrict.F-ob(Θ, Θᴰ, p)
  ∀PshLargeStrict .F-hom {Θ , Θᴰ , p} {Γ , Γᴰ , p'} =
    Hom/-elim λ γ γᴰ γ⋆p'≡p (sec , nat) →
      {!!}
  ∀PshLargeStrict .F-id = funExt λ (sec , nat) →
    {!!}
    -- ΣPathPProp (isProp-∀Psh-NatTy _ _ _ _)
    --   (funExt λ Δ → funExt λ Δᴰ → funExt λ δ → funExt λ q →
    --     PQᴰ.rectifyOut $
    --       PQᴰ.reind-filler⁻ _
    --       ∙ cong (sec Δ Δᴰ _) (C.⋆IdR _))
  ∀PshLargeStrict .F-seq f g = funExt λ (sec , nat) →
    {!!}
    -- ΣPathPProp (isProp-∀Psh-NatTy _ _ _ _)
    --   (funExt λ Δ → funExt λ Δᴰ → funExt λ δ → funExt λ q →
    --     PQᴰ.rectify $ PQᴰ.≡out $
    --       PQᴰ.reind-filler⁻ _
    --       ∙ PQᴰ.⋆ᴰ-reind _
    --       ∙ cong (sec Δ Δᴰ _) (sym $ C.⋆Assoc _ _ _))

  private
    module ∀Psh = PresheafᴰNotation ∀PshLargeStrict
