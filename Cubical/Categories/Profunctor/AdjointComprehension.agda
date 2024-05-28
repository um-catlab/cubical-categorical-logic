{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.AdjointComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties hiding (L)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.KanExtension
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Profunctor.FunctorComprehension

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Functor
open NatIso
open UniversalElement
open NatTrans
open NaturalBijection

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (L : Functor C D)
    where

  -- D[ L - , = ]
  LProf : Profunctor D C ℓD'
  LProf = CurryBifunctor (Sym ((HomBif D) ∘Fl (L ^opF)))

  module _ (ues : UniversalElements LProf) where
    R : Functor D C
    R = FunctorComprehension {P = LProf} ues

    the-prof-iso = ProfIso {P = LProf} ues
    the-prof-iso-inv = symNatIso (ProfIso {P = LProf} ues)

    open _⊣_
    open NatElt
    -- TODO create a universe polymorphic definition of adjoint
    -- then whisker with a lift natiso
    L⊣R : L ⊣ R
    L⊣R .adjIso {c}{d} .Iso.fun x =
      lower (the-prof-iso-inv .trans .N-ob d .N-ob c (lift x))
    L⊣R .adjIso {c}{d} .Iso.inv x =
      lower (the-prof-iso .trans .N-ob d .N-ob c (lift x))
    L⊣R .adjIso {c}{d} .Iso.rightInv b =
      cong (λ a → lower (a .N-ob c (lift b))) (the-prof-iso .nIso d .isIsoC.ret)
    L⊣R .adjIso {c}{d} .Iso.leftInv a =
      cong (λ z → lower (z .N-ob c (lift a))) (the-prof-iso .nIso d .isIsoC.sec)
    L⊣R .adjNatInD {c}{d}{d'} f k =
      cong (λ a → lower ((a .N-ob c) (lift f))) (the-prof-iso-inv .trans .N-hom k)
    L⊣R .adjNatInC {c'}{c}{d} g h =
      cong (λ a → lower (a (lift g))) (the-prof-iso .trans .N-ob d .N-hom h)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor C D)
  ℓS
  where

  F* = precomposeF (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)) (F ^opF)

  open Ran ℓS F

  -- Define the right Kan-extension of preseheaves along F
  -- via FunctorComprehension
  --
  -- This still requires the Presheaf.KanExtension definitions of
  -- RanOb, RanHom, η, ε, and Δ₂
  Ran' :
    Functor
      (FUNCTOR (C ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
      (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
  Ran' = R F* the-ues
    where
    the-ues : UniversalElements (LProf F*)
    the-ues P .vertex = RanOb P
    the-ues P .element = ε .N-ob P
    the-ues P .universal A .equiv-proof y .fst .fst =
      seqTrans (η .N-ob A) (RanHom y)
    the-ues P .universal A .equiv-proof y .fst .snd =
      makeNatTransPath (funExt (λ c → funExt (λ x →
        cong (λ a → y .N-ob c a) (cong (λ a → a x) (A .F-id)))))
    the-ues P .universal A .equiv-proof y .snd z =
      Σ≡Prop
        (λ x → isSetHom
          (FUNCTOR (C ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
          (action (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
          (LProf F* ⟅ P ⟆) x (the-ues P .element)) y)
        (cong (λ a → seqTrans (η .N-ob A) (RanHom a)) (sym (z .snd) ) ∙
        cong (λ a → seqTrans (η .N-ob A) a) (makeNatTransPath (funExt (mapL∘ _ _))) ∙
        sym ((FUNCTOR (D ^op) (SET _)) .⋆Assoc _ _ _) ∙
        cong (λ a → seqTrans a (RanHom (ε .N-ob P))) (sym (η .N-hom (z .fst))) ∙
        (FUNCTOR (D ^op) (SET _)) .⋆Assoc _ _ _ ∙
        cong (λ a → seqTrans (z .fst) a) (Δ₂ P) ∙
        (FUNCTOR (D ^op) (SET _)) .⋆IdR (z .fst))

  _ : ∀ P → Ran ⟅ P ⟆ ≡ Ran' ⟅ P ⟆
  _ = λ P → refl

  -- The action on morphisms is not definitionally equal but could be
  -- proved path-equal with a similar path to above
  -- i.e. reassociate the seqTrans and use (Δ₂ P)
  -- _ : ∀ {P}{Q}(f : FUNCTOR (C ^op) (SET _) [ P , Q ]) → Ran ⟪ f ⟫ ≡ Ran' ⟪ f ⟫
  -- _ = λ f → {!!}
