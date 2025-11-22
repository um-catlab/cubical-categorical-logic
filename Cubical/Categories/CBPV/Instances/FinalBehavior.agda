{-# OPTIONS --lossy-unification #-}
--{-# OPTIONS --show-implicit #-}
module Cubical.Categories.CBPV.Instances.FinalBehavior where
  open import Cubical.Foundations.Prelude
  open import Cubical.Categories.Functor
  open import Cubical.Categories.Category
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Categories.CBPV.Base
  open import Cubical.Categories.CBPV.Instances.SmallStep
  open import Cubical.Categories.CBPV.Instances.Kleisli
  open import Cubical.Categories.Enriched.Presheaf
  open import Cubical.Categories.Enriched.More
  open import Cubical.Categories.Monad.ExtensionSystem
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.CBPV.Instances.TransitionSystem
  open import Cubical.CoData.Delay
  open Monad
  open EnrichedFunctor
  open CBPVModel
  open CBPVModelHom


  module _ {ℓ : Level} where
    open mod
   -- open Model {ℓ}
    open Model
    open TSys


    behave : CBPVModelHom {!   !} {! kleisli {ℓ} ? !}
    behave = {!   !}
    -- this is dumb
    {-}
    liftSem : CBPVModel {ℓ-suc ℓ} {ℓ} {ℓ} {ℓ-suc (ℓ-suc ℓ)}
    liftSem .𝓒 = sem .𝓒
    liftSem .𝓔 = liftE (sem .𝓔 ) _
    liftSem .vTy = sem .vTy
    liftSem .vTm = sem .vTm
    liftSem .cTm .F₀ (lift X) = sem .cTm .F₀ X
    liftSem .cTm .F₁ = sem .cTm .F₁
    liftSem .cTm .Fid = sem .cTm .Fid
    liftSem .cTm .Fseq = sem .cTm .Fseq
    liftSem .emp = sem .emp
    liftSem ._×c_ = sem ._×c_
    liftSem .up×c = sem .up×c

    K : CBPVModel {ℓ-suc ℓ} {ℓ} {ℓ} {ℓ-suc ℓ}
    K = kleisli DExt

    E = enrich (Kleisli (SET ℓ) DExt)

    liftK : CBPVModel {ℓ-suc ℓ} {ℓ} {ℓ} {ℓ-suc (ℓ-suc ℓ)}
    liftK .𝓒 = K .𝓒
    liftK .𝓔 = liftE (K .𝓔) _
    liftK .vTy = K .vTy
    liftK .vTm = K .vTm
    liftK .cTm .F₀ (lift X) = K .cTm .F₀ X
    liftK .cTm .F₁ = K .cTm .F₁
    liftK .cTm .Fid = K .cTm .Fid
    liftK .cTm .Fseq = K .cTm .Fseq
    liftK .emp = K .emp
    liftK ._×c_ = K ._×c_
    liftK .up×c = K .up×c

    𝓜 = (model.𝓟Mon (SET ℓ))

    dumb : EnrichedFunctor 𝓜 E (BaseChange Id (liftK .𝓔))
    dumb .F₀ X = {!   !}
    dumb .F₁ = {!   !} -- natTrans (λ x x₁ → x₁) λ _  → refl
    dumb .Fid = {!   !} --refl
    dumb .Fseq = {!   !} -- makeNatTransPath refl

    runF : Functor {!   !} {! liftK .𝓔  !}
    runF = {!   !}

    ef : EnrichedFunctor
      (model.𝓟Mon (liftSem .𝓒)) (liftSem .𝓔)
      (BaseChange Id (liftK .𝓔))
    ef = {! enrichF ? ? runF  !}
      --ecomp _ (enrichF {!   !} {!   !} {!   !}) {! dumb  !}

    behave : CBPVModelHom liftSem liftK
    behave .ctx = Id
    behave .ty A = A
    behave .tm A = natTrans (λ Γ v Γ∙ → v Γ∙) λ _ → refl
    behave .CBPVModelHom.stk = ef
      --ecomp _ (enrichF {!   !} {!   !} {!   !})
    behave .CBPVModelHom.cmp = {!   !}

-}
