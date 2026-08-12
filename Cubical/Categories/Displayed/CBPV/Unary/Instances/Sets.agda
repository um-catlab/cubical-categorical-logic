-- Sets and set-indexed families as a unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Sets where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets as EqSET
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.CBPV.Unary.Base

open Category
open Functor
open Functorᴰ

private
  variable
    ℓ ℓ' : Level

SetCBPV : ∀ ℓ → CBPVCat (ℓ-suc ℓ) ℓ
SetCBPV ℓ = weaken KIND (SET ℓ)

SetCBPVᴰ : ∀ ℓ → CBPVCatᴰ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
SetCBPVᴰ ℓ = reindex (SETᴰ ℓ ℓ) (weakenΠ KIND (SET ℓ))

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  points : C.ob[ 𝓥 ] → Functorⱽ C (SetCBPV ℓ')
  points A .F-obᴰ X = C.Hom[ _ ][ A , X ] , C.isSetHomᴰ
  points A .F-homᴰ f g = g C.⋆ᴰ f
  points A .F-idᴰ i g = C.⋆IdRᴰ g i
  points A .F-seqᴰ f g i h = C.⋆Assocᴰ h f g (~ i)

private
  SetCBPVΠ^op : ∀ ℓ → Functor (∫C (SetCBPV ℓ ^opᴰ)) (SET ℓ ^op)
  SetCBPVΠ^op ℓ .F-ob = snd
  SetCBPVΠ^op ℓ .F-hom = snd
  SetCBPVΠ^op ℓ .F-id = refl
  SetCBPVΠ^op ℓ .F-seq _ _ = refl

  SET-fib : ∀ ℓ → isFibration (SETᴰ ℓ ℓ)
  SET-fib ℓ =
    EqFibration→Fibration EqSET.SetAssoc (SETᴰ ℓ ℓ) EqSET.SetᴰFibration

  SET-opfib : ∀ ℓ → isFibration ((SETᴰ ℓ ℓ) ^opᴰ)
  SET-opfib ℓ =
    EqFibration→Fibration EqSET.SetAssoc^op ((SETᴰ ℓ ℓ) ^opᴰ)
      EqSET.SetᴰFibration^op

SetCBPV-Uⱽ : ∀ ℓ → hasUⱽ (SetCBPVᴰ ℓ)
SetCBPV-Uⱽ ℓ f Bᴰ =
  reindexCartesianLift (SETᴰ ℓ ℓ) (weakenΠ KIND (SET ℓ)) (_ , f) Bᴰ
    (SET-fib ℓ Bᴰ _ f)

SetCBPV-Fⱽ : ∀ ℓ → hasFⱽ (SetCBPVᴰ ℓ)
SetCBPV-Fⱽ ℓ {A = A} {B = B} f Aᴰ =
  f*Aᴰ .fst ,
  pshiso
    (pshhom
      (λ x → f*Aᴰ .snd .PshIso.trans .PshHom.N-ob x)
      (λ c c' g p → f*Aᴰ .snd .PshIso.trans .PshHom.N-hom c c' g p))
    (f*Aᴰ .snd .PshIso.nIso)
  where
  f*Aᴰ : CartesianLift
    (reindex ((SETᴰ ℓ ℓ) ^opᴰ) (SetCBPVΠ^op ℓ))
    {x = 𝓒 , B} {y = 𝓥 , A} (_ , f) Aᴰ
  f*Aᴰ =
    reindexCartesianLift ((SETᴰ ℓ ℓ) ^opᴰ)
      (SetCBPVΠ^op ℓ) (_ , f) Aᴰ
      (SET-opfib ℓ Aᴰ _ f)

SetCBPVⱽ : ∀ ℓ → MultCBPVCatⱽ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
SetCBPVⱽ ℓ .fst = SetCBPVᴰ ℓ
SetCBPVⱽ ℓ .snd .fst = SetCBPV-Uⱽ ℓ
SetCBPVⱽ ℓ .snd .snd = SetCBPV-Fⱽ ℓ
