{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.SmallStep where
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Category
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.More
open import Cubical.Categories.Enriched.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Structure
open import Cubical.Categories.CBPV.Instances.Free
open import Cubical.Categories.CBPV.Base using (CBPVModel ; CBPVModelHom)
open import Cubical.Categories.CBPV.Instances.TransitionSystem

open CBPVModel
open Category
open Functor
open NatTrans
open EnrichedFunctor
open EnrichedCategory
open CBPVModelHom
open TSys
open TSystem
open TSystem[_,_]

module mod {ℓ : Level} where
  private
    set = SET ℓ
    𝓜 = model.𝓟Mon set
    self = model.self  set

    self[_,_] = self {ℓ} .Hom[_,_]

    E : EnrichedCategory 𝓜 _
    E = enrich TSysCat

    E[_,_] = E .Hom[_,_]

  semcmp : ob E → ob (self {ℓ})
  semcmp S .F-ob Γ =
    (Lift (set [ Γ , S .state ])) ,
    isOfHLevelLift 2 (set .isSetHom {Γ}{S .state})
  semcmp S .F-hom γ m = lift (m .lower ∘S γ)
  semcmp S .F-id = refl
  semcmp S .F-seq _ _ = refl

  stacktrans : {S T : TSystem {ℓ}} →
    NatTrans E[ S , T ] self[ semcmp S , semcmp T ]
  stacktrans {S}{T} .N-ob Γ (lift k) =
    pshhom
      (λ Δ (γ , m) → lift λ Δ∙ → k (γ Δ∙) .tmap (m .lower Δ∙))
      λ _ _ _ _  → cong lift refl
  stacktrans {S}{T} .N-hom f = funExt λ x → makePshHomPath refl

  EF : EnrichedFunctor 𝓜 E self
  EF .F₀ = semcmp
  EF .F₁ {S}{T} = stacktrans
  EF .Fid = makeNatTransPath
    (funExt λ Γ → funExt λ tt* → makePshHomPath refl)
  EF .Fseq = makeNatTransPath
    (funExt λ Γ → funExt λ tt* → makePshHomPath refl)

  sem : CBPVModel
  sem .𝓒 = set
  sem .𝓔 = E
  sem .vTy = hSet ℓ
  sem .vTm A = set [-, A ]
  sem .cTm = EF
  sem .emp =
    (Unit*  {ℓ}, isSetUnit*) ,
    λ X → (λ _ → tt*) , λ f → funExt λ _ → refl
  sem ._×c_ = λ A B → ⟨ A ⟩ × ⟨ B ⟩ , isSetΣ (A .snd) λ _ → B .snd
  sem .up×c Γ A =
    record {
      trans =
        natTrans
          (λ X f → (λ x → fst (f x)) , (λ x → snd (f x)))
          λ _ → refl ;
      nIso = λ X →
        isiso
          (λ {(f , g) x → (f x) , (g x)})
          (funExt (λ _ → refl))
          (funExt (λ _ → refl)) }
-- TODO define instance for syntax with defined substitution
