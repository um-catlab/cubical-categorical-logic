{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Direct.Examples.ToposOfTrees where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ ; _+_)
import Cubical.Data.Nat.Order.Recursive as NatOrd
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Instances.BinProduct using (_,F_)
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive

ω : Category ℓ-zero ℓ-zero
ω = WFOrder→Cat ℕWFOrder

ωDir : DirectStr ω ℕWFOrder
ωDir = Id

open import Cubical.Categories.Direct.StrictDownset ωDir
open import Cubical.Categories.Direct.Guarded.Presheaf ωDir
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self ω ℓ-zero
  using (selfEnrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Limits ω ℓ-zero
  using (Γ×- ; ×-Enr ; ⨂-Enr)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Product ω ℓ-zero
  using (IdEnr ; _,Enr_)
import Cubical.Categories.Direct.ContractiveCompleteness ωDir as CC
open import Cubical.Categories.Enriched.Enrichment.Limits.Power using (EnrichedPower)
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical using (EnrichedLimit)
open import Cubical.Categories.Enriched.Enrichment.Stage.Yoneda ω ℓ-zero using (ŷ)
import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Power ω ℓ-zero as Power
import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Conical as Conical
open import Cubical.Categories.Instances.FullSubcategory

open PshMon ω ℓ-zero using (𝓟)
open PshHomStrict
open Functor

Const : hSet ℓ-zero → Presheaf ω ℓ-zero
Const K .F-ob _ = K
Const K .F-hom _ x = x
Const K .F-id = refl
Const K .F-seq _ _ = refl

module Guarded (F : Functor 𝓟 𝓟) (lc : isLocallyContractive pshGuarded selfEnrichment selfEnrichment F) where
  private
    pws : ∀ z X → EnrichedPower selfEnrichment (ŷ z) X
    pws z X = Power.pshPower (ŷ z) X

    lims : ∀ (S : ℕ → Type) (D : Functor (FullSubcategory ω S ^op) 𝓟) → EnrichedLimit selfEnrichment D
    lims S D = Conical.pshLimit ω (FullSubcategory ω S ^op) ℓ-zero D

  fix : Presheaf ω ℓ-zero
  fix = CC.fix selfEnrichment F lc pws lims

  in-fix : 𝓟 [ F ⟅ fix ⟆ , fix ]
  in-fix = CC.fixIso selfEnrichment F lc pws lims .fst

  out-fix : 𝓟 [ fix , F ⟅ fix ⟆ ]
  out-fix = CC.fixIso selfEnrichment F lc pws lims .snd .isIso.inv

  unfold : ∀ {B} → 𝓟 [ B , F ⟅ B ⟆ ] → 𝓟 [ B , fix ]
  unfold c = Hylo.hylo pshGuarded {F = F} lc c in-fix

module Streams (K : hSet ℓ-zero) where
  SF : Functor 𝓟 𝓟
  SF = Γ×- (Const K) ∘F ▷

  SF-LC : isLocallyContractive pshGuarded selfEnrichment selfEnrichment SF
  SF-LC = LC-postcomp pshGuarded {F = ▷} {H = Γ×- (Const K)} ▷Psh-LC (×-Enr (Const K))

  open Guarded SF SF-LC public

ℕSet : hSet ℓ-zero
ℕSet = ℕ , isSetℕ

private
  pred≤ : ∀ n → ω [ n , suc n ]
  pred≤ n = Cubical.Data.Sum.inl (NatOrd.≤-refl n)

module StreamsOfℕ where
  open Streams ℕSet

  head : ∀ n → ⟨ fix .F-ob n ⟩ → ℕ
  head n x = out-fix .N-ob n x .fst

  tail : ∀ n → ⟨ fix .F-ob (suc n) ⟩ → ⟨ fix .F-ob n ⟩
  tail n x = out-fix .N-ob (suc n) x .snd .N-ob n (pred≤ n , NatOrd.≤-refl n)

  nth : ∀ n → ⟨ fix .F-ob n ⟩ → ℕ
  nth zero x = head zero x
  nth (suc n) x = nth n (tail n x)

  constC : ℕ → 𝓟 [ UnitPsh , SF ⟅ UnitPsh ⟆ ]
  constC k .N-ob n u = k , next UnitPsh .N-ob n u
  constC k .N-hom c c' f u' u e = ΣPathP (refl , next UnitPsh .N-hom c c' f u' u e)

  countC : 𝓟 [ Const ℕSet , SF ⟅ Const ℕSet ⟆ ]
  countC .N-ob n m = m , next (Const ℕSet) .N-ob n (suc m)
  countC .N-hom c c' f m' m e = ΣPathP (e , next (Const ℕSet) .N-hom c c' f (suc m') (suc m) (cong suc e))

  test-const : head 3 (unfold (constC 7) .N-ob 3 tt) ≡ 7
  test-const = refl

  test-const-tail : nth 4 (unfold (constC 7) .N-ob 4 tt) ≡ 7
  test-const-tail = refl

  test-count : nth 3 (unfold countC .N-ob 3 0) ≡ 3
  test-count = refl

Δ : Functor 𝓟 𝓟
Δ = PshProd'Strict ∘F (Id ,F Id)

Δ-Enr : FE.Enrichment (PshMon.𝓟Mon ω ℓ-zero) selfEnrichment selfEnrichment Δ
Δ-Enr = ⨂-Enr FE.∘Enr (IdEnr selfEnrichment ,Enr IdEnr selfEnrichment)

module Trees (K : hSet ℓ-zero) where
  TF : Functor 𝓟 𝓟
  TF = Γ×- (Const K) ∘F ▷ ∘F Δ

  TF-LC : isLocallyContractive pshGuarded selfEnrichment selfEnrichment TF
  TF-LC = LC-postcomp pshGuarded {F = ▷ ∘F Δ} {H = Γ×- (Const K)}
    (LC-precomp pshGuarded {H = Δ} {F = ▷} Δ-Enr ▷Psh-LC) (×-Enr (Const K))

  open Guarded TF TF-LC public

module TreesOfℕ where
  open Trees ℕSet

  label : ∀ n → ⟨ fix .F-ob n ⟩ → ℕ
  label n x = out-fix .N-ob n x .fst

  children : ∀ n → ⟨ fix .F-ob (suc n) ⟩ → ⟨ fix .F-ob n ⟩ × ⟨ fix .F-ob n ⟩
  children n x = out-fix .N-ob (suc n) x .snd .N-ob n (pred≤ n , NatOrd.≤-refl n)

  left right : ∀ n → ⟨ fix .F-ob (suc n) ⟩ → ⟨ fix .F-ob n ⟩
  left n x = children n x .fst
  right n x = children n x .snd

  bfsC : 𝓟 [ Const ℕSet , TF ⟅ Const ℕSet ⟆ ]
  bfsC .N-ob n m = m , next (Δ ⟅ Const ℕSet ⟆) .N-ob n (suc (m + m) , suc (suc (m + m)))
  bfsC .N-hom c c' f m' m e =
    ΣPathP (e , next (Δ ⟅ Const ℕSet ⟆) .N-hom c c' f _ _
      (cong (λ k → suc (k + k) , suc (suc (k + k))) e))

  test-root : label 2 (unfold bfsC .N-ob 2 0) ≡ 0
  test-root = refl

  test-right-left : label 0 (left 0 (right 1 (unfold bfsC .N-ob 2 0))) ≡ 5
  test-right-left = refl
