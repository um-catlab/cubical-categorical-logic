{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.LocallyContractive
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr A Wo) where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor using (Functor ; _∘F_)
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras.Recursive
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.StrictHom.Self

open import Cubical.Categories.Enriched.Enrichment.Base
  renaming (Enrichment to VE)
open import Cubical.Categories.Enriched.Enrichment.Functor.Base

open import Cubical.Categories.Monoidal.Base


open DirectNotation dir using (_≺_)

module _
  {ℓC ℓC' ℓD ℓD' ℓO : Level}
  {Wo : WFOrder ℓO ℓ'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (ℰC : VE C (PshMon.𝓟Mon A ℓ))
  (ℰD : VE D (PshMon.𝓟Mon A ℓ))
  (F : Functor C D)
  where
    open import Cubical.Categories.Enriched.Enrichment.Functor.Instances.Presheaf.Next ℰC dir
    private
      module C = Category C
      module D = Category D
      PSh = (PshMon.𝓟Mon A ℓ)
      module PSh = MonoidalCategory PSh
      module ℰD = VE ℰD
      module ℰC = VE ℰC
      module F = Functor F
      module Γ*▷*ℰC-Cat = Category Γ*▷*ℰC-Cat
      module Next = Enrichment Next-Enr

    open Functor
    open Enrichment
    open Category
    open EnrichmentFor

    isLocallyContractive : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓC) ℓC')
    isLocallyContractive =
      Σ[ GE ∈ EnrichmentFor PSh target-Enr ℰD F.F-ob ]
          ∀ {x y} → ∀ (f : C.Hom[ x , y ]) →
            ℰD.⌜ F.F-hom f ⌝ ≡ ℰC.⌜ f ⌝ PSh.⋆ (Next.F[ x , y ] PSh.⋆ GE .f[_,_] (F-ob Fun x)(F-ob Fun y))

-- Fam : Category _ _
-- Fam = FamBase.Fam {ℓ = ℓ'} C

-- module HyloPsh (F : LocallyContractive)
--                (X B : Presheaf C ℓ▷)
--                (c : PshHomStrict X (F .fst .F-ob X))
--                (a : PshHomStrict (F .fst .F-ob B) B)
--                where
--   private
--     F₀ = F .fst .F-ob
--     Fδ = F .snd .fst
--     Fhom≡ = F .snd .snd

--   hyloBody : PshHomStrict ((▷ .F-ob (X ⇒ B)) ×Psh X) B
--   hyloBody =
--     (Fδ {X} {B} ×PshHomStrict c)
--       ⋆PshHomStrict appPshHomStrict (F₀ X) (F₀ B)
--       ⋆PshHomStrict a

--   hyloStep : PshHomStrict (▷ .F-ob (X ⇒ B)) (X ⇒ B)
--   hyloStep = λPshHomStrict X B hyloBody

--   hyloTranspose : PshHomStrict UnitPsh (X ⇒ B)
--   hyloTranspose = löb (X ⇒ B) hyloStep

--   private
--     hyloMap : PshHomStrict X B
--     hyloMap =
--       ×PshIntroStrict (UnitPsh-introStrict ⋆PshHomStrict hyloTranspose)
--         idPshHomStrict
--         ⋆PshHomStrict appPshHomStrict X B

--   hyloTranspose-fix :
--     hyloTranspose ≡ (hyloTranspose ⋆PshHomStrict next (X ⇒ B)) ⋆PshHomStrict hyloStep
--   hyloTranspose-fix = löb-fix (X ⇒ B) hyloStep

--   hyloTranspose-uniq :
--     (s : PshHomStrict UnitPsh (X ⇒ B))
--     → s ≡ (s ⋆PshHomStrict next (X ⇒ B)) ⋆PshHomStrict hyloStep
--     → s ≡ hyloTranspose
--   hyloTranspose-uniq = löb-uniq (X ⇒ B) hyloStep

--   hylo : Hylo (F .fst) (X , c) (B , a)
--   hylo .fst = hyloMap
--   hylo .snd = makePshHomStrictPath (funExt λ x → funExt λ p →
--     cong (λ s → s .N-ob x tt .N-ob x (id , p)) hyloTranspose-fix
--     ∙ cong (λ z → a .N-ob x (Fδ .N-ob x z .N-ob x (id , c .N-ob x p)))
--         (funExt⁻ (▷ .F-ob (X ⇒ B) .F-id)
--            (next (X ⇒ B) .N-ob x (hyloTranspose .N-ob x tt))
--          ∙ nextT≡▷transpose x)
--     ∙ cong (λ φ → a .N-ob x (φ .N-ob x (c .N-ob x p)))
--         (sym (funExt⁻ Fhom≡ hyloMap)))
--     where
--     nextT≡▷transpose : ∀ x →
--       next (X ⇒ B) .N-ob x (hyloTranspose .N-ob x tt)
--         ≡ ▷transpose hyloMap .N-ob x tt
--     nextT≡▷transpose x = makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
--       makePshHomStrictPath (funExt λ d → funExt λ (f , ξ) →
--         sym (cong (λ m → hyloTranspose .N-ob x tt .N-ob d (m , ξ))
--                (⋆IdL (f ⋆ g)))
--         ∙ cong (λ α → α .N-ob d (id , ξ))
--             (hyloTranspose .N-hom d x (f ⋆ g) tt tt refl)))

-- _⇒Fam_ : Category.ob Fam → Category.ob Fam → Category.ob Fam
-- (A ⇒Fam B) x = (⟨ A x ⟩ → ⟨ B x ⟩) , isSet→ (B x .snd)

-- ▷HomActionFam : Functor Fam Fam → Type _
-- ▷HomActionFam H =
--   {A B : Category.ob Fam}
--   → Fam [ ▷Fam {ℓF = ℓ-zero} (A ⇒Fam B)
--         , (H .F-ob A ⇒Fam H .F-ob B) ]

-- -- apply a later function-family at a strict bound
-- ▷app : {A B : Category.ob Fam} {x y : ob}
--      → ⟨ ▷Fam {ℓF = ℓ-zero} (A ⇒Fam B) x ⟩
--      → C [ y , x ] → y ≺ x → ⟨ A y ⟩ → ⟨ B y ⟩
-- ▷app β g q = β .N-ob _ (g , q) _ id

-- -- ▷ preserves the pointwise product laxly
-- ▷× : {P Q : Presheaf C ℓ▷}
--    → PshHomStrict (▷ .F-ob P ×Psh ▷ .F-ob Q)
--                   (▷ .F-ob (P ×Psh Q))
-- ▷× .N-ob x (α , β) = ×PshIntroStrict α β
-- ▷× .N-hom x x' f (α' , β') (α , β) e =
--   makePshHomStrictPath refl
--   ∙ (λ i → ×PshIntroStrict (cong fst e i) (cong snd e i))

-- -- H's hom-action factors through nextFam, via Hδ
-- isPwContractiveHomActionFam :
--   (H : Functor Fam Fam) → ▷HomActionFam H → Type _
-- isPwContractiveHomActionFam H Hδ =
--   {A B : Category.ob Fam} (h : Fam [ A , B ]) (x : ob)
--   → H .F-hom h x
--     ≡ Hδ {A} {B} x (nextFam {ℓF = ℓ-zero} (A ⇒Fam B) h x)

-- PointwiseLocallyContractiveFam : Type _
-- PointwiseLocallyContractiveFam =
--   Σ[ H ∈ Functor Fam Fam ]
--   Σ[ Hδ ∈ ▷HomActionFam H ]
--     isPwContractiveHomActionFam H Hδ

-- module HyloFam (H : PointwiseLocallyContractiveFam)
--                (X B : Category.ob Fam)
--                (c : Fam [ X , H .fst .F-ob X ])
--                (a : Fam [ H .fst .F-ob B , B ])
--                where
--   private
--     Hδ = H .snd .fst
--     Hhom≡ = H .snd .snd

--     hyloStep : ∀ x → ⟨ ▷Fam {ℓF = ℓ-zero} (X ⇒Fam B) x ⟩
--              → ⟨ (X ⇒Fam B) x ⟩
--     hyloStep x β ξ = a x (Hδ {X} {B} x β (c x ξ))

--   private
--     hyloMap : Fam [ X , B ]
--     hyloMap = löbFam {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep

--   hylo : Hylo (H .fst) (X , c) (B , a)
--   hylo .fst = hyloMap
--   hylo .snd = funExt λ x →
--     löbFam-unfold {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep x
--     ∙ cong (λ k → λ ξ → a x (k (c x ξ)))
--         (sym (Hhom≡ {X} {B} hyloMap x))

--   hylo-uniq : (h : Hylo (H .fst) (X , c) (B , a)) → h ≡ hylo
--   hylo-uniq (h , he) = ΣPathP (mapEq , path2)
--     where
--       mapEq : h ≡ hyloMap
--       mapEq =
--         löbFam-uniq-unfold {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep h
--           λ x → funExt⁻ he x
--                 ∙ (λ i ξ → a x (Hhom≡ {X} {B} h x i (c x ξ)))

--       path2 : PathP
--         (λ i → mapEq i
--                ≡ (λ x ξ → a x (H .fst .F-hom (mapEq i) x (c x ξ))))
--         he (hylo .snd)
--       path2 = isProp→PathP
--         (λ i → isSetΠ (λ x → isSet→ (B x .snd))
--                  (mapEq i)
--                  (λ x ξ → a x (H .fst .F-hom (mapEq i) x (c x ξ))))
--         he (hylo .snd)

-- -- local contractivity makes the hylomorphism profunctor trivial;
-- -- recursiveness and corecursiveness are its curried readings, and
-- -- finality/initiality at a fixed point follow from FixpointRecursion
-- module Recursiveness (H : PointwiseLocallyContractiveFam) where
--   hyloTrivial : HYLOTrivial (H .fst)
--   hyloTrivial (X , c) (B , a) = HF.hylo , λ h → sym (HF.hylo-uniq h)
--     where module HF = HyloFam H X B c a

--   recursive : ∀ Xc → isRecursiveCoalgebra (H .fst) Xc
--   recursive = HYLOTrivial→recursive (H .fst) hyloTrivial

--   corecursive : ∀ Ba → isCorecursiveAlgebra (H .fst) Ba
--   corecursive = HYLOTrivial→corecursive (H .fst) hyloTrivial
