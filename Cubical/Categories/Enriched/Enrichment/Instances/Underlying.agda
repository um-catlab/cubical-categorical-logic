-- Underlying enrichment: given an enriched category `C` over a
-- monoidal category `V`, its data (hom-objects, id, seq, axioms)
-- transports to an `Enrichment` over `V` of its *underlying* plain
-- category — obtained by base-changing `C` along `Γ := V[I,-] : V →
-- Set` and then taking the resulting Set-enriched category as a plain
-- category via `ToCat`.
--
-- Since `(ToCat (Γ* C)).Hom[x, y] = V[I, C.Hom[x, y]]` by definition,
-- `⇄-agree` is the identity isomorphism; the enriched axioms carry
-- over unchanged.
module Cubical.Categories.Enriched.Enrichment.Instances.Underlying where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (idIso)

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Functor.Instances.Set.HomFromUnit
  using (HomFromUnitLax; SetMon)
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.BaseChange.Base as EnrBC
open import Cubical.Categories.Enriched.Instances.ToCat using (ToCat)

private variable ℓV ℓV' ℓ : Level

module _ {V : MonoidalCategory ℓV ℓV'}
         (C : EnrichedCategory V ℓ) where
  private module C = EnrichedCategory C

  Γ : LaxMonoidalFunctor V (SetMon V)
  Γ = HomFromUnitLax V

  Γ*C : EnrichedCategory (SetMon V) ℓ
  Γ*C = EnrBC.BaseChange Γ C

  Γ*C-Cat : Category ℓ ℓV'
  Γ*C-Cat = ToCat Γ*C

  Underlying : Enrichment Γ*C-Cat V
  Underlying .Enrichment.VE[_,_] = C.Hom[_,_]
  Underlying .Enrichment.id = C.id
  Underlying .Enrichment.seq = C.seq
  Underlying .Enrichment.⇄-agree = idIso
  Underlying .Enrichment.⋆IdL = C.⋆IdL
  Underlying .Enrichment.⋆IdR = C.⋆IdR
  Underlying .Enrichment.⋆Assoc = C.⋆Assoc
  Underlying .Enrichment.⌜id⌝ = V.⋆IdL _
    where module V = MonoidalCategory V
  Underlying .Enrichment.⌜⋆⌝ f g = V.⋆Assoc _ _ _
    where module V = MonoidalCategory V
