-- A Set-enriched category is a plain category: the hom-objects are
-- `hSet`s, and the enriched `id`, `seq`, and axioms transfer pointwise
-- to the ordinary category structure by applying each enriched arrow
-- in SET to its argument(s).
module Cubical.Categories.Enriched.Instances.ToCat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Sets using (SETMon)

private variable ℓS ℓob : Level

module _ (C : EnrichedCategory (SETMon {ℓS}) ℓob) where
  private module C = EnrichedCategory C

  ToCat : Category ℓob ℓS
  ToCat .Category.ob = C.ob
  ToCat .Category.Hom[_,_] x y = C.Hom[ x , y ] .fst
  ToCat .Category.id = C.id tt*
  ToCat .Category._⋆_ f g = C.seq _ _ _ (f , g)
  ToCat .Category.⋆IdL f = sym (funExt⁻ (C.⋆IdL _ _) (tt* , f))
  ToCat .Category.⋆IdR f = sym (funExt⁻ (C.⋆IdR _ _) (f , tt*))
  ToCat .Category.⋆Assoc f g h =
    funExt⁻ (C.⋆Assoc _ _ _ _) (f , g , h)
  ToCat .Category.isSetHom = C.Hom[ _ , _ ] .snd
