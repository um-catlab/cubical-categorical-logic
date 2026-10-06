module Cubical.Categories.Enriched.Enrichment.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Sets
open import Cubical.Categories.Enriched.Enrichment.Base

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C

  SET-Enrichment : Enrichment C (SETMon {ℓC'})
  SET-Enrichment .Enrichment.VE[_,_] X Y = C [ X , Y ] , C.isSetHom
  SET-Enrichment .Enrichment.id _ = C.id
  SET-Enrichment .Enrichment.seq _ _ _ (f , g) = f C.⋆ g
  SET-Enrichment .Enrichment.⇄-agree .Iso.fun f _ = f
  SET-Enrichment .Enrichment.⇄-agree .Iso.inv g = g tt*
  SET-Enrichment .Enrichment.⇄-agree .Iso.sec g = refl
  SET-Enrichment .Enrichment.⇄-agree .Iso.ret f = refl
  SET-Enrichment .Enrichment.⋆IdL _ _ = funExt λ (_ , f) → sym (C.⋆IdL f)
  SET-Enrichment .Enrichment.⋆IdR _ _ = funExt λ (f , _) → sym (C.⋆IdR f)
  SET-Enrichment .Enrichment.⋆Assoc _ _ _ _ = funExt λ (f , (g , h)) → C.⋆Assoc f g h
  SET-Enrichment .Enrichment.⌜id⌝ = refl
  SET-Enrichment .Enrichment.⌜⋆⌝ f g = refl
