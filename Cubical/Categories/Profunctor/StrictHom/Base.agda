module Cubical.Categories.Profunctor.StrictHom.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.StrictHom.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D

  -- Strict versions of relator morphisms
  RelatorHomStrict : (P : C o-[ ℓP ]-* D) → (Q : C o-[ ℓQ ]-* D) → Type _
  RelatorHomStrict P Q = PshHomStrict (Relator→Psh P) (Relator→Psh Q)

  RelatorIsoStrict : (P : C o-[ ℓP ]-* D) → (Q : C o-[ ℓQ ]-* D) → Type _
  RelatorIsoStrict P Q = PshIsoStrict (Relator→Psh P) (Relator→Psh Q)

  module _ {P : C o-[ ℓP ]-* D}{Q : C o-[ ℓQ ]-* D} where
    private
      module P = RelatorNotation P
      module Q = RelatorNotation Q
    open PshHomStrict

    appL-HomStrict : RelatorHomStrict P Q → ∀ c →
      PshHomStrict (P.rappL c) (Q.rappL c)
    appL-HomStrict α c .N-ob d = α .N-ob (c , d)
    appL-HomStrict α c .N-hom d d' f p' p e =
      (funExt⁻ (Q.Bif-R×-agree f) _)
      ∙ α .N-hom (c , d) (c , d') (C.id , f) p' (P.Bif-hom× (Category.id (C ^op)) f p') refl
      ∙ cong (α .N-ob _) ((sym $ funExt⁻ (P.Bif-R×-agree f) p') ∙ e)

    appR-HomStrict : RelatorHomStrict P Q → ∀ d → PshHomStrict (appR P d) (appR Q d)
    appR-HomStrict α d .N-ob c = α .N-ob (c , d)
    appR-HomStrict α d .N-hom c c' f p' p e =
      (funExt⁻ (Q.Bif-L×-agree f) _)
      ∙ α .N-hom (c , d) (c' , d) (f , D.id) p' _ refl
      ∙ cong (α .N-ob _) ((sym $ funExt⁻ (P.Bif-L×-agree f) p') ∙ e)

  module _ {P : C o-[ ℓP ]-* D}{Q : C o-[ ℓQ ]-* D} where
    private
      module P = RelatorNotation P
      module Q = RelatorNotation Q
    open PshIsoStrict

    -- Apply isomorphism to left argument
    appL-IsoStrict : RelatorIsoStrict P Q → ∀ c → PshIsoStrict (P.rappL c) (Q.rappL c)
    appL-IsoStrict α c .trans = appL-HomStrict (α .trans) c
    appL-IsoStrict α c .nIso d = α .nIso (c , d)

    -- Apply isomorphism to right argument
    appR-IsoStrict : RelatorIsoStrict P Q → ∀ c → PshIsoStrict (appR P c) (appR Q c)
    appR-IsoStrict α d .trans = appR-HomStrict (α .trans) d
    appR-IsoStrict α d .nIso c = α .nIso (c , d)
