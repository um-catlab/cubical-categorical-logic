{-

  The usual definition of a displayed category over C is *precisely*
  that of a lax functor from C to Span.

  An (equivalent) alternate definition is instead of a normal lax
  functor from C to Prof. The main difference is that in targeting
  Prof, we define a category of *vertical morphisms* over each object,
  whereas in targeting Span we only define displayed morphisms. Of
  course vertical morphisms can be *defined* as displayed over id, but
  in doing so the definition of composition of vertical morphisms
  *inherently* involves transport, leading to undesirable stuck terms.

-}
module Cubical.Categories.Displayed.Alt.Fibrous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv hiding (fiber)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear
import Cubical.Categories.Displayed.Base as Fiberless
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓCᴰᵥ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Homomorphism
open Bilinear
open Category
open NatElt

record Categoryᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' ℓCᴰᵥ
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' ℓCᴰᵥ)))) where
  no-eta-equality
  field
    disp : Fiberless.Categoryᴰ C ℓCᴰ ℓCᴰ'
  private
    module disp = Fiberless.Categoryᴰ disp
    module R = HomᴰReasoning disp
  field
    vert : ∀ {x} → (xᴰ xᴰ' : disp.ob[ x ]) → Type ℓCᴰᵥ
    idᵥ : ∀ {x}{xᴰ : disp.ob[ x ]} → vert xᴰ xᴰ
    _⋆ᵥ_ : ∀ {x}{xᴰ xᴰ' xᴰ'' : disp.ob[ x ]}
         → vert xᴰ xᴰ' → vert xᴰ' xᴰ'' → vert xᴰ xᴰ''

    vertToDisp : ∀ {x} {xᴰ xᴰ' : disp.ob[ x ]} → vert xᴰ xᴰ'
      → disp.Hom[ C .id ][ xᴰ , xᴰ' ]
    isEquivVertToDisp : ∀ {x} {xᴰ xᴰ' : disp.ob[ x ]}
      → isEquiv (vertToDisp {x}{xᴰ}{xᴰ'})
    vertToDispId : ∀ {x} {xᴰ : disp.ob[ x ]}
      → vertToDisp (idᵥ {xᴰ = xᴰ}) ≡ disp.idᴰ
    vertToDispSeq : ∀ {x}{xᴰ xᴰ' xᴰ'' : disp.ob[ x ]}
      → (v : vert xᴰ xᴰ')(u : vert xᴰ' xᴰ'')
      → vertToDisp (v ⋆ᵥ u)
        disp.≡[ sym (C .⋆IdL _) ] (vertToDisp v disp.⋆ᴰ vertToDisp u)

    _⋆ᵥᴰ_ : ∀ {x y}{xᴰ' xᴰ : disp.ob[ x ]}{yᴰ : disp.ob[ y ]}{f : C [ x , y ]}
          → vert xᴰ' xᴰ → disp.Hom[ f ][ xᴰ , yᴰ ]
          → disp.Hom[ f ][ xᴰ' , yᴰ ]
    vertᵥᴰ : ∀ {x y}{xᴰ' xᴰ : disp.ob[ x ]}{yᴰ : disp.ob[ y ]}{f : C [ x , y ]}
          → (v : vert xᴰ' xᴰ) → (fᴰ : disp.Hom[ f ][ xᴰ , yᴰ ])
          → v ⋆ᵥᴰ fᴰ disp.≡[ sym (C .⋆IdL f) ] vertToDisp v disp.⋆ᴰ fᴰ
    _⋆ᴰᵥ_ : ∀ {x y}{xᴰ : disp.ob[ x ]}{yᴰ yᴰ' : disp.ob[ y ]}{f : C [ x , y ]}
          → disp.Hom[ f ][ xᴰ , yᴰ ] → vert yᴰ yᴰ'
          → disp.Hom[ f ][ xᴰ , yᴰ' ]
    vertᴰᵥ : ∀ {x y}{xᴰ : disp.ob[ x ]}{yᴰ yᴰ' : disp.ob[ y ]}{f : C [ x , y ]}
          → (fᴰ : disp.Hom[ f ][ xᴰ , yᴰ ]) → (v : vert yᴰ yᴰ')
          → fᴰ ⋆ᴰᵥ v disp.≡[ sym (C .⋆IdR f) ] fᴰ disp.⋆ᴰ vertToDisp v

  vertToDispInj = λ {x}{xᴰ}{xᴰ'} →
    isoFunInjective (equivToIso (vertToDisp {x}{xᴰ}{xᴰ'} , isEquivVertToDisp))

  fiber[_] : C .ob → Category ℓCᴰ ℓCᴰᵥ
  fiber[ x ] .ob = disp.ob[ x ]
  fiber[ x ] .Hom[_,_] = vert {x}
  fiber[ x ] .id = idᵥ
  fiber[ x ] ._⋆_ = _⋆ᵥ_
  fiber[ x ] .⋆IdL v = vertToDispInj _ _ (R.≡[]-rectify (
    R.≡[]∙ _ _ (vertToDispSeq _ _)
    (R.≡[]∙ _ _ (R.≡[]⋆ _ refl vertToDispId refl)
    (disp.⋆IdLᴰ (vertToDisp v)))))
  fiber[ x ] .⋆IdR v = vertToDispInj _ _ (R.≡[]-rectify
    (R.≡[]∙ _ _ (vertToDispSeq _ _)
    (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl vertToDispId)
    (disp.⋆IdRᴰ (vertToDisp v)))))
  fiber[ x ] .⋆Assoc u v w = vertToDispInj _ _ (R.≡[]-rectify
    (R.≡[]∙ _ _ (vertToDispSeq _ _)
    (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (vertToDispSeq _ _) refl)
    (R.≡[]∙ _ _ (disp.⋆Assocᴰ _ _ _)
    (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (symP (vertToDispSeq _ _)))
    (symP (vertToDispSeq _ _)))))))
  fiber[ x ] .isSetHom =
    isSetRetract vertToDisp
      (invIsEq isEquivVertToDisp) (retIsEq (isEquivVertToDisp)) disp.isSetHomᴰ

  fiber[_]f : ∀ {x y} → (f : C [ x , y ]) → fiber[ x ] o-[ ℓCᴰ' ]-* fiber[ y ]
  fiber[_]f {x}{y} f = mkBifunctorSep (record
    { Bif-ob = λ xᴰ yᴰ → disp.Hom[ f ][ xᴰ , yᴰ ] , disp.isSetHomᴰ
    ; Bif-homL = λ v yᴰ fᴰ → v ⋆ᵥᴰ fᴰ
    ; Bif-homR = λ xᴰ v fᴰ → fᴰ ⋆ᴰᵥ v
    ; Bif-L-id = λ {xᴰ}{yᴰ} → funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (vertᵥᴰ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl vertToDispId refl)
      (disp.⋆IdLᴰ fᴰ)))
    ; Bif-L-seq = λ u v → funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (vertᵥᴰ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (vertToDispSeq v u) refl)
      (R.≡[]∙ _ _ (disp.⋆Assocᴰ _ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (symP (vertᵥᴰ u fᴰ)))
      (symP (vertᵥᴰ _ _))))))
    ; Bif-R-id = funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (vertᴰᵥ fᴰ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl vertToDispId)
      (disp.⋆IdRᴰ fᴰ)))
    ; Bif-R-seq = λ u v → funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (vertᴰᵥ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (vertToDispSeq u v))
      (R.≡[]∙ _ _ (symP (disp.⋆Assocᴰ _ _ _))
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (symP (vertᴰᵥ fᴰ u)) refl)
      (symP (vertᴰᵥ _ _))))))
    ; SepBif-RL-commute = λ {xᴰ'}{xᴰ}{yᴰ yᴰ'} u v →
      funExt λ fᴰ → R.≡[]-rectify
      (R.≡[]∙ _ _ (vertᵥᴰ _ _)
      (R.≡[]∙ _ _ (R.≡[]⋆ refl _ refl (vertᴰᵥ _ _))
      (R.≡[]∙ _ _ (symP (disp.⋆Assocᴰ _ _ _))
      (R.≡[]∙ _ _ (R.≡[]⋆ _ refl (symP (vertᵥᴰ _ _)) refl)
      (symP (vertᴰᵥ _ _))))))
    })

-- TODO: motivating examples:
-- 1. Slice categories: vertical category should be a commuting
-- triangle, not a commuting square over id.

-- 2. Reindexing: the vertical categories can be taken directly from
-- the codomain, leading to better definitional behavior

-- 3. Displayed limits: the definition of a displayed limit is
-- naturally formulated as having vertical projections and the cone
-- property stated in terms of mixed composition

-- 4. Should also show that defining the fiber as the morphisms over
-- id does allow a displayed cat to be "upgraded" to a redundant displayed cat
