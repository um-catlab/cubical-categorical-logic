{-

  Limits in PRESHEAF are computed pointwise.

  `PRESHEAF C ℓ` is the category of presheaves on `C` with *strict*
  presheaf morphisms (`PshHomStrict`), whose naturality condition is
  forded, and therefore proposition-valued. This makes the "assemble a
  family of pointwise mediating maps into a presheaf morphism" argument
  especially cheap: the only content is that the family is natural, and
  that follows from uniqueness of mediating maps at each stage.

-}
module Cubical.Categories.Presheaf.StrictHom.Pointwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓP : Level

open Category
open Functor
open Cone
open LimCone
open PshHomStrict

module _ {C : Category ℓC ℓC'} {ℓP : Level} where

  -- (1) Evaluation at an object
  evPsh : (c : C .ob) → Functor (PRESHEAF C ℓP) (SET ℓP)
  evPsh c .F-ob P = P ⟅ c ⟆
  evPsh c .F-hom α = α .N-ob c
  evPsh c .F-id = refl
  evPsh c .F-seq α β = refl

  module _ {J : Category ℓJ ℓJ'} {D : Functor J (PRESHEAF C ℓP)} where
    -- (2) The evaluated cone
    evCone : (c : C .ob) {P : Presheaf C ℓP} → Cone D P
           → Cone (evPsh c ∘F D) (P ⟅ c ⟆)
    evCone c cc .coneOut v = cc .coneOut v .N-ob c
    evCone c cc .coneOutCommutes e =
      cong (λ α → α .N-ob c) (cc .coneOutCommutes e)

    -- (4) A cone that is pointwise limiting is limiting in PRESHEAF.
    module _ {P : Presheaf C ℓP} (cc : Cone D P)
      (ptLim : ∀ c → isLimCone (evPsh c ∘F D) (P ⟅ c ⟆) (evCone c cc))
      where

      module Mediating (Q : Presheaf C ℓP) (cc' : Cone D Q) where
        h : ∀ c → ⟨ Q ⟅ c ⟆ ⟩ → ⟨ P ⟅ c ⟆ ⟩
        h c = ptLim c (Q ⟅ c ⟆) (evCone c cc') .fst .fst

        hConeMor : ∀ c → isConeMor (evCone c cc') (evCone c cc) (h c)
        hConeMor c = ptLim c (Q ⟅ c ⟆) (evCone c cc') .fst .snd

        -- The auxiliary cone used to prove naturality of `h`.
        K : ∀ {c c'} (f : C [ c , c' ]) → Cone (evPsh c ∘F D) (Q ⟅ c' ⟆)
        K {c} {c'} f .coneOut v q' =
          (D ⟅ v ⟆) .F-hom f (cc' .coneOut v .N-ob c' q')
        K {c} {c'} f .coneOutCommutes {u} {v} e = funExt λ q' →
          sym ((D ⟪ e ⟫) .N-hom c c' f _ _ refl)
          ∙ cong ((D ⟅ v ⟆) .F-hom f)
              (funExt⁻ (cong (λ α → α .N-ob c') (cc' .coneOutCommutes e)) q')

        map1 : ∀ {c c'} (f : C [ c , c' ]) → ⟨ Q ⟅ c' ⟆ ⟩ → ⟨ P ⟅ c ⟆ ⟩
        map1 {c} {c'} f q' = P .F-hom f (h c' q')

        map2 : ∀ {c c'} (f : C [ c , c' ]) → ⟨ Q ⟅ c' ⟆ ⟩ → ⟨ P ⟅ c ⟆ ⟩
        map2 {c} {c'} f q' = h c (Q .F-hom f q')

        map1IsConeMor : ∀ {c c'} (f : C [ c , c' ])
          → isConeMor (K f) (evCone c cc) (map1 f)
        map1IsConeMor {c} {c'} f v = funExt λ q' →
          sym (cc .coneOut v .N-hom c c' f (h c' q') _ refl)
          ∙ cong ((D ⟅ v ⟆) .F-hom f) (funExt⁻ (hConeMor c' v) q')

        map2IsConeMor : ∀ {c c'} (f : C [ c , c' ])
          → isConeMor (K f) (evCone c cc) (map2 f)
        map2IsConeMor {c} {c'} f v = funExt λ q' →
          funExt⁻ (hConeMor c v) (Q .F-hom f q')
          ∙ sym (cc' .coneOut v .N-hom c c' f q' _ refl)

        natEq : ∀ {c c'} (f : C [ c , c' ]) → map1 f ≡ map2 f
        natEq {c} {c'} f = cong fst
          (isContr→isProp (ptLim c (Q ⟅ c' ⟆) (K f))
            (map1 f , map1IsConeMor f)
            (map2 f , map2IsConeMor f))

        α : PshHomStrict Q P
        α .N-ob = h
        α .N-hom c c' f q' q eq = funExt⁻ (natEq f) q' ∙ cong (h c) eq

        αIsConeMor : isConeMor cc' cc α
        αIsConeMor v = makePshHomStrictPath (funExt λ c → hConeMor c v)

        αUnique : ∀ (βp : Σ[ β ∈ PshHomStrict Q P ] isConeMor cc' cc β)
                → (α , αIsConeMor) ≡ βp
        αUnique (β , βIsConeMor) = Σ≡Prop (isPropIsConeMor cc' cc)
          (makePshHomStrictPath (funExt λ c → cong fst
            (ptLim c (Q ⟅ c ⟆) (evCone c cc') .snd
              (β .N-ob c , λ v → cong (λ γ → γ .N-ob c) (βIsConeMor v)))))

      open Mediating

      isLimCone-fromPointwise : isLimCone D P cc
      isLimCone-fromPointwise Q cc' =
        (α Q cc' , αIsConeMor Q cc') , αUnique Q cc'

    -- (3) Pointwise limits, assuming SET has limits of shape J for
    -- each of the evaluated diagrams.
    module _ (L : ∀ c → LimCone (evPsh c ∘F D)) where

      -- Restriction along `f` is the mediating map for this cone.
      restrCone : ∀ {x y} (f : C [ x , y ]) → Cone (evPsh x ∘F D) (L y .lim)
      restrCone {x} {y} f .coneOut v l =
        (D ⟅ v ⟆) .F-hom f (limOut (L y) v l)
      restrCone {x} {y} f .coneOutCommutes {u} {v} e = funExt λ l →
        sym ((D ⟪ e ⟫) .N-hom x y f _ _ refl)
        ∙ cong ((D ⟅ v ⟆) .F-hom f) (funExt⁻ (limOutCommutes (L y) e) l)

      LimPsh : Presheaf C ℓP
      LimPsh .F-ob c = L c .lim
      LimPsh .F-hom {x} {y} f = limArrow (L y) (L x .lim) (restrCone f)
      LimPsh .F-id {x} =
        limArrowUnique (L x) (L x .lim) (restrCone (C .id)) (λ l → l)
          (λ v → funExt λ l →
            sym (funExt⁻ ((D ⟅ v ⟆) .F-id) (limOut (L x) v l)))
      LimPsh .F-seq {x} {y} {z} f g =
        limArrowUnique (L z) (L x .lim) (restrCone (g ⋆⟨ C ⟩ f))
          (λ l → LimPsh .F-hom g (LimPsh .F-hom f l))
          (λ v → funExt λ l →
            funExt⁻ (limArrowCommutes (L z) (L y .lim) (restrCone g) v)
              (LimPsh .F-hom f l)
            ∙ cong ((D ⟅ v ⟆) .F-hom g)
                (funExt⁻ (limArrowCommutes (L y) (L x .lim) (restrCone f) v) l)
            ∙ sym (funExt⁻ ((D ⟅ v ⟆) .F-seq f g) (limOut (L x) v l)))

      limConePsh : Cone D LimPsh
      limConePsh .coneOut v .N-ob c = limOut (L c) v
      limConePsh .coneOut v .N-hom c c' f p' p eq =
        sym (funExt⁻ (limArrowCommutes (L c) (L c' .lim) (restrCone f) v) p')
        ∙ cong (limOut (L c) v) eq
      limConePsh .coneOutCommutes e =
        makePshHomStrictPath (funExt λ c → limOutCommutes (L c) e)

      evConeLimPsh≡ : ∀ c → L c .limCone ≡ evCone c limConePsh
      evConeLimPsh≡ c = cone≡ λ v → refl

      isLimConeEvConeLimPsh :
        ∀ c → isLimCone (evPsh c ∘F D) (LimPsh ⟅ c ⟆) (evCone c limConePsh)
      isLimConeEvConeLimPsh c =
        subst (isLimCone (evPsh c ∘F D) (L c .lim)) (evConeLimPsh≡ c)
          (L c .univProp)

      LimConePRESHEAF : LimCone D
      LimConePRESHEAF .lim = LimPsh
      LimConePRESHEAF .limCone = limConePsh
      LimConePRESHEAF .univProp =
        isLimCone-fromPointwise limConePsh isLimConeEvConeLimPsh

    -- (5) Conversely: a limiting cone in PRESHEAF is pointwise
    -- limiting.  This is *derived*, not proved directly: the cone is
    -- uniquely isomorphic to the pointwise limit cone of (3), and
    -- evaluating that isomorphism transports limitingness.
    module _ (L : ∀ c → LimCone (evPsh c ∘F D))
      {P : Presheaf C ℓP} (cc : Cone D P) where

      isLimCone-pointwise : isLimCone D P cc
        → ∀ c → isLimCone (evPsh c ∘F D) (P ⟅ c ⟆) (evCone c cc)
      isLimCone-pointwise isLim c =
        Iso→LimCone (limCone (L c)) ec (univProp (L c)) (evCone c cc)
          ecConeMor
        where
          ccLimCone : LimCone D
          ccLimCone .lim = P
          ccLimCone .limCone = cc
          ccLimCone .univProp = isLim

          e : CatIso (PRESHEAF C ℓP) (LimPsh L) P
          e = LimIso D (LimConePRESHEAF L) ccLimCone .fst .fst

          eConeMor : isConeMor (limConePsh L) cc (e .fst)
          eConeMor = LimIso D (LimConePRESHEAF L) ccLimCone .fst .snd

          ec : CatIso (SET ℓP) (lim (L c)) (P ⟅ c ⟆)
          ec = F-Iso {F = evPsh c} e

          ecConeMor : isConeMor (limCone (L c)) (evCone c cc) (ec .fst)
          ecConeMor v = cong (λ γ → γ .N-ob c) (eConeMor v)

      -- The two notions agree.  Both sides are propositions, so a
      -- logical equivalence is an equivalence.
      isLimCone≃pointwise : isLimCone D P cc
        ≃ (∀ c → isLimCone (evPsh c ∘F D) (P ⟅ c ⟆) (evCone c cc))
      isLimCone≃pointwise = propBiimpl→Equiv
        (isPropIsLimCone D P cc)
        (isPropΠ λ c → isPropIsLimCone (evPsh c ∘F D) (P ⟅ c ⟆) (evCone c cc))
        isLimCone-pointwise
        (isLimCone-fromPointwise cc)
