{-

  Colimits in PRESHEAF are computed pointwise.

  This is the exact mirror image of
  `Cubical.Categories.Presheaf.StrictHom.Pointwise`, which proves the
  limit case.

  Why the argument is *written out* rather than obtained by
  instantiating the limit theorem at an opposite category: to get the
  colimit statement as an instance we would need some `C₀`, `ℓ₀` with
  `PRESHEAF C₀ ℓ₀` definitionally equal to `(PRESHEAF C ℓP) ^op`.
  Matching the object part forces `C₀ = C` and `ℓ₀ = ℓP`, but then the
  hom types disagree: `PshHomStrict P Q` on one side versus
  `PshHomStrict Q P` on the other.  Presheaf categories are not
  self-dual, so no such `C₀` exists.  The codomain fails as well:
  `evPsh c` lands in `SET ℓP`, while the dual statement needs a functor
  into `(SET ℓP) ^op`, which is not `SET ℓ₀` for any `ℓ₀`.  So this is
  the one place where the standing "dualize by instantiation, never
  re-prove" rule genuinely does not apply.

  Note that *defining* cocones via the opposite category is still
  legitimate, and that is what we do: only the theorem fails to
  instantiate, not the definitions.

-}
module Cubical.Categories.Presheaf.StrictHom.PointwiseColim where

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
open import Cubical.Categories.Presheaf.StrictHom.Pointwise

private
  variable
    ℓJ ℓJ' ℓC ℓC' ℓE ℓE' ℓP : Level

open Category
open Functor
open Cone
open LimCone
open PshHomStrict

-- (1) Cocones and colimits, defined via the opposite category.
module _ {J : Category ℓJ ℓJ'} {E : Category ℓE ℓE'} where
  Cocone : (D : Functor J E) (x : E .ob) → Type (ℓ-max (ℓ-max ℓJ ℓJ') ℓE')
  Cocone D x = Cone {J = J ^op} {C = E ^op} (D ^opF) x

  isColimCocone : (D : Functor J E) (x : E .ob) → Cocone D x
                → Type (ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓE) ℓE')
  isColimCocone D x cc = isLimCone {J = J ^op} {C = E ^op} (D ^opF) x cc

  isPropIsColimCocone : (D : Functor J E) (x : E .ob) (cc : Cocone D x)
                      → isProp (isColimCocone D x cc)
  isPropIsColimCocone D x cc = isPropIsLimCone (D ^opF) x cc

  ColimCocone : (D : Functor J E) → Type (ℓ-max (ℓ-max (ℓ-max ℓJ ℓJ') ℓE) ℓE')
  ColimCocone D = LimCone {J = J ^op} {C = E ^op} (D ^opF)

module _ {C : Category ℓC ℓC'} {ℓP : Level} where
  module _ {J : Category ℓJ ℓJ'} {D : Functor J (PRESHEAF C ℓP)} where
    -- (2) The evaluated cocone
    evCocone : (c : C .ob) {P : Presheaf C ℓP} → Cocone D P
             → Cocone (evPsh c ∘F D) (P ⟅ c ⟆)
    evCocone c cc .coneOut v = cc .coneOut v .N-ob c
    evCocone c cc .coneOutCommutes e =
      cong (λ α → α .N-ob c) (cc .coneOutCommutes e)

    -- (3) A cocone that is pointwise colimiting is colimiting in
    -- PRESHEAF.
    module _ {P : Presheaf C ℓP} (cc : Cocone D P)
      (ptColim : ∀ c → isColimCocone (evPsh c ∘F D) (P ⟅ c ⟆) (evCocone c cc))
      where

      module MediatingColim (Q : Presheaf C ℓP) (cc' : Cocone D Q) where
        h : ∀ c → ⟨ P ⟅ c ⟆ ⟩ → ⟨ Q ⟅ c ⟆ ⟩
        h c = ptColim c (Q ⟅ c ⟆) (evCocone c cc') .fst .fst

        hCoconeMor : ∀ c → isConeMor (evCocone c cc') (evCocone c cc) (h c)
        hCoconeMor c = ptColim c (Q ⟅ c ⟆) (evCocone c cc') .fst .snd

        -- The auxiliary cocone used to prove naturality of `h`.
        K : ∀ {c c'} (f : C [ c , c' ]) → Cocone (evPsh c' ∘F D) (Q ⟅ c ⟆)
        K {c} {c'} f .coneOut v p' =
          Q .F-hom f (cc' .coneOut v .N-ob c' p')
        K {c} {c'} f .coneOutCommutes {u} {v} e = funExt λ p' →
          cong (Q .F-hom f)
            (funExt⁻ (cong (λ α → α .N-ob c') (cc' .coneOutCommutes e)) p')

        map1 : ∀ {c c'} (f : C [ c , c' ]) → ⟨ P ⟅ c' ⟆ ⟩ → ⟨ Q ⟅ c ⟆ ⟩
        map1 {c} {c'} f p' = Q .F-hom f (h c' p')

        map2 : ∀ {c c'} (f : C [ c , c' ]) → ⟨ P ⟅ c' ⟆ ⟩ → ⟨ Q ⟅ c ⟆ ⟩
        map2 {c} {c'} f p' = h c (P .F-hom f p')

        map1IsCoconeMor : ∀ {c c'} (f : C [ c , c' ])
          → isConeMor (K f) (evCocone c' cc) (map1 f)
        map1IsCoconeMor {c} {c'} f v = funExt λ d →
          cong (Q .F-hom f) (funExt⁻ (hCoconeMor c' v) d)

        map2IsCoconeMor : ∀ {c c'} (f : C [ c , c' ])
          → isConeMor (K f) (evCocone c' cc) (map2 f)
        map2IsCoconeMor {c} {c'} f v = funExt λ d →
          cong (h c) (cc .coneOut v .N-hom c c' f d _ refl)
          ∙ funExt⁻ (hCoconeMor c v) _
          ∙ sym (cc' .coneOut v .N-hom c c' f d _ refl)

        natEq : ∀ {c c'} (f : C [ c , c' ]) → map1 f ≡ map2 f
        natEq {c} {c'} f = cong fst
          (isContr→isProp (ptColim c' (Q ⟅ c ⟆) (K f))
            (map1 f , map1IsCoconeMor f)
            (map2 f , map2IsCoconeMor f))

        α : PshHomStrict P Q
        α .N-ob = h
        α .N-hom c c' f p' p eq = funExt⁻ (natEq f) p' ∙ cong (h c) eq

        αIsCoconeMor : isConeMor cc' cc α
        αIsCoconeMor v = makePshHomStrictPath (funExt λ c → hCoconeMor c v)

        αUnique : ∀ (βp : Σ[ β ∈ PshHomStrict P Q ] isConeMor cc' cc β)
                → (α , αIsCoconeMor) ≡ βp
        αUnique (β , βIsCoconeMor) = Σ≡Prop (isPropIsConeMor cc' cc)
          (makePshHomStrictPath (funExt λ c → cong fst
            (ptColim c (Q ⟅ c ⟆) (evCocone c cc') .snd
              (β .N-ob c , λ v → cong (λ γ → γ .N-ob c) (βIsCoconeMor v)))))

      open MediatingColim

      isColimCocone-fromPointwise : isColimCocone D P cc
      isColimCocone-fromPointwise Q cc' =
        (α Q cc' , αIsCoconeMor Q cc') , αUnique Q cc'

    -- (4) Pointwise colimits, assuming SET has colimits of shape J for
    -- each of the evaluated diagrams.
    module _ (L : ∀ c → ColimCocone (evPsh c ∘F D)) where

      -- Restriction along `f` is the mediating map for this cocone.
      restrCocone : ∀ {x y} (f : C [ x , y ])
                  → Cocone (evPsh y ∘F D) (L x .lim)
      restrCocone {x} {y} f .coneOut v d =
        limOut (L x) v ((D ⟅ v ⟆) .F-hom f d)
      restrCocone {x} {y} f .coneOutCommutes {u} {v} e = funExt λ d →
        cong (limOut (L x) u) ((D ⟪ e ⟫) .N-hom x y f d _ refl)
        ∙ funExt⁻ (limOutCommutes (L x) e) _

      ColimPsh : Presheaf C ℓP
      ColimPsh .F-ob c = L c .lim
      ColimPsh .F-hom {x} {y} f = limArrow (L x) (L y .lim) (restrCocone f)
      ColimPsh .F-id {x} =
        limArrowUnique (L x) (L x .lim) (restrCocone (C .id)) (λ l → l)
          (λ v → funExt λ d →
            cong (limOut (L x) v) (sym (funExt⁻ ((D ⟅ v ⟆) .F-id) d)))
      ColimPsh .F-seq {x} {y} {z} f g =
        limArrowUnique (L x) (L z .lim) (restrCocone (g ⋆⟨ C ⟩ f))
          (λ l → ColimPsh .F-hom g (ColimPsh .F-hom f l))
          (λ v → funExt λ d →
            cong (ColimPsh .F-hom g)
              (funExt⁻ (limArrowCommutes (L x) (L y .lim) (restrCocone f) v) d)
            ∙ funExt⁻ (limArrowCommutes (L y) (L z .lim) (restrCocone g) v) _
            ∙ cong (limOut (L z) v) (sym (funExt⁻ ((D ⟅ v ⟆) .F-seq f g) d)))

      colimCoconePsh : Cocone D ColimPsh
      colimCoconePsh .coneOut v .N-ob c = limOut (L c) v
      colimCoconePsh .coneOut v .N-hom c c' f p' p eq =
        funExt⁻ (limArrowCommutes (L c') (L c .lim) (restrCocone f) v) p'
        ∙ cong (limOut (L c) v) eq
      colimCoconePsh .coneOutCommutes e =
        makePshHomStrictPath (funExt λ c → limOutCommutes (L c) e)

      evCoconeColimPsh≡ : ∀ c → L c .limCone ≡ evCocone c colimCoconePsh
      evCoconeColimPsh≡ c = cone≡ λ v → refl

      isColimCoconeEvColimPsh : ∀ c
        → isColimCocone (evPsh c ∘F D) (ColimPsh ⟅ c ⟆)
            (evCocone c colimCoconePsh)
      isColimCoconeEvColimPsh c =
        subst (isLimCone ((evPsh c ∘F D) ^opF) (L c .lim))
          (evCoconeColimPsh≡ c) (L c .univProp)

      ColimCoconePRESHEAF : ColimCocone D
      ColimCoconePRESHEAF .lim = ColimPsh
      ColimCoconePRESHEAF .limCone = colimCoconePsh
      ColimCoconePRESHEAF .univProp =
        isColimCocone-fromPointwise colimCoconePsh isColimCoconeEvColimPsh

    -- (5) Conversely: a colimiting cocone in PRESHEAF is pointwise
    -- colimiting.  As in the limit case this is *derived*: the cocone
    -- is uniquely isomorphic to the pointwise colimit cocone of (4),
    -- and evaluating that isomorphism transports colimitingness.
    module _ (L : ∀ c → ColimCocone (evPsh c ∘F D))
      {P : Presheaf C ℓP} (cc : Cocone D P) where

      isColimCocone-pointwise : isColimCocone D P cc
        → ∀ c → isColimCocone (evPsh c ∘F D) (P ⟅ c ⟆) (evCocone c cc)
      isColimCocone-pointwise isColim c =
        Iso→LimCone (limCone (L c)) ec (univProp (L c)) (evCocone c cc)
          ecCoconeMor
        where
          ccColimCocone : ColimCocone D
          ccColimCocone .lim = P
          ccColimCocone .limCone = cc
          ccColimCocone .univProp = isColim

          theIso = LimIso (D ^opF) (ColimCoconePRESHEAF L) ccColimCocone

          e : CatIso ((PRESHEAF C ℓP) ^op) (ColimPsh L) P
          e = theIso .fst .fst

          eCoconeMor : isConeMor (colimCoconePsh L) cc (e .fst)
          eCoconeMor = theIso .fst .snd

          ec : CatIso ((SET ℓP) ^op) (lim (L c)) (P ⟅ c ⟆)
          ec = F-Iso {F = evPsh c ^opF} e

          ecCoconeMor : isConeMor (limCone (L c)) (evCocone c cc) (ec .fst)
          ecCoconeMor v = cong (λ γ → γ .N-ob c) (eCoconeMor v)

      -- The two notions agree.  Both sides are propositions, so a
      -- logical equivalence is an equivalence.
      isColimCocone≃pointwise : isColimCocone D P cc
        ≃ (∀ c → isColimCocone (evPsh c ∘F D) (P ⟅ c ⟆) (evCocone c cc))
      isColimCocone≃pointwise = propBiimpl→Equiv
        (isPropIsColimCocone D P cc)
        (isPropΠ λ c →
          isPropIsColimCocone (evPsh c ∘F D) (P ⟅ c ⟆) (evCocone c cc))
        isColimCocone-pointwise
        (isColimCocone-fromPointwise cc)
