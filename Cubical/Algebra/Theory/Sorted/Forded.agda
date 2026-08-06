-- How much of `ALGᴰ`'s homomorphism condition can be forded?
--
-- `Sorted.ALGᴰ` fords the *result* of the condition,
--
--     (o) (x) (y) → y ≡ α o x → f _ y ≡ β o (λ a → f _ (x a)) ,
--
-- and all three of its category laws are `refl`.  Three results
-- downstream are not: `Section.MODOVERᴰ`'s laws, `Section.ReindexMod`'s
-- `F-id`/`F-seq`, and `Theories.MODReindexᴰ`'s `F-idᴰ`/`F-seqᴰ`.  All
-- three were traced to `resHomCondᶠ`, which must exchange
-- `f (coeArg z)` for `coeArg (f z)` *underneath* `β o (—)`, and the
-- pinned argument makes that a `cong`.
--
-- PART ONE records the obvious repair -- ford the argument position too
-- -- and the fact that it does not work.  `Homᶠ` below takes the
-- arguments `z` of `β` free, together with `(a) → z a ≡ f _ (x a)`.
-- Neither unit law survives:
--
--   `⋆ᶠIdL`, with the composite feeding `idᶠ` the trivial rewrite:
--     hcomp (doubleComp-faces (λ _ → y)
--            (λ i → α o (funExt (λ a i₁ → x a) i)) i) (x₁ i)
--     and x₁ i are not equal
--
--   `⋆ᶠIdR`, with `idᶠ` post-processing what `ϕ` produced:
--     hcomp (doubleComp-faces (λ _ → f (σ .resultSort o) y)
--            (λ i → β o (funExt (λ a i₁ → x a (~ i₁)) i)) i)
--           (ϕ o x₁ y (λ a → f (σ .sortOf o a) (x₁ a)) x₂
--            (λ a _ → f (σ .sortOf o a) (x₁ a)) i)
--     and ϕ o x₁ y z x₂ x i are not equal
--
-- The second is structural, and no choice of `idᶠ` repairs it.  The
-- result ford works because the hypothesis of `ψ` is the *conclusion*
-- of `ϕ`: composition is composition of functions, `idᶠ` is the
-- identity function, so the laws are `refl`.  An argument ford is not
-- chained that way.  `_⋆ᶠ_` can only hand `ϕ` the trivial rewrite
-- `λ a → refl` -- anything else needs `cong g` to retype the
-- hypothesis -- so the rewrite `hz` is always consumed by the second
-- factor.  For `⋆IdR` that second factor is `idᶠ`, which is forced by
-- its own type to use `hz` (its conclusion mentions `z`, its hypothesis
-- `x`), so `⋆IdR` asks a variable `ϕ` to be natural in `hz`.  That is a
-- property, not a definitional equality.
--
-- Fording the *conclusion* is strictly worse: `Homᶜ` below fords only
-- the conclusion, keeping `ALGᴰ`'s arguments pinned, and already
--
--   `⋆ᶜIdL`:
--     hcomp (doubleComp-faces (λ _ → y) (λ _ → α o (λ a → x a)) i)
--           (x₁ i)
--     and x₁ i are not equal
--
-- because `idᶜ` must compose its two hypotheses.  Double-forded
-- equations have no strict identity: `Hom(-,a) → Hom(b,=) → …` is not
-- a Yoneda chain.
--
-- PART TWO does make the restriction definitional, by fording the
-- *sorts* rather than the arguments.  Interpret the operations not on
-- `X` but on
--
--     Yon X t = (s : S) → s Eq.≡ t → X s ,
--
-- the dual of `Theories.Cay`, and state the homomorphism condition
-- pointwise in `(s , e)` rather than at a whole `Yon`-element.  Then a
-- signature map acts on an interpretation by *precomposing* its sort
-- coherences, which commutes with postcomposing `f` on the nose, and
-- the result coercion lands on `e` instead of on the forded `y`.  The
-- consequences, all `refl` and all checked below:
--
--   * `ALGᴰʸ`'s three laws, exactly as for `ALGᴰ`;
--   * `resOpsʸId`, `resOpsʸ⋆` -- restriction strictly functorial;
--   * `resHomCondʸ` -- a bare application of the τ-condition, with no
--     `cong` and no `_∙_` anywhere;
--   * `ALGReindexʸ`'s and `MODReindexʸ`'s `F-idᴰ` and `F-seqᴰ`, the
--     analogue of `Theories.MODReindexᴰ`;
--   * `ReindexModʸ`'s `F-id` and `F-seq`, the analogue of
--     `Section.ReindexMod`, together with `resHomCondʸId` and
--     `resHomCondʸ⋆`, which are what `Section.MODOVERᴰ`'s laws consume.
--
-- `Yon X t ≃ X t` (`YonIso`), so, exactly as for `Cay`, this is a
-- change of presentation and not of content.
module Cubical.Algebra.Theory.Sorted.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.TotalCategory

open import Cubical.Algebra.Theory.Sorted

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level
    ℓ1 ℓ1' ℓ2 ℓ2' ℓ3 ℓ3' ℓ4 ℓ4' : Level
    ℓ1'' ℓ2'' ℓw : Level

open SortedSig
open SortedEqns

-- ------------------------------------------------------------------
-- PART ONE: the argument ford, and why it does not work
-- ------------------------------------------------------------------

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') {ℓX : Level} where

  Homᶠ : {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
    → Ops {σ = σ} (λ s → ⟨ X s ⟩) → Ops {σ = σ} (λ s → ⟨ Y s ⟩) → Type _
  Homᶠ {X = X} {Y = Y} f α β =
    (o : σ .ops) (x : (a : σ .arities o) → ⟨ X (σ .sortOf o a) ⟩)
    (y : ⟨ X (σ .resultSort o) ⟩)
    (z : (a : σ .arities o) → ⟨ Y (σ .sortOf o a) ⟩)
    → y ≡ α o x
    → ((a : σ .arities o) → z a ≡ f (σ .sortOf o a) (x a))
    → f (σ .resultSort o) y ≡ β o z

  idᶠ : {X : S → hSet ℓX} (α : Ops {σ = σ} (λ s → ⟨ X s ⟩))
    → Homᶠ {X = X} {Y = X} (λ s x → x) α α
  idᶠ α o x y z eq hz = eq ∙ cong (α o) (funExt (λ a → sym (hz a)))

  _⋆ᶠ_ : {X Y Z : S → hSet ℓX}
    {f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩} {g : (s : S) → ⟨ Y s ⟩ → ⟨ Z s ⟩}
    {α : Ops {σ = σ} (λ s → ⟨ X s ⟩)} {β : Ops {σ = σ} (λ s → ⟨ Y s ⟩)}
    {γ : Ops {σ = σ} (λ s → ⟨ Z s ⟩)}
    → Homᶠ {X = X} {Y = Y} f α β → Homᶠ {X = Y} {Y = Z} g β γ
    → Homᶠ {X = X} {Y = Z} (λ s x → g s (f s x)) α γ
  _⋆ᶠ_ {f = f} ϕ ψ o x y z eq hz =
    ψ o (λ a → f (σ .sortOf o a) (x a)) (f (σ .resultSort o) y) z
      (ϕ o x y (λ a → f (σ .sortOf o a) (x a)) eq (λ a → refl)) hz

  isPropHomᶠ : {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
    (α : Ops {σ = σ} (λ s → ⟨ X s ⟩)) (β : Ops {σ = σ} (λ s → ⟨ Y s ⟩))
    → isProp (Homᶠ {X = X} {Y = Y} f α β)
  isPropHomᶠ {Y = Y} f α β =
    isPropΠ4 (λ o x y z → isPropΠ2 (λ _ _ → Y _ .snd _ _))

  module _ {X Y : S → hSet ℓX} {f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩}
    {α : Ops {σ = σ} (λ s → ⟨ X s ⟩)} {β : Ops {σ = σ} (λ s → ⟨ Y s ⟩)}
    (ϕ : Homᶠ {X = X} {Y = Y} f α β) where

    ⋆ᶠIdL :
      _⋆ᶠ_ {X = X} {Y = X} {Z = Y} {f = λ s w → w} {g = f}
        {α = α} {β = α} {γ = β} (idᶠ {X = X} α) ϕ
      ≡ ϕ
    ⋆ᶠIdL = isPropHomᶠ {X = X} {Y = Y} f α β _ _

    ⋆ᶠIdR :
      _⋆ᶠ_ {X = X} {Y = Y} {Z = Y} {f = f} {g = λ s w → w}
        {α = α} {β = β} {γ = β} ϕ (idᶠ {X = Y} β)
      ≡ ϕ
    ⋆ᶠIdR = isPropHomᶠ {X = X} {Y = Y} f α β _ _

-- the conclusion ford on its own: `ALGᴰ`'s arguments, but the
-- conclusion consumed rather than produced.  `⋆ᶜIdL` already fails.
module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') {ℓX : Level} where

  Homᶜ : {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
    → Ops {σ = σ} (λ s → ⟨ X s ⟩) → Ops {σ = σ} (λ s → ⟨ Y s ⟩) → Type _
  Homᶜ {X = X} {Y = Y} f α β =
    (o : σ .ops) (x : (a : σ .arities o) → ⟨ X (σ .sortOf o a) ⟩)
    (y : ⟨ X (σ .resultSort o) ⟩) (w : ⟨ Y (σ .resultSort o) ⟩)
    → y ≡ α o x
    → β o (λ a → f (σ .sortOf o a) (x a)) ≡ w
    → f (σ .resultSort o) y ≡ w

  idᶜ : {X : S → hSet ℓX} (α : Ops {σ = σ} (λ s → ⟨ X s ⟩))
    → Homᶜ {X = X} {Y = X} (λ s x → x) α α
  idᶜ α o x y w eq hw = eq ∙ hw

  _⋆ᶜ_ : {X Y Z : S → hSet ℓX}
    {f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩} {g : (s : S) → ⟨ Y s ⟩ → ⟨ Z s ⟩}
    {α : Ops {σ = σ} (λ s → ⟨ X s ⟩)} {β : Ops {σ = σ} (λ s → ⟨ Y s ⟩)}
    {γ : Ops {σ = σ} (λ s → ⟨ Z s ⟩)}
    → Homᶜ {X = X} {Y = Y} f α β → Homᶜ {X = Y} {Y = Z} g β γ
    → Homᶜ {X = X} {Y = Z} (λ s x → g s (f s x)) α γ
  _⋆ᶜ_ {f = f} {β = β} ϕ ψ o x y w eq hw =
    ψ o (λ a → f (σ .sortOf o a) (x a)) (f (σ .resultSort o) y) w
      (ϕ o x y (β o (λ a → f (σ .sortOf o a) (x a))) eq refl) hw

  module _ {X Y : S → hSet ℓX} {f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩}
    {α : Ops {σ = σ} (λ s → ⟨ X s ⟩)} {β : Ops {σ = σ} (λ s → ⟨ Y s ⟩)}
    (ϕ : Homᶜ {X = X} {Y = Y} f α β) where

    ⋆ᶜIdL :
      _⋆ᶜ_ {X = X} {Y = X} {Z = Y} {f = λ s w → w} {g = f}
        {α = α} {β = α} {γ = β} (idᶜ {X = X} α) ϕ
      ≡ ϕ
    ⋆ᶜIdL =
      isPropΠ4 (λ o x y w → isPropΠ2 (λ _ _ → Y _ .snd _ _)) _ _

-- ------------------------------------------------------------------
-- PART TWO: fording the sorts instead
-- ------------------------------------------------------------------
--
-- `Yon` is the Yoneda-form carrier dual to `Theories.Cay`: where `Cay`
-- is transport-closed by carrying an equation *out of* the sort, `Yon`
-- is transport-closed by consuming one.  A signature map then acts by
-- precomposition, and precomposition commutes with `YonMap f` on the
-- nose -- that is the whole trick.
module _ {S : Type ℓS} where

  Yon : (S → Type ℓX) → S → Type (ℓ-max ℓS ℓX)
  Yon X t = (s : S) → s Eq.≡ t → X s

  module _ {X Y : S → Type ℓX} (f : (s : S) → X s → Y s) where
    YonMap : {t : S} → Yon X t → Yon Y t
    YonMap k s e = f s (k s e)

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (ℓX : Level) where

  ALGᴰʸ : Categoryᴰ (FAM S ℓX) _ _
  ALGᴰʸ .Categoryᴰ.ob[_] X = Ops {σ = σ} (Yon (λ s → ⟨ X s ⟩))
  ALGᴰʸ .Categoryᴰ.Hom[_][_,_] {x = X} {y = Y} f α β =
    (o : σ .ops)
    (x : (a : σ .arities o) → Yon (λ s → ⟨ X s ⟩) (σ .sortOf o a))
    (s : S) (e : s Eq.≡ σ .resultSort o) (y : ⟨ X s ⟩)
    → y ≡ α o x s e
    → f s y ≡ β o (λ a → YonMap f (x a)) s e
  ALGᴰʸ .Categoryᴰ.idᴰ o x s e y eq = eq
  ALGᴰʸ .Categoryᴰ._⋆ᴰ_ {f = f} ϕ ψ o x s e y eq =
    ψ o (λ a → YonMap f (x a)) s e (f s y) (ϕ o x s e y eq)
  ALGᴰʸ .Categoryᴰ.⋆IdLᴰ ϕ = refl
  ALGᴰʸ .Categoryᴰ.⋆IdRᴰ ϕ = refl
  ALGᴰʸ .Categoryᴰ.⋆Assocᴰ ϕ ψ χ = refl
  ALGᴰʸ .Categoryᴰ.isSetHomᴰ {y = Y} =
    isProp→isSet (isPropΠ5 (λ o x s e y → isPropΠ (λ _ → Y s .snd _ _)))

-- signature maps whose sort coherences are in the Yoneda form dual to
-- `Theories.SortedSigMapᶠ`: arguments are pulled back, results pushed
-- forward, which is what `Yon` (rather than `Cay`) asks for
record SigMapʸ {S : Type ℓS}
  (σ : SortedSig S ℓ1 ℓ1') (τ : SortedSig S ℓ2 ℓ2')
  : Type (ℓ-max ℓS (ℓ-max ℓ1 (ℓ-max ℓ2 (ℓ-max ℓ1' ℓ2')))) where
  field
    onOps : σ .ops → τ .ops
    unArity : (o : σ .ops) → τ .arities (onOps o) → σ .arities o
    unSortOf : (o : σ .ops) (b : τ .arities (onOps o)) (s : S)
      → s Eq.≡ τ .sortOf (onOps o) b → s Eq.≡ σ .sortOf o (unArity o b)
    unResult : (o : σ .ops) (s : S)
      → s Eq.≡ σ .resultSort o → s Eq.≡ τ .resultSort (onOps o)

open SigMapʸ

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} where

  idSigMapʸ : SigMapʸ σ σ
  idSigMapʸ .onOps o = o
  idSigMapʸ .unArity o a = a
  idSigMapʸ .unSortOf o b s e = e
  idSigMapʸ .unResult o s e = e

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SigMapʸ σ τ) (G : SigMapʸ τ υ) where

  _⋆SigMapʸ_ : SigMapʸ σ υ
  _⋆SigMapʸ_ .onOps o = G .onOps (F .onOps o)
  _⋆SigMapʸ_ .unArity o a = F .unArity o (G .unArity (F .onOps o) a)
  _⋆SigMapʸ_ .unSortOf o b s e =
    F .unSortOf o (G .unArity (F .onOps o) b) s
      (G .unSortOf (F .onOps o) b s e)
  _⋆SigMapʸ_ .unResult o s e =
    G .unResult (F .onOps o) s (F .unResult o s e)

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SigMapʸ σ τ) where

  ⋆SigMapʸIdL : (idSigMapʸ ⋆SigMapʸ F) ≡ F
  ⋆SigMapʸIdL = refl

  ⋆SigMapʸIdR : (F ⋆SigMapʸ idSigMapʸ) ≡ F
  ⋆SigMapʸIdR = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} {ν : SortedSig S ℓ4 ℓ4'}
  (F : SigMapʸ σ τ) (G : SigMapʸ τ υ) (H : SigMapʸ υ ν) where

  ⋆SigMapʸAssoc :
    ((F ⋆SigMapʸ G) ⋆SigMapʸ H) ≡ (F ⋆SigMapʸ (G ⋆SigMapʸ H))
  ⋆SigMapʸAssoc = refl

-- restriction of interpretations: precomposition with the coherences,
-- no transport anywhere
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (F : SigMapʸ σ τ) where

  resOpsʸ : (X : S → Type ℓX)
    → Ops {σ = τ} (Yon X) → Ops {σ = σ} (Yon X)
  resOpsʸ X α o x s e =
    α (F .onOps o)
      (λ b s' e' → x (F .unArity o b) s' (F .unSortOf o b s' e'))
      s (F .unResult o s e)

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} (X : S → Type ℓX)
  (α : Ops {σ = σ} (Yon X)) where

  resOpsʸId : resOpsʸ (idSigMapʸ {σ = σ}) X α ≡ α
  resOpsʸId = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} (F : SigMapʸ σ τ) (G : SigMapʸ τ υ)
  (X : S → Type ℓX) (α : Ops {σ = υ} (Yon X)) where

  resOpsʸ⋆ : resOpsʸ (F ⋆SigMapʸ G) X α ≡ resOpsʸ F X (resOpsʸ G X α)
  resOpsʸ⋆ = refl

-- THE MEASUREMENT: restriction of a homomorphism condition along a
-- signature map, against `ALGᴰʸ`.  No `cong`, no `_∙_`: `ψ` is applied
-- to the pulled-back arguments and the pushed-forward result sort.
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {ℓX : Level} (F : SigMapʸ σ τ) {X Y : S → hSet ℓX}
  (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  (β : Ops {σ = τ} (Yon (λ s → ⟨ X s ⟩)))
  (γ : Ops {σ = τ} (Yon (λ s → ⟨ Y s ⟩)))
  (ψ : Categoryᴰ.Hom[_][_,_] (ALGᴰʸ τ ℓX) {x = X} {y = Y} f β γ) where

  resHomCondʸ :
    Categoryᴰ.Hom[_][_,_] (ALGᴰʸ σ ℓX) {x = X} {y = Y} f
      (resOpsʸ F (λ s → ⟨ X s ⟩) β) (resOpsʸ F (λ s → ⟨ Y s ⟩) γ)
  resHomCondʸ o x s e y eq =
    ψ (F .onOps o)
      (λ b s' e' → x (F .unArity o b) s' (F .unSortOf o b s' e'))
      s (F .unResult o s e) y eq

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (ℓX : Level) (F : SigMapʸ σ τ) where

  ALGReindexʸ : Functorⱽ (ALGᴰʸ τ ℓX) (ALGᴰʸ σ ℓX)
  ALGReindexʸ .Functorᴰ.F-obᴰ {x = X} β = resOpsʸ F (λ s → ⟨ X s ⟩) β
  ALGReindexʸ .Functorᴰ.F-homᴰ {x = X} {y = Y} {f = f} {xᴰ = β} {yᴰ = γ}
    ψ = resHomCondʸ F {X = X} {Y = Y} f β γ ψ
  ALGReindexʸ .Functorᴰ.F-idᴰ {x = X} {xᴰ = β} = refl
  ALGReindexʸ .Functorᴰ.F-seqᴰ {x = X} {y = Y} {z = Z}
    {xᴰ = β} {yᴰ = γ} {zᴰ = δ} ψ χ = refl

-- the rest of the tower, over `ALGᴰʸ`
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (ℓX : Level) where

  ALGʸ : Category _ _
  ALGʸ = ∫C (ALGᴰʸ σ ℓX)

  EQNSᴰʸ : Categoryᴰ ALGʸ _ _
  EQNSᴰʸ .Categoryᴰ.ob[_] (X , α) =
    (e : σeq .eqns)
    (ρ : (v : σeq .vars e) → Yon (λ s → ⟨ X s ⟩) (σeq .varSort e v))
    → TmRec (Yon (λ s → ⟨ X s ⟩)) α ρ (σeq .lhs e)
      ≡ TmRec (Yon (λ s → ⟨ X s ⟩)) α ρ (σeq .rhs e)
  EQNSᴰʸ .Categoryᴰ.Hom[_][_,_] _ _ _ = Unit* {ℓ-zero}
  EQNSᴰʸ .Categoryᴰ.idᴰ = tt*
  EQNSᴰʸ .Categoryᴰ._⋆ᴰ_ _ _ = tt*
  EQNSᴰʸ .Categoryᴰ.⋆IdLᴰ _ = refl
  EQNSᴰʸ .Categoryᴰ.⋆IdRᴰ _ = refl
  EQNSᴰʸ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  EQNSᴰʸ .Categoryᴰ.isSetHomᴰ = isProp→isSet (λ _ _ → refl)

  MODᴰʸ : Categoryᴰ (FAM S ℓX) _ _
  MODᴰʸ = ∫Cᴰ (ALGᴰʸ σ ℓX) EQNSᴰʸ

  MODʸ : Category _ _
  MODʸ = ∫C MODᴰʸ

  ModHomʸ : (M N : Category.ob MODʸ) → Type _
  ModHomʸ M N = MODʸ [ M , N ]

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SigMapʸ σ τ) where

  PresEqnsʸ : Type _
  PresEqnsʸ = (X : S → hSet ℓX)
    (α : Ops {σ = τ} (Yon (λ s → ⟨ X s ⟩)))
    (sat : (e : τeq .eqns)
           (ρ : (v : τeq .vars e)
              → Yon (λ s → ⟨ X s ⟩) (τeq .varSort e v))
         → TmRec (Yon (λ s → ⟨ X s ⟩)) α ρ (τeq .lhs e)
           ≡ TmRec (Yon (λ s → ⟨ X s ⟩)) α ρ (τeq .rhs e))
    (e : σeq .eqns)
    (ρ : (v : σeq .vars e) → Yon (λ s → ⟨ X s ⟩) (σeq .varSort e v))
    → TmRec (Yon (λ s → ⟨ X s ⟩)) (resOpsʸ F (λ s → ⟨ X s ⟩) α) ρ
        (σeq .lhs e)
      ≡ TmRec (Yon (λ s → ⟨ X s ⟩)) (resOpsʸ F (λ s → ⟨ X s ⟩) α) ρ
          (σeq .rhs e)

  isPropPresEqnsʸ : isProp PresEqnsʸ
  isPropPresEqnsʸ =
    isPropΠ5 (λ X _ _ e _ →
      isSetΠ2 (λ s _ → X s .snd) _ _)

  module _ (pres : PresEqnsʸ) where

    -- the sorted analogue of `Theories.MODReindexᴰ`, and it is strict
    MODReindexʸ : Functorⱽ (MODᴰʸ τeq ℓX) (MODᴰʸ σeq ℓX)
    MODReindexʸ .Functorᴰ.F-obᴰ {x = X} Mᴰ =
      resOpsʸ F (λ s → ⟨ X s ⟩) (Mᴰ .fst)
      , pres X (Mᴰ .fst) (Mᴰ .snd)
    MODReindexʸ .Functorᴰ.F-homᴰ {x = X} {y = Y} {f = f}
      {xᴰ = Mᴰ} {yᴰ = Nᴰ} ϕ =
      resHomCondʸ F {X = X} {Y = Y} f (Mᴰ .fst) (Nᴰ .fst) (ϕ .fst) , tt*
    MODReindexʸ .Functorᴰ.F-idᴰ {x = X} {xᴰ = Mᴰ} = refl
    MODReindexʸ .Functorᴰ.F-seqᴰ {x = X} {y = Y} {z = Z}
      {xᴰ = Mᴰ} {yᴰ = Nᴰ} {zᴰ = Pᴰ} ϕ ψ = refl

-- `Yon X t ≃ X t`, so this is a change of presentation, not of content
module _ {S : Type ℓS} {X : S → Type ℓX} where

  εYon : {t : S} → Yon X t → X t
  εYon {t = t} k = k t Eq.refl

  ηYon : {t : S} → X t → Yon X t
  ηYon z s e = Eq.transport X (Eq.sym e) z

  εηYon : {t : S} (z : X t) → εYon (ηYon z) ≡ z
  εηYon z = refl

  ηεYon : {t : S} (k : Yon X t) → ηYon (εYon k) ≡ k
  ηεYon {t = t} k = funExt (λ s → funExt (λ e → lem s e))
    where
      lem : (s : S) (e : s Eq.≡ t)
        → Eq.transport X (Eq.sym e) (k t Eq.refl) ≡ k s e
      lem s Eq.refl = refl

  YonIso : {t : S} → Iso (Yon X t) (X t)
  YonIso .Iso.fun = εYon
  YonIso .Iso.inv = ηYon
  YonIso .Iso.sec = εηYon
  YonIso .Iso.ret = ηεYon

isSetYon : {S : Type ℓS} {X : S → Type ℓX}
  → ((s : S) → isSet (X s)) → (t : S) → isSet (Yon X t)
isSetYon isSetX t = isSetΠ2 (λ s _ → isSetX s)

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {X : S → Type ℓX} where

  liftOpsʸ : Ops {σ = σ} X → Ops {σ = σ} (Yon X)
  liftOpsʸ α o x = ηYon (α o (λ a → εYon (x a)))

  lowerOpsʸ : Ops {σ = σ} (Yon X) → Ops {σ = σ} X
  lowerOpsʸ α o x = εYon (α o (λ a → ηYon (x a)))

  lowerLiftOpsʸ : (α : Ops {σ = σ} X) → lowerOpsʸ (liftOpsʸ α) ≡ α
  lowerLiftOpsʸ α = refl

  liftLowerOpsʸ : (α : Ops {σ = σ} (Yon X))
    → liftOpsʸ (lowerOpsʸ α) ≡ α
  liftLowerOpsʸ α = funExt (λ o → funExt (λ x →
    ηεYon (α o (λ a → ηYon (εYon (x a))))
    ∙ cong (α o) (funExt (λ a → ηεYon (x a)))))

-- the argument-forded tower, for the record: it exists, but its three
-- laws are propositions rather than `refl`
module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (ℓX : Level) where

  ALGᴰᶠ : Categoryᴰ (FAM S ℓX) _ _
  ALGᴰᶠ .Categoryᴰ.ob[_] X = Ops {σ = σ} (λ s → ⟨ X s ⟩)
  ALGᴰᶠ .Categoryᴰ.Hom[_][_,_] {x = X} {y = Y} f α β =
    Homᶠ σ {ℓX = ℓX} {X = X} {Y = Y} f α β
  ALGᴰᶠ .Categoryᴰ.idᴰ {x = X} {p = α} = idᶠ σ {X = X} α
  ALGᴰᶠ .Categoryᴰ._⋆ᴰ_ {x = X} {y = Y} {z = Z} {f = f} {g = g}
    {xᴰ = α} {yᴰ = β} {zᴰ = γ} ϕ ψ =
    _⋆ᶠ_ σ {X = X} {Y = Y} {Z = Z} {f = f} {g = g}
      {α = α} {β = β} {γ = γ} ϕ ψ
  ALGᴰᶠ .Categoryᴰ.⋆IdLᴰ {x = X} {y = Y} {f = f} {xᴰ = α} {yᴰ = β} ϕ =
    isPropHomᶠ σ {X = X} {Y = Y} f α β _ _
  ALGᴰᶠ .Categoryᴰ.⋆IdRᴰ {x = X} {y = Y} {f = f} {xᴰ = α} {yᴰ = β} ϕ =
    isPropHomᶠ σ {X = X} {Y = Y} f α β _ _
  ALGᴰᶠ .Categoryᴰ.⋆Assocᴰ {x = X} {y = Y} {z = Z} {w = W}
    {f = f} {g = g} {h = h} {xᴰ = α} {wᴰ = δ} ϕ ψ χ =
    isPropHomᶠ σ {X = X} {Y = W}
      (λ s w → h s (g s (f s w))) α δ _ _
  ALGᴰᶠ .Categoryᴰ.isSetHomᴰ {x = X} {y = Y} {f = f} {xᴰ = α} {yᴰ = β} =
    isProp→isSet (isPropHomᶠ σ {X = X} {Y = Y} f α β)

  ALGᶠ : Category _ _
  ALGᶠ = ∫C ALGᴰᶠ

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (ℓX : Level) where

  EQNSᴰᶠ : Categoryᴰ (ALGᶠ σ ℓX) _ _
  EQNSᴰᶠ .Categoryᴰ.ob[_] (X , α) =
    (e : σeq .eqns) (ρ : (v : σeq .vars e) → ⟨ X (σeq .varSort e v) ⟩)
    → TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .lhs e)
      ≡ TmRec (λ s → ⟨ X s ⟩) α ρ (σeq .rhs e)
  EQNSᴰᶠ .Categoryᴰ.Hom[_][_,_] _ _ _ = Unit* {ℓ-zero}
  EQNSᴰᶠ .Categoryᴰ.idᴰ = tt*
  EQNSᴰᶠ .Categoryᴰ._⋆ᴰ_ _ _ = tt*
  EQNSᴰᶠ .Categoryᴰ.⋆IdLᴰ _ = refl
  EQNSᴰᶠ .Categoryᴰ.⋆IdRᴰ _ = refl
  EQNSᴰᶠ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  EQNSᴰᶠ .Categoryᴰ.isSetHomᴰ = isProp→isSet (λ _ _ → refl)

  MODᴰᶠ : Categoryᴰ (FAM S ℓX) _ _
  MODᴰᶠ = ∫Cᴰ (ALGᴰᶠ σ ℓX) EQNSᴰᶠ

  MODᶠ : Category _ _
  MODᶠ = ∫C MODᴰᶠ

  ModHomᶠ : (M N : Category.ob MODᶠ) → Type _
  ModHomᶠ M N = MODᶠ [ M , N ]

-- the translation `ALGᴰ` <-> `ALGᴰᶠ` on homs
module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (ℓX : Level)
  {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  (α : Ops {σ = σ} (λ s → ⟨ X s ⟩))
  (β : Ops {σ = σ} (λ s → ⟨ Y s ⟩)) where

  isPropHomALG :
    isProp (Categoryᴰ.Hom[_][_,_] (ALGᴰ σ ℓX) {x = X} {y = Y} f α β)
  isPropHomALG = isPropΠ4 (λ o x y _ → Y _ .snd _ _)

  -- forded to unforded: supply `z := f ∘ x` with `refl`.  A plain
  -- application; no path operations.
  unford : Homᶠ σ {ℓX = ℓX} {X = X} {Y = Y} f α β
    → Categoryᴰ.Hom[_][_,_] (ALGᴰ σ ℓX) {x = X} {y = Y} f α β
  unford ϕ o x y eq =
    ϕ o x y (λ a → f (σ .sortOf o a) (x a)) eq (λ a → refl)

  -- unforded to forded: needs the argument rewrite, hence a path
  ford : Categoryᴰ.Hom[_][_,_] (ALGᴰ σ ℓX) {x = X} {y = Y} f α β
    → Homᶠ σ {ℓX = ℓX} {X = X} {Y = Y} f α β
  ford ϕ o x y z eq hz =
    ϕ o x y eq ∙ cong (β o) (funExt (λ a → sym (hz a)))

  -- neither round trip is `refl`: both leave a `_∙ refl`
  fordUnford : (ϕ : Categoryᴰ.Hom[_][_,_] (ALGᴰ σ ℓX)
                     {x = X} {y = Y} f α β)
    → unford (ford ϕ) ≡ ϕ
  fordUnford ϕ = isPropHomALG _ _

  unfordFord : (ϕ : Homᶠ σ {ℓX = ℓX} {X = X} {Y = Y} f α β)
    → ford (unford ϕ) ≡ ϕ
  unfordFord ϕ = isPropHomᶠ σ {X = X} {Y = Y} f α β _ _

-- `unford` preserves composition on the nose, but not the identity
module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (ℓX : Level)
  {X Y Z : S → hSet ℓX}
  (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩) (g : (s : S) → ⟨ Y s ⟩ → ⟨ Z s ⟩)
  (α : Ops {σ = σ} (λ s → ⟨ X s ⟩)) (β : Ops {σ = σ} (λ s → ⟨ Y s ⟩))
  (γ : Ops {σ = σ} (λ s → ⟨ Z s ⟩))
  (ϕ : Homᶠ σ {ℓX = ℓX} {X = X} {Y = Y} f α β)
  (ψ : Homᶠ σ {ℓX = ℓX} {X = Y} {Y = Z} g β γ) where

  unford⋆ :
    unford σ ℓX {X = X} {Y = Z} (λ s w → g s (f s w)) α γ
      (_⋆ᶠ_ σ {X = X} {Y = Y} {Z = Z} {f = f} {g = g}
        {α = α} {β = β} {γ = γ} ϕ ψ)
    ≡ Categoryᴰ._⋆ᴰ_ (ALGᴰ σ ℓX) {x = X} {y = Y} {z = Z} {f = f} {g = g}
        {xᴰ = α} {yᴰ = β} {zᴰ = γ}
        (unford σ ℓX {X = X} {Y = Y} f α β ϕ)
        (unford σ ℓX {X = Y} {Y = Z} g β γ ψ)
  unford⋆ = refl

-- restriction of homomorphism conditions is *strictly* functorial in
-- the signature map: these are the two facts that `Section.MODOVERᴰ`'s
-- laws consume, and there they are only propositional
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {ℓX : Level}
  {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  (β : Ops {σ = σ} (Yon (λ s → ⟨ X s ⟩)))
  (γ : Ops {σ = σ} (Yon (λ s → ⟨ Y s ⟩)))
  (ψ : Categoryᴰ.Hom[_][_,_] (ALGᴰʸ σ ℓX) {x = X} {y = Y} f β γ) where

  resHomCondʸId :
    resHomCondʸ (idSigMapʸ {σ = σ}) {X = X} {Y = Y} f β γ ψ ≡ ψ
  resHomCondʸId = refl

module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  {υ : SortedSig S ℓ3 ℓ3'} {ℓX : Level}
  (F : SigMapʸ σ τ) (G : SigMapʸ τ υ)
  {X Y : S → hSet ℓX} (f : (s : S) → ⟨ X s ⟩ → ⟨ Y s ⟩)
  (β : Ops {σ = υ} (Yon (λ s → ⟨ X s ⟩)))
  (γ : Ops {σ = υ} (Yon (λ s → ⟨ Y s ⟩)))
  (ψ : Categoryᴰ.Hom[_][_,_] (ALGᴰʸ υ ℓX) {x = X} {y = Y} f β γ) where

  resHomCondʸ⋆ :
    resHomCondʸ (F ⋆SigMapʸ G) {X = X} {Y = Y} f β γ ψ
    ≡ resHomCondʸ F {X = X} {Y = Y} f
        (resOpsʸ G (λ s → ⟨ X s ⟩) β) (resOpsʸ G (λ s → ⟨ Y s ⟩) γ)
        (resHomCondʸ G {X = X} {Y = Y} f β γ ψ)
  resHomCondʸ⋆ = refl

-- and the same one level up: `Section.ReindexMod`'s `F-id` and `F-seq`
-- are `Σ≡Prop … refl` there and `refl` here
module _ {S : Type ℓS} {σ : SortedSig S ℓ1 ℓ1'} {τ : SortedSig S ℓ2 ℓ2'}
  (σeq : SortedEqns σ ℓ1'' ℓv) (τeq : SortedEqns τ ℓ2'' ℓw)
  (ℓX : Level) (F : SigMapʸ σ τ)
  (pres : PresEqnsʸ σeq τeq ℓX F) where

  resModObʸ : Category.ob (MODʸ τeq ℓX) → Category.ob (MODʸ σeq ℓX)
  resModObʸ M =
    M .fst
    , resOpsʸ F (λ s → ⟨ M .fst s ⟩) (M .snd .fst)
    , pres (M .fst) (M .snd .fst) (M .snd .snd)

  resModHomʸ : (N P : Category.ob (MODʸ τeq ℓX))
    → ModHomʸ τeq ℓX N P → ModHomʸ σeq ℓX (resModObʸ N) (resModObʸ P)
  resModHomʸ N P ψ =
    ψ .fst
    , resHomCondʸ F {X = N .fst} {Y = P .fst} (ψ .fst)
        (N .snd .fst) (P .snd .fst) (ψ .snd .fst)
    , tt*

  ReindexModʸ : Functor (MODʸ τeq ℓX) (MODʸ σeq ℓX)
  ReindexModʸ .Functor.F-ob = resModObʸ
  ReindexModʸ .Functor.F-hom {x = N} {y = P} = resModHomʸ N P
  ReindexModʸ .Functor.F-id {x = N} = refl
  ReindexModʸ .Functor.F-seq {x = N} {y = P} {z = Q} ψ χ = refl
