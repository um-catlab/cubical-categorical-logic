{-
  The reind normal form, generically.

  For a dependent type B : A → Type, a value of `B a` is represented not
  directly but as a triple

      idx : A          -- where the payload actually lives
      pth : a ≡ idx    -- how the nominal index relates to it
      val : B idx      -- the payload

  Reindexing composes `pth` and leaves `idx` and `val` alone, so no transport
  is ever created and none can nest: an N-fold tower of reinds has, for every
  N, definitionally the same `idx` and `val` as the value it was built from.

  The point is not that each reind is cheaper but that the total-space view

      ∫ x = (x .idx , x .val)  :  Σ A B

  -- which is what this library's equational reasoning already talks about,
  `_∫≡_` in Cubical.Foundations.More.depReasoning being `Path (Σ A B) _ _` --
  is invariant under `reind` definitionally.  A chain step whose only job is
  to cross a reind therefore becomes `refl` and drops out of the chain.

  What is definitional and what is not:

    payload / index preservation, at any tower depth     definitional
    products: projections, pairing, reind commuting      definitional
    sums: injections, case analysis, reind commuting     definitional
    functions (hereditary, Fun₁): formation,
               application, abstraction                  definitional
    functions (family, Fun₂): payload preservation       definitional
    functions: reind-naturality                          propositional
    dependent Σ: the filler                              propositional
    `un` (leaving the normal form at a fixed index)      the one transport

  Both propositional obligations are payload-constant -- they move only the
  `pth` field -- so over an hSet base they are discharged by `RNF≡` in
  `RNFSet` below, once per chain rather than once per crossing.

  Design notes:

  * `_∙ᴿ_` is opaque.  Transparent also works and keeps the collapse
    definitional, but opacity gives a single throttle point should a chain
    ever start nesting hcomps through the record.
  * The record is `no-eta-equality`, and every operation is defined by
    projection rather than by pattern matching: `no-eta-equality` makes
    `reind q (rnf p v) = …` a [SplitOnNonEtaRecord] error, and the `pattern`
    attribute Agda suggests in its place would disable copattern matching for
    the record, which this library depends on everywhere.  Copattern
    definitions into the record are fine; `RNF≡` below uses them.
  * `pth : a ≡ idx` rather than `idx ≡ a`, so that `nf v = rnf refl v` is
    the unit.
  * The hSet-specific equality principle lives in its own module, mirroring
    the existing depReasoning / hSetReasoning split.
  * Functions come in both forms, and they are not freely interderivable:
    crossing costs a transport in either direction, because the two normal
    forms sit at different indices and the argument's payload has to move.
    The hereditary form `Fun₁` is the primary one.
-}

module Cubical.Foundations.ReindNormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level

-- The stored-path algebra: the only constructors allowed for the `pth` field.
--
-- These live at top level rather than inside `module RNF B`, because
-- otherwise every instantiation `RNF B`, `RNF C`, `RNF (λ a → B a ⊎ C a)`
-- would get its own opaque symbol, and a stored path built in one would not
-- be definitionally equal to the same path built in another -- which is
-- exactly the cross-family coherence the algebra is for (`Sums.case-reind`
-- below is the first casualty).
opaque
  _∙ᴿ_ : {A : Type ℓ}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  p ∙ᴿ q = p ∙ q

  ⟨cong⟩ᴿ : {A : Type ℓ}{B : Type ℓ'}(h : A → B){a a' : A}
    → a ≡ a' → h a ≡ h a'
  ⟨cong⟩ᴿ h p = cong h p

  ⟨cong₂⟩ᴿ : {A : Type ℓ}{B : Type ℓ'}{C : Type ℓ''}(h : A → B → C)
    {a a' : A}{b b' : B} → a ≡ a' → b ≡ b' → h a b ≡ h a' b'
  ⟨cong₂⟩ᴿ h p q = cong₂ h p q


module RNF {A : Type ℓ} (B : A → Type ℓ') where

  record ReindNormalForm (a : A) : Type (ℓ-max ℓ ℓ') where
    no-eta-equality
    constructor rnf
    field
      {idx} : A
      pth   : a ≡ idx
      val   : B idx
  open ReindNormalForm public

  -- The total-space view: what the library's equational reasoning sees.
  ∫ : {a : A} → ReindNormalForm a → Σ A B
  ∫ x = x .idx , x .val

  -- by projection, never by pattern matching on the record
  reind : {a a' : A} → a ≡ a' → ReindNormalForm a → ReindNormalForm a'
  reind q x = rnf (sym q ∙ᴿ x .pth) (x .val)

  -- the unit: entering at the nominal index
  nf : {a : A} → B a → ReindNormalForm a
  nf v = rnf refl v

  -- A real transport, for the boundary only: where a value has to be handed
  -- back at a fixed index, a record field say.  Never inside a chain.
  un : {a : A} → ReindNormalForm a → B a
  un x = subst B (sym (x .pth)) (x .val)

  un-filler : {a : A}(x : ReindNormalForm a) → Path (Σ A B) (∫ x) (a , un x)
  un-filler x = ΣPathP (sym (x .pth) , subst-filler B (sym (x .pth)) (x .val))

  un-filler⁻ : {a : A}(x : ReindNormalForm a) → Path (Σ A B) (a , un x) (∫ x)
  un-filler⁻ x = sym (un-filler x)

  -- The invariant, checked.  All of these hold definitionally.
  reind-val : {a a' : A}(q : a ≡ a')(x : ReindNormalForm a)
    → reind q x .val ≡ x .val
  reind-val _ _ = refl

  reind-idx : {a a' : A}(q : a ≡ a')(x : ReindNormalForm a)
    → reind q x .idx ≡ x .idx
  reind-idx _ _ = refl

  reind-∫ : {a a' : A}(q : a ≡ a')(x : ReindNormalForm a) → ∫ (reind q x) ≡ ∫ x
  reind-∫ _ _ = refl

  -- a four-fold tower, and every deeper one, collapses on the nose
  tower : {a b c d e : A}
    (q₁ : a ≡ b)(q₂ : b ≡ c)(q₃ : c ≡ d)(q₄ : d ≡ e)(x : ReindNormalForm a)
    → ∫ (reind q₄ (reind q₃ (reind q₂ (reind q₁ x)))) ≡ ∫ x
  tower _ _ _ _ _ = refl

  nf-val : {a : A}(v : B a) → nf v .val ≡ v
  nf-val _ = refl

  nf-∫ : {a : A}(v : B a) → ∫ (nf v) ≡ (a , v)
  nf-∫ _ = refl

  -- It is a faithful representation (contractibility of singletons).
  Iso-RNF : (a : A) → Iso (ReindNormalForm a) (B a)
  Iso-RNF a = iso un nf sec ret where
    sec : ∀ v → un (nf v) ≡ v
    sec v = transportRefl v
    -- by copattern: there is no pattern matching and no eta to appeal to
    ret : ∀ x → nf (un x) ≡ x
    ret x i .idx = x .pth i
    ret x i .pth j = x .pth (i ∧ j)
    ret x i .val = symP (subst-filler B (sym (x .pth)) (x .val)) i

  ≃-RNF : (a : A) → ReindNormalForm a ≃ B a
  ≃-RNF a = isoToEquiv (Iso-RNF a)

-- The hSet layer: one coherence per chain, not per crossing.

module RNFSet {A : Type ℓ} (isSetA : isSet A) (B : A → Type ℓ') where
  open RNF B public

  RNF≡ : {a : A}{x y : ReindNormalForm a}
    → (ip : x .idx ≡ y .idx)
    → PathP (λ i → B (ip i)) (x .val) (y .val)
    → x ≡ y
  RNF≡ {x = x}{y} ip vp i .idx = ip i
  RNF≡ {x = x}{y} ip vp i .pth =
    isSet→SquareP (λ _ _ → isSetA) (x .pth) (y .pth) refl ip i
  RNF≡ {x = x}{y} ip vp i .val = vp i

  roundtrip : {a a' : A}(q : a ≡ a')(x : ReindNormalForm a)
    → reind (sym q) (reind q x) ≡ x
  roundtrip q x = RNF≡ refl refl

-- Functoriality.  Everything downstream is an instance of these, so no
-- client has to touch `pth` by hand.

module _ {A : Type ℓ}{A' : Type ℓ'}{B : A → Type ℓ''}{B' : A' → Type ℓ'''} where
  private
    module R  = RNF B
    module R' = RNF B'

  -- The payload is mapped directly, with no transport; the stored path
  -- rides along by `cong`.
  mapRNF : (h : A → A') → (∀ {a} → B a → B' (h a))
    → {a : A} → R.ReindNormalForm a → R'.ReindNormalForm (h a)
  mapRNF h g x = R'.rnf (⟨cong⟩ᴿ h (x .R.pth)) (g (x .R.val))

  mapRNF-∫ : (h : A → A')(g : ∀ {a} → B a → B' (h a))
    {a : A}(x : R.ReindNormalForm a)
    → R'.∫ (mapRNF h g x) ≡ (h (x .R.idx) , g (x .R.val))
  mapRNF-∫ _ _ _ = refl

module _ {A : Type ℓ}{A' : Type ℓ'}{A'' : Type ℓ''}
         {B : A → Type ℓ'''}{B' : A' → Type ℓ''''}{B'' : A'' → Type ℓ'''''} where
  private
    module R   = RNF B
    module R'  = RNF B'
    module R'' = RNF B''

  map₂RNF : (h : A → A' → A'') → (∀ {a a'} → B a → B' a' → B'' (h a a'))
    → {a : A}{a' : A'} → R.ReindNormalForm a → R'.ReindNormalForm a'
    → R''.ReindNormalForm (h a a')
  map₂RNF h g x y =
    R''.rnf (⟨cong₂⟩ᴿ h (x .R.pth) (y .R'.pth)) (g (x .R.val) (y .R'.val))

  map₂RNF-∫ : (h : A → A' → A'')(g : ∀ {a a'} → B a → B' a' → B'' (h a a'))
    {a : A}{a' : A'}(x : R.ReindNormalForm a)(y : R'.ReindNormalForm a')
    → R''.∫ (map₂RNF h g x y)
    ≡ (h (x .R.idx) (y .R'.idx) , g (x .R.val) (y .R'.val))
  map₂RNF-∫ _ _ _ _ = refl

-- Products.  One stored path serves the pair, and projections and pairing
-- both commute with reind on the nose.

module Products {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') where
  private
    B×C : A → Type (ℓ-max ℓ' ℓ'')
    B×C a = B a × C a
    module RB  = RNF B
    module RC  = RNF C
    module RBC = RNF B×C

  fstRNF : {a : A} → RBC.ReindNormalForm a → RB.ReindNormalForm a
  fstRNF x = RB.rnf (x .RBC.pth) (x .RBC.val .fst)

  sndRNF : {a : A} → RBC.ReindNormalForm a → RC.ReindNormalForm a
  sndRNF x = RC.rnf (x .RBC.pth) (x .RBC.val .snd)

  pairRNF : {a b : A} → a ≡ b → B b → C b → RBC.ReindNormalForm a
  pairRNF p u v = RBC.rnf p (u , v)

  -- definitional
  fst-reind : {a a' : A}(q : a ≡ a')(x : RBC.ReindNormalForm a)
    → RB.∫ (fstRNF (RBC.reind q x)) ≡ RB.∫ (RB.reind q (fstRNF x))
  fst-reind _ _ = refl

  snd-reind : {a a' : A}(q : a ≡ a')(x : RBC.ReindNormalForm a)
    → RC.∫ (sndRNF (RBC.reind q x)) ≡ RC.∫ (RC.reind q (sndRNF x))
  snd-reind _ _ = refl

  pair-reind : {a a' b : A}(q : a ≡ a')(p : a ≡ b)(u : B b)(v : C b)
    → RBC.∫ (RBC.reind q (pairRNF p u v)) ≡ RBC.∫ (pairRNF p u v)
  pair-reind _ _ _ _ = refl

  -- the componentwise family, closed under reind on the nose
  reind× : {a a' : A} → a ≡ a'
    → RB.ReindNormalForm a × RC.ReindNormalForm a
    → RB.ReindNormalForm a' × RC.ReindNormalForm a'
  reind× q (x , y) = RB.reind q x , RC.reind q y

  split : {a : A} → RBC.ReindNormalForm a
    → RB.ReindNormalForm a × RC.ReindNormalForm a
  split x = fstRNF x , sndRNF x

  split-reind : {a a' : A}(q : a ≡ a')(x : RBC.ReindNormalForm a)
    → (RB.∫ (split (RBC.reind q x) .fst) ≡ RB.∫ (reind× q (split x) .fst))
    × (RC.∫ (split (RBC.reind q x) .snd) ≡ RC.∫ (reind× q (split x) .snd))
  split-reind _ _ = refl , refl

-- Sums.  reind commutes with both injections and with case analysis.

module Sums {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ') where
  private
    B⊎C : A → Type ℓ'
    B⊎C a = B a ⊎ C a
    module RB  = RNF B
    module RC  = RNF C
    module RBC = RNF B⊎C

  inlRNF : {a : A} → RB.ReindNormalForm a → RBC.ReindNormalForm a
  inlRNF x = RBC.rnf (x .RB.pth) (inl (x .RB.val))

  inrRNF : {a : A} → RC.ReindNormalForm a → RBC.ReindNormalForm a
  inrRNF x = RBC.rnf (x .RC.pth) (inr (x .RC.val))

  -- definitional
  inl-reind : {a a' : A}(q : a ≡ a')(x : RB.ReindNormalForm a)
    → RBC.∫ (inlRNF (RB.reind q x)) ≡ RBC.∫ (RBC.reind q (inlRNF x))
  inl-reind _ _ = refl

  inr-reind : {a a' : A}(q : a ≡ a')(x : RC.ReindNormalForm a)
    → RBC.∫ (inrRNF (RC.reind q x)) ≡ RBC.∫ (RBC.reind q (inrRNF x))
  inr-reind _ _ = refl

  -- Case analysis without pattern-matching the record: split on the payload
  -- only, and rebuild each branch with the same stored path.
  module _ {D : Type ℓ''} where
    private
      goRNF : {a i : A}
        → (RB.ReindNormalForm a → D) → (RC.ReindNormalForm a → D)
        → a ≡ i → (B i ⊎ C i) → D
      goRNF f g p (inl u) = f (RB.rnf p u)
      goRNF f g p (inr v) = g (RC.rnf p v)

    caseRNF : {a : A}
      → (RB.ReindNormalForm a → D) → (RC.ReindNormalForm a → D)
      → RBC.ReindNormalForm a → D
    caseRNF f g x = goRNF f g (x .RBC.pth) (x .RBC.val)

    -- definitional in both branches; this is the coherence that fails if
    -- `_∙ᴿ_` is instantiation-local rather than a single shared symbol
    case-reind : {a a' : A}
      (q : a ≡ a')(f : RB.ReindNormalForm a' → D)(g : RC.ReindNormalForm a' → D)
      {i : A}(p : a ≡ i)(w : B i ⊎ C i)
      → caseRNF f g (RBC.reind q (RBC.rnf p w))
      ≡ caseRNF (λ y → f (RB.reind q y)) (λ y → g (RC.reind q y)) (RBC.rnf p w)
    case-reind q f g p (inl u) = refl
    case-reind q f g p (inr v) = refl

-- Functions, in both forms; the hereditary one is primary.

module Functions {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') where
  private
    module RB = RNF B
    module RC = RNF C
  module RBC = RNF (λ a → B a → C a)

  -- Transporting a function between raw families generates two substs, one
  -- of them contravariant, and they nest.
  reind→raw : {a a' : A} → a ≡ a' → (B a → C a) → (B a' → C a')
  reind→raw q f x = subst C q (f (subst B (sym q) x))

  -- The hereditary form, and the primary one: a function between normal
  -- forms.  Both directions are stored-path composition, with no subst in
  -- either variance.
  Fun₁ : A → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Fun₁ a = RB.ReindNormalForm a → RC.ReindNormalForm a

  reind→ : {a a' : A} → a ≡ a' → Fun₁ a → Fun₁ a'
  reind→ q f x = RC.reind q (f (RB.reind (sym q) x))

  -- application: transport-free
  app₁ : {a : A} → Fun₁ a → RB.ReindNormalForm a → RC.ReindNormalForm a
  app₁ f x = f x

  -- abstraction: the body sees the stored path and the payload, neither
  -- of them moved
  lam₁ : {a : A} → ({i : A} → a ≡ i → B i → RC.ReindNormalForm a) → Fun₁ a
  lam₁ g x = g (x .RB.pth) (x .RB.val)

  lam-app : {a : A}(g : {i : A} → a ≡ i → B i → RC.ReindNormalForm a)
    (x : RB.ReindNormalForm a)
    → app₁ (lam₁ g) x ≡ g (x .RB.pth) (x .RB.val)
  lam-app _ _ = refl                                       -- definitional

  app-reind-∫ : {a a' : A}(q : a ≡ a')(f : Fun₁ a)(x : RB.ReindNormalForm a)
    → RC.∫ (RC.reind q (app₁ f x)) ≡ RC.∫ (app₁ f x)
  app-reind-∫ _ _ _ = refl                                 -- definitional

  -- The family form: a normal form of a function family, for when a function
  -- family genuinely is the thing being reindexed.
  Fun₂ : A → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  Fun₂ = RBC.ReindNormalForm

  reind₂ : {a a' : A} → a ≡ a' → Fun₂ a → Fun₂ a'
  reind₂ = RBC.reind

  reind₂-val : {a a' : A}(q : a ≡ a')(f : Fun₂ a)
    → reind₂ q f .RBC.val ≡ f .RBC.val
  reind₂-val _ _ = refl                                    -- definitional

  -- The crossing between the two forms is a transport boundary, named here
  -- so that it is not performed by accident inside a chain: the two normal
  -- forms sit at different indices, so the argument's payload has to be
  -- moved through `un`.
  crossing-2→1 : {a : A} → Fun₂ a → Fun₁ a
  crossing-2→1 g x = RC.nf (RBC.un g (RB.un x))

  crossing-1→2 : {a : A} → Fun₁ a → Fun₂ a
  crossing-1→2 f = RBC.nf (λ v → RC.un (f (RB.nf v)))

-- Dependent Σ: the one former that needs a filler.  It is supplied here so
-- that callers never write it, and it is payload-constant -- `idx` and `val`
-- are constant along it and only `pth` moves.  Contrast `subst-filler`,
-- which must compute a transport under the motive.

module DepSigma {A : Type ℓ} (B : A → Type ℓ') where
  open RNF B

  opaque
    unfolding _∙ᴿ_

    reind-filler : {a a' : A}(q : a ≡ a')(x : ReindNormalForm a)
      → Path (Σ A ReindNormalForm) (a , x) (a' , reind q x)
    reind-filler q x i .fst = q i
    reind-filler q x i .snd .idx = x .idx
    reind-filler q x i .snd .val = x .val
    reind-filler q x i .snd .pth j = compPath-filler' (sym q) (x .pth) i j
    -- `idx` and `val` are constant along this filler, as the clauses above
    -- show; only `pth` moves.  That constancy cannot be stated as a `refl`
    -- lemma here, since with `no-eta-equality` Agda cannot project through
    -- `reind-filler q x i .snd` outside a clause head.
