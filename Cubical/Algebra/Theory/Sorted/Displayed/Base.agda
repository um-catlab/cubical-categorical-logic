-- Displayed models of a many-sorted theory, with displayed SORTS, and
-- the global elimination principle for the free model.
module Cubical.Algebra.Theory.Sorted.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; var; node; Ops; TmRec;
         MOD; ModHom)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓXᴰ ℓSᴰ ℓi : Level

open SortedSig
open SortedEqns

-- ------------------------------------------------------------------
-- Displayed signatures
-- ------------------------------------------------------------------

record SortedSigᴰ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓSᴰ ℓi
  : Type (ℓ-max (ℓ-max ℓS ℓ)
          (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓSᴰ) (ℓ-suc ℓi)))) where
  field
    Sortᴰ : S → Type ℓSᴰ
    opIdxᴰ : σ .ops → Type ℓi
    argSortᴰ : (o : σ .ops) → opIdxᴰ o
      → (a : σ .arities o) → Sortᴰ (σ .sortOf o a)
    resSortᴰ : (o : σ .ops) → opIdxᴰ o → Sortᴰ (σ .resultSort o)

open SortedSigᴰ

-- ------------------------------------------------------------------
-- Displayed terms, forded displayed operations
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) where

  data Tmᴰ {V : Type ℓv} {vs : V → S} (vsᴰ : (v : V) → σᴰ .Sortᴰ (vs v))
    : {s : S} → σᴰ .Sortᴰ s → Tm σ V vs s
    → Type (ℓ-max (ℓ-max ℓS ℓ)
            (ℓ-max (ℓ-max ℓ' ℓv) (ℓ-max ℓSᴰ ℓi))) where
    varᴰ : (v : V) → Tmᴰ vsᴰ (vsᴰ v) (var v)
    nodeᴰ : (o : σ .ops) (i : σᴰ .opIdxᴰ o)
      (ts : (a : σ .arities o) → Tm σ V vs (σ .sortOf o a))
      → ((a : σ .arities o) → Tmᴰ vsᴰ (σᴰ .argSortᴰ o i a) (ts a))
      → Tmᴰ vsᴰ (σᴰ .resSortᴰ o i) (node o ts)

  -- The displayed operations, FORDED in the result exactly as `ALGᴰ`'s
  -- homomorphism condition is: the result `y` is taken free together
  -- with `y ≡ α o x`.  This is what makes the displayed homomorphism
  -- condition below a plain path rather than a `PathP`, and hence what
  -- makes the displayed category strict.
  Opsᶠᴰ : {ℓX ℓXᴰ : Level} (X : S → Type ℓX) (α : Ops {σ = σ} X)
    (Xᴰ : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ) → Type _
  Opsᶠᴰ X α Xᴰ = (o : σ .ops) (i : σᴰ .opIdxᴰ o)
    (x : (a : σ .arities o) → X (σ .sortOf o a))
    (xᴰ : (a : σ .arities o)
        → Xᴰ (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a))
    (y : X (σ .resultSort o)) → y ≡ α o x
    → Xᴰ (σ .resultSort o) (σᴰ .resSortᴰ o i) y

  module _ {X : S → Type ℓX} {α : Ops {σ = σ} X}
    {Xᴰ : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ} where

    -- discharging the ford is an application, not a transport
    unfordᴰ : Opsᶠᴰ X α Xᴰ
      → (o : σ .ops) (i : σᴰ .opIdxᴰ o)
        (x : (a : σ .arities o) → X (σ .sortOf o a))
      → ((a : σ .arities o)
         → Xᴰ (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a))
      → Xᴰ (σ .resultSort o) (σᴰ .resSortᴰ o i) (α o x)
    unfordᴰ αᴰ o i x xᴰ = αᴰ o i x xᴰ (α o x) refl

  TmRecᴰ : {ℓX ℓXᴰ : Level} (X : S → Type ℓX) (α : Ops {σ = σ} X)
    (Xᴰ : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ) (αᴰ : Opsᶠᴰ X α Xᴰ)
    {V : Type ℓv} {vs : V → S} {vsᴰ : (v : V) → σᴰ .Sortᴰ (vs v)}
    {ρ : (v : V) → X (vs v)}
    (ρᴰ : (v : V) → Xᴰ (vs v) (vsᴰ v) (ρ v))
    {s : S} {sᴰ : σᴰ .Sortᴰ s} {N : Tm σ V vs s}
    (Nᴰ : Tmᴰ vsᴰ sᴰ N) → Xᴰ s sᴰ (TmRec X α ρ N)
  TmRecᴰ X α Xᴰ αᴰ ρᴰ (varᴰ v) = ρᴰ v
  TmRecᴰ X α Xᴰ αᴰ ρᴰ (nodeᴰ o i ts tsᴰ) =
    unfordᴰ {X = X} {α = α} {Xᴰ = Xᴰ} αᴰ o i _
      (λ a → TmRecᴰ X α Xᴰ αᴰ ρᴰ (tsᴰ a))

  -- --------------------------------------------------------------
  -- Sections of a displayed signature
  -- --------------------------------------------------------------
  --
  -- A choice of displayed sort for every sort, together with a choice
  -- of index for every operation making that choice coherent.  This is
  -- what splits the sort projection; without it the total model lives
  -- over `Σ S Sortᴰ` and there is no `ModHom` down to `M` at all.
  record Sectionᴰ
    : Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' (ℓ-max ℓSᴰ ℓi))) where
    field
      secSort : (s : S) → σᴰ .Sortᴰ s
      secIdx : (o : σ .ops) → σᴰ .opIdxᴰ o
      secArg : (o : σ .ops) (a : σ .arities o)
        → σᴰ .argSortᴰ o (secIdx o) a Eq.≡ secSort (σ .sortOf o a)
      secRes : (o : σ .ops)
        → σᴰ .resSortᴰ o (secIdx o) Eq.≡ secSort (σ .resultSort o)

  open Sectionᴰ

  -- every term has a displayed typing derivation along a section.  In
  -- an instance the coherences are `Eq.refl` and these transports are
  -- the identity function on the nose.
  secTm : (sec : Sectionᴰ) {V : Type ℓv} {vs : V → S} {s : S}
    (N : Tm σ V vs s)
    → Tmᴰ (λ v → sec .secSort (vs v)) (sec .secSort s) N
  secTm sec (var v) = varᴰ v
  secTm sec {vs = vs} (node o ts) =
    Eq.transport (λ t → Tmᴰ (λ v → sec .secSort (vs v)) t (node o ts))
      (sec .secRes o)
      (nodeᴰ o (sec .secIdx o) ts
        (λ a → Eq.transport
                 (λ t → Tmᴰ (λ v → sec .secSort (vs v)) t (ts a))
                 (Eq.sym (sec .secArg o a)) (secTm sec (ts a))))

-- ------------------------------------------------------------------
-- Displayed models
-- ------------------------------------------------------------------

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (M : Category.ob (MOD σeq ℓX))
  (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) (ℓXᴰ : Level) where

  private
    X : S → Type ℓX
    X s = ⟨ M .fst s ⟩

    α = M .snd .fst
    sat = M .snd .snd

  record Modelᴰˢ
    : Type (ℓ-max (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' ℓ''))
            (ℓ-max (ℓ-max ℓv ℓSᴰ)
             (ℓ-max ℓi (ℓ-max ℓX (ℓ-suc ℓXᴰ))))) where
    field
      carrierᴰ : (s : S) → σᴰ .Sortᴰ s → X s → hSet ℓXᴰ

    Xᴰ : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ
    Xᴰ s sᴰ x = ⟨ carrierᴰ s sᴰ x ⟩

    field
      opsᴰ : Opsᶠᴰ σᴰ X α Xᴰ
      -- the displayed equation, quantified over all displayed typings
      -- of the two sides at a common displayed sort
      satᴰ : (e : σeq .eqns)
        (vsᴰ : (v : σeq .vars e) → σᴰ .Sortᴰ (σeq .varSort e v))
        (sᴰ : σᴰ .Sortᴰ (σeq .eqnSort e))
        (L : Tmᴰ σᴰ vsᴰ sᴰ (σeq .lhs e)) (R : Tmᴰ σᴰ vsᴰ sᴰ (σeq .rhs e))
        (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
        (ρᴰ : (v : σeq .vars e) → Xᴰ (σeq .varSort e v) (vsᴰ v) (ρ v))
        → PathP (λ i → Xᴰ (σeq .eqnSort e) sᴰ (sat e ρ i))
            (TmRecᴰ σᴰ X α Xᴰ opsᴰ ρᴰ L)
            (TmRecᴰ σᴰ X α Xᴰ opsᴰ ρᴰ R)

open Modelᴰˢ

-- ------------------------------------------------------------------
-- Displayed models form a displayed category over `MOD`, STRICTLY
-- ------------------------------------------------------------------
--
-- A displayed homomorphism over `h` is a map of displayed carriers
-- together with a forded displayed operation condition, whose
-- hypothesis is exactly the *conclusion* of the previous factor.  That
-- is the chain that makes `⋆IdLᴰ`, `⋆IdRᴰ` and `⋆Assocᴰ` `refl`; it is
-- also why `opsᴰ` had to be forded, since with an unforded `opsᴰ` the
-- conclusion is a `PathP` over the base homomorphism condition and
-- nothing chains.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) {ℓXᴰ : Level} where

  FamHomᴰ : {M N : Category.ob (MOD σeq ℓX)}
    (f : (s : S) → ⟨ M .fst s ⟩ → ⟨ N .fst s ⟩)
    (Mᴰ : Modelᴰˢ σeq M σᴰ ℓXᴰ) (Nᴰ : Modelᴰˢ σeq N σᴰ ℓXᴰ) → Type _
  FamHomᴰ {M = M} f Mᴰ Nᴰ =
    (s : S) (sᴰ : σᴰ .Sortᴰ s) (x : ⟨ M .fst s ⟩)
    → ⟨ Mᴰ .carrierᴰ s sᴰ x ⟩ → ⟨ Nᴰ .carrierᴰ s sᴰ (f s x) ⟩

  OpsHomᴰ : {M N : Category.ob (MOD σeq ℓX)} (h : ModHom σeq ℓX M N)
    (Mᴰ : Modelᴰˢ σeq M σᴰ ℓXᴰ) (Nᴰ : Modelᴰˢ σeq N σᴰ ℓXᴰ)
    (fᴰ : FamHomᴰ {M = M} {N = N} (h .fst) Mᴰ Nᴰ) → Type _
  OpsHomᴰ {M = M} {N = N} h Mᴰ Nᴰ fᴰ =
    (o : σ .ops) (i : σᴰ .opIdxᴰ o)
    (x : (a : σ .arities o) → ⟨ M .fst (σ .sortOf o a) ⟩)
    (xᴰ : (a : σ .arities o)
        → ⟨ Mᴰ .carrierᴰ (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a) ⟩)
    (y : ⟨ M .fst (σ .resultSort o) ⟩) (eq : y ≡ M .snd .fst o x)
    (yᴰ : ⟨ Mᴰ .carrierᴰ (σ .resultSort o) (σᴰ .resSortᴰ o i) y ⟩)
    → yᴰ ≡ Mᴰ .opsᴰ o i x xᴰ y eq
    → fᴰ (σ .resultSort o) (σᴰ .resSortᴰ o i) y yᴰ
      ≡ Nᴰ .opsᴰ o i (λ a → h .fst (σ .sortOf o a) (x a))
          (λ a → fᴰ (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a) (xᴰ a))
          (h .fst (σ .resultSort o) y) (h .snd .fst o x y eq)

  MODᴰᴰ : Categoryᴰ (MOD σeq ℓX) _ _
  MODᴰᴰ .Categoryᴰ.ob[_] M = Modelᴰˢ σeq M σᴰ ℓXᴰ
  MODᴰᴰ .Categoryᴰ.Hom[_][_,_] {x = M} {y = N} h Mᴰ Nᴰ =
    Σ[ fᴰ ∈ FamHomᴰ {M = M} {N = N} (h .fst) Mᴰ Nᴰ ]
      OpsHomᴰ {M = M} {N = N} h Mᴰ Nᴰ fᴰ
  MODᴰᴰ .Categoryᴰ.idᴰ =
    (λ s sᴰ x xᴰ → xᴰ) , (λ o i x xᴰ y eq yᴰ hyp → hyp)
  MODᴰᴰ .Categoryᴰ._⋆ᴰ_ {f = h} {g = k} ϕ ψ =
    (λ s sᴰ x xᴰ → ψ .fst s sᴰ (h .fst s x) (ϕ .fst s sᴰ x xᴰ))
    , (λ o i x xᴰ y eq yᴰ hyp →
        ψ .snd o i (λ a → h .fst (σ .sortOf o a) (x a))
          (λ a → ϕ .fst (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a) (xᴰ a))
          (h .fst (σ .resultSort o) y) (h .snd .fst o x y eq)
          (ϕ .fst (σ .resultSort o) (σᴰ .resSortᴰ o i) y yᴰ)
          (ϕ .snd o i x xᴰ y eq yᴰ hyp))
  MODᴰᴰ .Categoryᴰ.⋆IdLᴰ ϕ = refl
  MODᴰᴰ .Categoryᴰ.⋆IdRᴰ ϕ = refl
  MODᴰᴰ .Categoryᴰ.⋆Assocᴰ ϕ ψ χ = refl
  MODᴰᴰ .Categoryᴰ.isSetHomᴰ {yᴰ = Nᴰ} =
    isSetΣ
      (isSetΠ3 (λ s sᴰ x → isSetΠ (λ _ → Nᴰ .carrierᴰ s sᴰ _ .snd)))
      (λ _ → isProp→isSet
        (isPropΠ5 (λ o i x xᴰ y → isPropΠ (λ eq → isPropΠ (λ yᴰ →
          isPropΠ (λ _ → Nᴰ .carrierᴰ _ _ _ .snd _ _))))))

open Sectionᴰ

-- ------------------------------------------------------------------
-- The total model along a section, and its projection
-- ------------------------------------------------------------------
--
-- With displayed sorts the total model lives over `Σ S Sortᴰ`, so it is
-- a model of a *different* theory and the projection is not a
-- `ModHom`.  A `Sectionᴰ` splits the sort projection coherently with
-- the operations, and restricting along it lands back in `MOD σeq`.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (M : Category.ob (MOD σeq ℓX))
  (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) (Mᴰ : Modelᴰˢ σeq M σᴰ ℓX)
  (sec : Sectionᴰ σᴰ) where

  private
    X : S → Type ℓX
    X s = ⟨ M .fst s ⟩

    α = M .snd .fst
    sat = M .snd .snd

    Fibᴰ : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓX
    Fibᴰ s sᴰ x = ⟨ Mᴰ .carrierᴰ s sᴰ x ⟩

    -- the unforded displayed operations, which is what `TmRecᴰ` uses
    uop : (o : σ .ops) (i : σᴰ .opIdxᴰ o)
      (x : (a : σ .arities o) → X (σ .sortOf o a))
      → ((a : σ .arities o)
         → Fibᴰ (σ .sortOf o a) (σᴰ .argSortᴰ o i a) (x a))
      → Fibᴰ (σ .resultSort o) (σᴰ .resSortᴰ o i) (α o x)
    uop = unfordᴰ σᴰ {X = X} {α = α} {Xᴰ = Fibᴰ} (Mᴰ .opsᴰ)

    coeᴰ : {s : S} {sᴰ sᴰ' : σᴰ .Sortᴰ s} → sᴰ Eq.≡ sᴰ' → {x : X s}
      → Fibᴰ s sᴰ x → Fibᴰ s sᴰ' x
    coeᴰ {s = s} p {x = x} = Eq.transport (λ t → Fibᴰ s t x) p

    ∫X : S → hSet ℓX
    ∫X s = (Σ[ x ∈ X s ] Fibᴰ s (sec .secSort s) x)
           , isSetΣ (M .fst s .snd)
               (λ x → Mᴰ .carrierᴰ s (sec .secSort s) x .snd)

    ∫α : Ops {σ = σ} (λ s → ⟨ ∫X s ⟩)
    ∫α o x =
      α o (λ a → x a .fst)
      , coeᴰ (sec .secRes o)
          (uop o (sec .secIdx o) (λ a → x a .fst)
            (λ a → coeᴰ (Eq.sym (sec .secArg o a)) (x a .snd)))

    TmRecᴰ-Eq : {V : Type ℓv} {vs : V → S}
      {vsᴰ : (v : V) → σᴰ .Sortᴰ (vs v)} {ρ : (v : V) → X (vs v)}
      (ρᴰ : (v : V) → Fibᴰ (vs v) (vsᴰ v) (ρ v))
      {s : S} {sᴰ sᴰ' : σᴰ .Sortᴰ s} (p : sᴰ Eq.≡ sᴰ')
      {N : Tm σ V vs s} (Nᴰ : Tmᴰ σᴰ vsᴰ sᴰ N)
      → TmRecᴰ σᴰ X α Fibᴰ (Mᴰ .opsᴰ) ρᴰ
          (Eq.transport (λ t → Tmᴰ σᴰ vsᴰ t N) p Nᴰ)
        ≡ coeᴰ p (TmRecᴰ σᴰ X α Fibᴰ (Mᴰ .opsᴰ) ρᴰ Nᴰ)
    TmRecᴰ-Eq ρᴰ Eq.refl Nᴰ = refl

    TmRec∫ : {V : Type ℓv} {vs : V → S}
      (ρ : (v : V) → ⟨ ∫X (vs v) ⟩) {s : S} (N : Tm σ V vs s)
      → TmRec (λ s' → ⟨ ∫X s' ⟩) ∫α ρ N
        ≡ ( TmRec X α (λ v → ρ v .fst) N
          , TmRecᴰ σᴰ X α Fibᴰ (Mᴰ .opsᴰ) (λ v → ρ v .snd) (secTm σᴰ sec N) )
    TmRec∫ ρ (var v) = refl
    TmRec∫ ρ (node o ts) =
      cong (∫α o) (funExt (λ a → TmRec∫ ρ (ts a)))
      ∙ ΣPathP (refl , sym
          ( TmRecᴰ-Eq (λ v → ρ v .snd) (sec .secRes o) _
          ∙ cong (coeᴰ (sec .secRes o))
              (cong (uop o (sec .secIdx o) _)
                (funExt (λ a →
                  TmRecᴰ-Eq (λ v → ρ v .snd) (Eq.sym (sec .secArg o a))
                    (secTm σᴰ sec (ts a)))))))

  ∫Mod : Category.ob (MOD σeq ℓX)
  ∫Mod = ∫X , ∫α , λ e ρ →
    TmRec∫ ρ (σeq .lhs e)
    ∙ ΣPathP (sat e _
             , Mᴰ .satᴰ e _ _
                 (secTm σᴰ sec (σeq .lhs e)) (secTm σᴰ sec (σeq .rhs e))
                 _ _)
    ∙ sym (TmRec∫ ρ (σeq .rhs e))

  ∫π : ModHom σeq ℓX ∫Mod M
  ∫π = (λ _ → fst) , (λ o x y eq → cong fst eq) , tt*

  -- A section of the displayed model over the chosen sort section is a
  -- splitting of `∫π`.  The square is a path in a hom set, so nothing
  -- here is a `PathP`.
  Splitting : Type _
  Splitting =
    Σ[ k ∈ ModHom σeq ℓX M ∫Mod ]
      Category._⋆_ (MOD σeq ℓX) {x = M} {y = ∫Mod} {z = M} k ∫π
      ≡ Category.id (MOD σeq ℓX) {x = M}

-- ------------------------------------------------------------------
-- The sort-less notion of displayed model is the case `Sortᴰ s = Unit`
-- ------------------------------------------------------------------
--
-- Nothing is lost by displaying the sorts: `UnitSigᴰ` is the displayed
-- signature with one displayed sort and one index per operation, and
-- `Modelᴰˢ σeq M UnitSigᴰ` is then a family over the carrier only.  The
-- point of the general case is that `MODᴰᴰ` there has
-- `ob[ M ] = Modelᴰˢ σeq M UnitSigᴰ` whose displayed *sorts* are
-- trivial, so a displayed model cannot choose an object over a vertex.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  UnitSigᴰ : SortedSigᴰ σ ℓ-zero ℓ-zero
  UnitSigᴰ .Sortᴰ _ = Unit
  UnitSigᴰ .opIdxᴰ _ = Unit
  UnitSigᴰ .argSortᴰ _ _ _ = tt
  UnitSigᴰ .resSortᴰ _ _ = tt

  UnitSection : Sectionᴰ UnitSigᴰ
  UnitSection .secSort _ = tt
  UnitSection .secIdx _ = tt
  UnitSection .secArg _ _ = Eq.refl
  UnitSection .secRes _ = Eq.refl
