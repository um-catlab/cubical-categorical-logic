-- `MODᴰᴰ` is a fibration: reindexing a displayed model along a
-- homomorphism of models.
--
-- This is the workhorse of the whole development.  A displayed model is
-- a logical predicate; reindexing one along `h : M → N` is how every
-- logical relation, gluing construction and canonicity argument in this
-- library is supposed to arise -- never by writing the predicate's
-- fields out by hand.
--
-- Reindexing the carrier and the operations is TRANSPORT-FREE, exactly
-- because `opsᴰ` is forded: the forded homomorphism condition slots
-- straight into the forded operation's `y`/`eq` slot.  Only `satᴰ`
-- costs a transport argument, and it is a proposition.
--
-- The cartesian property is then degenerate:
-- `MODᴰᴰ [ g ⋆ hom ][ Lᴰ , Nᴰ ]` and `MODᴰᴰ [ g ][ Lᴰ , reindexMod ]`
-- are definitionally the SAME type and `_⋆ᴰ cartπ` is the identity
-- function, so every component of the universal property is `refl`.
module Cubical.Algebra.Theory.Sorted.Displayed.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; var; node; Ops; TmRec; MOD;
         ModHom)
open import Cubical.Algebra.Theory.Sorted.Displayed.Base
  using (SortedSigᴰ; Tmᴰ; varᴰ; nodeᴰ; Modelᴰˢ; MODᴰᴰ; UnitSigᴰ;
         Opsᶠᴰ; TmRecᴰ; unfordᴰ)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓXᴰ ℓSᴰ ℓi : Level

open SortedSig
open SortedEqns
open SortedSigᴰ
open Modelᴰˢ

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (σᴰ : SortedSigᴰ σ ℓSᴰ ℓi) {ℓXᴰ : Level}
  {M N : Category.ob (MOD σeq ℓX)} (hom : ModHom σeq ℓX M N)
  (Nᴰ : Modelᴰˢ σeq N σᴰ ℓXᴰ) where

  private
    X : S → Type ℓX
    X s = ⟨ M .fst s ⟩

    Yb : S → Type ℓX
    Yb s = ⟨ N .fst s ⟩

    αM = M .snd .fst
    αN = N .snd .fst
    satM = M .snd .snd

    f : (s : S) → X s → Yb s
    f = hom .fst

    ϕ : (o : σ .ops) (x : (a : σ .arities o) → X (σ .sortOf o a))
        (y : X (σ .resultSort o)) → y ≡ αM o x
      → f (σ .resultSort o) y ≡ αN o (λ a → f (σ .sortOf o a) (x a))
    ϕ = hom .snd .fst

    Xᴰ* : (s : S) → σᴰ .Sortᴰ s → X s → Type ℓXᴰ
    Xᴰ* s sᴰ x = Xᴰ Nᴰ s sᴰ (f s x)

    -- The point of the ford: no `subst`, no `PathP`.  `Nᴰ .opsᴰ`
    -- accepts `f _ y` presented via the homomorphism condition.
    ops* : Opsᶠᴰ σᴰ X αM Xᴰ*
    ops* o i x xᴰ y eq =
      Nᴰ .opsᴰ o i (λ a → f (σ .sortOf o a) (x a)) xᴰ
        (f (σ .resultSort o) y) (ϕ o x y eq)

    -- `Σ[ z ] (z ≡ c)` is contractible: any two presentations of a
    -- forded result are connected.
    isContrCoSingl : {A : Type ℓX} (c : A) → isContr (Σ[ z ∈ A ] (z ≡ c))
    isContrCoSingl c .fst = c , refl
    isContrCoSingl c .snd (z , p) i = p (~ i) , λ j → p (~ i ∨ j)

    TmRecHom : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v))
      {s : S} (t : Tm σ V vs s)
      → f s (TmRec X αM ρ t) ≡ TmRec Yb αN (λ v → f (vs v) (ρ v)) t
    TmRecHom ρ (var v) = refl
    TmRecHom ρ (node o ts) =
      ϕ o _ _ refl ∙ cong (αN o) (funExt (λ a → TmRecHom ρ (ts a)))

    TmRecHomᴰ : {V : Type ℓv} {vs : V → S}
      {vsᴰ : (v : V) → σᴰ .Sortᴰ (vs v)} {ρ : (v : V) → X (vs v)}
      (ρᴰ : (v : V) → Xᴰ* (vs v) (vsᴰ v) (ρ v))
      {s : S} {sᴰ : σᴰ .Sortᴰ s} {t : Tm σ V vs s}
      (tᴰ : Tmᴰ σᴰ vsᴰ sᴰ t)
      → PathP (λ i → Xᴰ Nᴰ s sᴰ (TmRecHom ρ t i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ tᴰ)
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ tᴰ)
    TmRecHomᴰ ρᴰ (varᴰ v) = refl
    TmRecHomᴰ {vs = vs} {ρ = ρ} ρᴰ (nodeᴰ o oi ts tsᴰ) =
      subst
        (λ p → PathP
          (λ i → Xᴰ Nᴰ (σ .resultSort o) (σᴰ .resSortᴰ o oi) (p i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ (nodeᴰ o oi ts tsᴰ))
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ (nodeᴰ o oi ts tsᴰ)))
        fix inner
      where
        x : (a : σ .arities o) → X (σ .sortOf o a)
        x a = TmRec X αM ρ (ts a)

        x'' : (a : σ .arities o) → Yb (σ .sortOf o a)
        x'' a = TmRec Yb αN (λ v → f (vs v) (ρ v)) (ts a)

        xp : (λ a → f (σ .sortOf o a) (x a)) ≡ x''
        xp = funExt (λ a → TmRecHom ρ (ts a))

        yp : PathP
               (λ i → Σ[ z ∈ Yb (σ .resultSort o) ] (z ≡ αN o (xp i)))
               (f (σ .resultSort o) (αM o x) , ϕ o x (αM o x) refl)
               (αN o x'' , refl)
        yp = isProp→PathP (λ i → isContr→isProp (isContrCoSingl _)) _ _

        inner : PathP
          (λ i → Xᴰ Nᴰ (σ .resultSort o) (σᴰ .resSortᴰ o oi) (yp i .fst))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ (nodeᴰ o oi ts tsᴰ))
          (TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ)
            {ρ = λ v → f (vs v) (ρ v)} ρᴰ (nodeᴰ o oi ts tsᴰ))
        inner i =
          Nᴰ .opsᴰ o oi (xp i) (λ a → TmRecHomᴰ ρᴰ (tsᴰ a) i)
            (yp i .fst) (yp i .snd)

        fix : (λ i → yp i .fst) ≡ TmRecHom ρ (node o ts)
        fix = N .fst (σ .resultSort o) .snd _ _ _ _

    sat* : (e : σeq .eqns)
      (vsᴰ : (v : σeq .vars e) → σᴰ .Sortᴰ (σeq .varSort e v))
      (sᴰ : σᴰ .Sortᴰ (σeq .eqnSort e))
      (L : Tmᴰ σᴰ vsᴰ sᴰ (σeq .lhs e)) (R : Tmᴰ σᴰ vsᴰ sᴰ (σeq .rhs e))
      (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
      (ρᴰ : (v : σeq .vars e) → Xᴰ* (σeq .varSort e v) (vsᴰ v) (ρ v))
      → PathP (λ i → Xᴰ* (σeq .eqnSort e) sᴰ (satM e ρ i))
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ L)
          (TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ R)
    sat* e vsᴰ sᴰ L R ρ ρᴰ = toPathP
      ( cong (λ p → subst B p L') basefix
      ∙ substComposite B u (v ∙ sym w) L'
      ∙ cong (subst B (v ∙ sym w)) (fromPathP (TmRecHomᴰ ρᴰ L))
      ∙ substComposite B v (sym w) L''
      ∙ cong (subst B (sym w))
          (fromPathP (Nᴰ .satᴰ e vsᴰ sᴰ L R fρ ρᴰ))
      ∙ cong (subst B (sym w)) (sym (fromPathP (TmRecHomᴰ ρᴰ R)))
      ∙ subst⁻Subst B w R' )
      where
        sE : S
        sE = σeq .eqnSort e

        B : Yb sE → Type ℓXᴰ
        B = Xᴰ Nᴰ sE sᴰ

        fρ : (v : σeq .vars e) → Yb (σeq .varSort e v)
        fρ v = f (σeq .varSort e v) (ρ v)

        L' = TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ L
        R' = TmRecᴰ σᴰ X αM Xᴰ* ops* ρᴰ R
        L'' = TmRecᴰ σᴰ Yb αN (Xᴰ Nᴰ) (Nᴰ .opsᴰ) {ρ = fρ} ρᴰ L

        u = TmRecHom ρ (σeq .lhs e)
        v = N .snd .snd e fρ
        w = TmRecHom ρ (σeq .rhs e)

        basefix : cong (f sE) (satM e ρ) ≡ u ∙ (v ∙ sym w)
        basefix = N .fst sE .snd _ _ _ _

  reindexMod : Modelᴰˢ σeq M σᴰ ℓXᴰ
  reindexMod .carrierᴰ s sᴰ x = Nᴰ .carrierᴰ s sᴰ (f s x)
  reindexMod .opsᴰ = ops*
  reindexMod .satᴰ = sat*

  private
    MODᴰᴰ' : Categoryᴰ (MOD σeq ℓX) _ _
    MODᴰᴰ' = MODᴰᴰ σeq {ℓX = ℓX} σᴰ {ℓXᴰ = ℓXᴰ}

  cartπ : MODᴰᴰ' [ hom ][ reindexMod , Nᴰ ]
  cartπ = (λ s sᴰ x xᴰ → xᴰ) , (λ o i x xᴰ y eq yᴰ hyp → hyp)

  cartβ : {L : Category.ob (MOD σeq ℓX)} {Lᴰ : Modelᴰˢ σeq L σᴰ ℓXᴰ}
    (g : ModHom σeq ℓX L M) (gᴰ : MODᴰᴰ' [ g ][ Lᴰ , reindexMod ])
    → Categoryᴰ._⋆ᴰ_ MODᴰᴰ' {f = g} {g = hom}
        {xᴰ = Lᴰ} {yᴰ = reindexMod} {zᴰ = Nᴰ} gᴰ cartπ
      ≡ gᴰ
  cartβ g gᴰ = refl

  -- Cartesianness: post-composition with `cartπ` is the IDENTITY
  -- function, and the two hom types it goes between are definitionally
  -- equal.  So `MODᴰᴰ` is a fibration, and every component of the
  -- universal property is `refl`.
  cartIso : {L : Category.ob (MOD σeq ℓX)} {Lᴰ : Modelᴰˢ σeq L σᴰ ℓXᴰ}
    (g : ModHom σeq ℓX L M)
    → Iso (MODᴰᴰ' [ g ][ Lᴰ , reindexMod ])
          (MODᴰᴰ' [ Category._⋆_ (MOD σeq ℓX) {x = L} {y = M} {z = N}
                      g hom ][ Lᴰ , Nᴰ ])
  cartIso {Lᴰ = Lᴰ} g .Iso.fun gᴰ =
    Categoryᴰ._⋆ᴰ_ MODᴰᴰ' {f = g} {g = hom}
      {xᴰ = Lᴰ} {yᴰ = reindexMod} {zᴰ = Nᴰ} gᴰ cartπ
  cartIso g .Iso.inv k = k
  cartIso g .Iso.sec _ = refl
  cartIso g .Iso.ret _ = refl
