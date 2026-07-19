-- First-order unification as Löb induction over thinnings
--
-- McBride, "First-order unification by structural recursion" (JFP 2003)
-- https://doi.org/10.1017/S0956796803004957
module Cubical.Categories.Direct.Examples.Unification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Maybe as Maybe
  using (Maybe ; just ; nothing ; isOfHLevelMaybe)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_≤_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Thinnings
import Cubical.Categories.Direct.StrictDownset as SD

module Unify (A : Type) (isSetA : isSet A) where
  private
    dir = ThinDirect A isSetA

  open DirectNotation dir using (_≺_)

  private
    variable
      xs ys zs : List A

  data Tm (xs : List A) : Type where
    var  : Var xs → Tm xs
    leaf : Tm xs
    fork : Tm xs → Tm xs → Tm xs

  private
    Cover : Tm xs → Tm xs → Type
    Cover (var x)    (var y)    = x ≡ y
    Cover leaf       leaf       = Unit
    Cover (fork s t) (fork u v) = Cover s u × Cover t v
    Cover _          _          = ⊥

    reflCover : (t : Tm xs) → Cover t t
    reflCover (var x)    = refl
    reflCover leaf       = tt
    reflCover (fork s t) = reflCover s , reflCover t

    encode : {t u : Tm xs} → t ≡ u → Cover t u
    encode {t = t} e = subst (Cover t) e (reflCover t)

    decode : (t u : Tm xs) → Cover t u → t ≡ u
    decode (var x)    (var y)    e        = cong var e
    decode (var x)    leaf       c        = ⊥.rec c
    decode (var x)    (fork u v) c        = ⊥.rec c
    decode leaf       (var y)    c        = ⊥.rec c
    decode leaf       leaf       _        = refl
    decode leaf       (fork u v) c        = ⊥.rec c
    decode (fork s t) (var y)    c        = ⊥.rec c
    decode (fork s t) leaf       c        = ⊥.rec c
    decode (fork s t) (fork u v) (c , c') =
      cong₂ fork (decode s u c) (decode t v c')

    decode-refl : (t : Tm xs) → decode t t (reflCover t) ≡ refl
    decode-refl (var x)    = refl
    decode-refl leaf       = refl
    decode-refl (fork s t) =
      λ i → cong₂ fork (decode-refl s i) (decode-refl t i)

    decode-encode : {t u : Tm xs} (e : t ≡ u) → decode _ _ (encode e) ≡ e
    decode-encode {t = t} =
      J (λ u e → decode t u (encode e) ≡ e)
        (cong (decode t t) (substRefl {B = Cover t} (reflCover t))
         ∙ decode-refl t)

    isPropCover : (t u : Tm xs) → isProp (Cover t u)
    isPropCover {xs} (var x) (var y) = isSetVar xs x y
    isPropCover (var x)    leaf       = ⊥.isProp⊥
    isPropCover (var x)    (fork u v) = ⊥.isProp⊥
    isPropCover leaf       (var y)    = ⊥.isProp⊥
    isPropCover leaf       leaf       = isPropUnit
    isPropCover leaf       (fork u v) = ⊥.isProp⊥
    isPropCover (fork s t) (var y)    = ⊥.isProp⊥
    isPropCover (fork s t) leaf       = ⊥.isProp⊥
    isPropCover (fork s t) (fork u v) =
      isProp× (isPropCover s u) (isPropCover t v)

  isSetTm : isSet (Tm xs)
  isSetTm t u =
    isOfHLevelRetract 1 encode (decode t u) decode-encode (isPropCover t u)

  private
    map2Maybe : {X Y Z : Type} → (X → Y → Z) → Maybe X → Maybe Y → Maybe Z
    map2Maybe f (just x) (just y) = just (f x y)
    map2Maybe f (just x) nothing  = nothing
    map2Maybe f nothing  _        = nothing

  check : (x : Var xs) → Tm xs → Maybe (Tm (delete xs x))
  check x (var y)    = Sum.rec (λ _ → nothing) (λ y' → just (var y'))
                               (thick x y)
  check x leaf       = just leaf
  check x (fork s t) = map2Maybe fork (check x s) (check x t)

  bind : (Var xs → Tm ys) → Tm xs → Tm ys
  bind f (var y)    = f y
  bind f leaf       = leaf
  bind f (fork s t) = fork (bind f s) (bind f t)

  for : (x : Var xs) → Tm (delete xs x) → Var xs → Tm (delete xs x)
  for x t y = Sum.rec (λ _ → t) var (thick x y)

  subst1 : (x : Var xs) → Tm (delete xs x) → Tm xs → Tm (delete xs x)
  subst1 x t = bind (for x t)

  Steps : ℕ → List A → List A → Type
  Steps zero    xs ys = xs Eq.≡ ys
  Steps (suc n) xs ys =
    Σ[ x ∈ Var xs ] Tm (delete xs x) × Steps n (delete xs x) ys

  AList : List A → List A → Type
  AList xs ys = Σ[ n ∈ ℕ ] Steps n xs ys

  isSetSteps : ∀ n (xs ys : List A) → isSet (Steps n xs ys)
  isSetSteps zero    xs ys = isProp→isSet (isPropEqList isSetA xs ys)
  isSetSteps (suc n) xs ys = isSetΣ (isSetVar xs) λ x →
    isSet× isSetTm (isSetSteps n (delete xs x) ys)

  isSetAList : isSet (AList xs ys)
  isSetAList = isSetΣ isSetℕ λ n → isSetSteps n _ _

  applySteps : ∀ {n} → Steps n xs ys → Tm xs → Tm ys
  applySteps {n = zero}  Eq.refl     t = t
  applySteps {n = suc n} (x , u , σ) t = applySteps σ (subst1 x u t)

  applyA : AList xs ys → Tm xs → Tm ys
  applyA (n , σ) = applySteps σ

  appendSteps : ∀ {m n} → Steps m xs ys → Steps n ys zs → Steps (m + n) xs zs
  appendSteps {m = zero}  Eq.refl     τ = τ
  appendSteps {m = suc m} (x , u , σ) τ = x , u , appendSteps σ τ

  _⋆A_ : AList xs ys → AList ys zs → AList xs zs
  (m , σ) ⋆A (n , τ) = m + n , appendSteps σ τ

  stepsThin : ∀ {n} → Steps n xs ys → Thin ys xs
  stepsThin {n = zero}  Eq.refl     = idThin _
  stepsThin {n = suc n} (x , u , σ) = seqThin (stepsThin σ) (faceThin x)

  alistThin : AList xs ys → Thin ys xs
  alistThin (n , σ) = stepsThin σ

  steps-strict : ∀ {n} → Steps (suc n) xs ys → ys ≺ xs
  steps-strict {xs = xs} {ys = ys} (x , u , σ) =
    subst (λ k → suc (length ys) ≤ k) (length-delete xs x)
          (thin-length (stepsThin σ))

  Result : List A → Type
  Result xs = Maybe (Σ[ ys ∈ List A ] AList xs ys)

  isSetResult : ∀ xs → isSet (Result xs)
  isSetResult xs = isOfHLevelMaybe 0
    (isSetΣ (isOfHLevelList 0 isSetA) λ ys → isSetAList)

  M : List A → hSet ℓ-zero
  M xs = (Tm xs → Tm xs → Result xs) , isSetΠ2 λ _ _ → isSetResult xs

  unifyStep : ∀ xs → ⟨ SD.▷Fam dir {ℓF = ℓ-zero} M xs ⟩ → ⟨ M xs ⟩
  unifyStep xs β = go
    where
      recur : AList xs ys → ys ≺ xs → Tm ys → Tm ys → Result ys
      recur σ q = SD.▷FamApp dir {ℓF = ℓ-zero} M β (alistThin σ) q

      noop : Result xs
      noop = just (xs , 0 , Eq.refl)

      solve : (x : Var xs) → Tm (delete xs x) → Result xs
      solve x t = just (delete xs x , 1 , x , t , Eq.refl)

      flexRigid : Var xs → Tm xs → Result xs
      flexRigid x t = Maybe.rec nothing (solve x) (check x t)

      flexFlex : Var xs → Var xs → Result xs
      flexFlex x y = Sum.rec (λ _ → noop) (λ y' → solve x (var y'))
                             (thick x y)

      go : Tm xs → Tm xs → Result xs
      go (var x)      (var y)      = flexFlex x y
      go (var x)      t            = flexRigid x t
      go t            (var y)      = flexRigid y t
      go leaf         leaf         = noop
      go leaf         (fork _ _)   = nothing
      go (fork _ _)   leaf         = nothing
      go (fork s₁ t₁) (fork s₂ t₂) = afterL (go s₁ s₂)
        where
          afterL : Result xs → Result xs
          afterL nothing                     = nothing
          afterL (just (_ , zero , Eq.refl)) = go t₁ t₂
          afterL (just (ys , suc n , σ))     =
            afterR (recur (suc n , σ) (steps-strict σ)
                      (applySteps σ t₁) (applySteps σ t₂))
            where
              afterR : Result ys → Result xs
              afterR nothing         = nothing
              afterR (just (zs , τ)) = just (zs , (suc n , σ) ⋆A τ)

  -- unification through Löb induction on thinnings
  unify : ∀ xs → Tm xs → Tm xs → Result xs
  unify = SD.löbFam dir {ℓF = ℓ-zero} M unifyStep

private module U = Unify ℕ isSetℕ

private
  ex why : ℕ
  ex = 0
  why = 1

  -- A scope of two unknowns
  sc : List ℕ
  sc = ex ∷ why ∷ []

  -- Two variables x and y
  x y : Var sc
  x = vz
  y = vs vz

  -- unify t = (x , leaf) with u = (leaf , y)
  t u : U.Tm sc
  t = U.fork (U.var x) U.leaf
  u = U.fork U.leaf (U.var y)

  -- Assign x and y both to leaf
  σ : U.AList sc []
  σ = 2 , x , U.leaf , vz , U.leaf , Eq.refl

-- t and u can be unified by the assignment σ
_ : U.unify sc t u ≡ just ([] , σ)
_ = refl

_ : U.applyA σ t ≡ U.applyA σ u
_ = refl

-- unifying a variable with itself needs no substitution at all
_ : U.unify sc (U.var x) (U.var x) ≡ just (sc , 0 , Eq.refl)
_ = refl

-- A term cannot unify with a pair containing itself
_ : U.unify sc (U.var x) (U.fork (U.var x) U.leaf) ≡ nothing
_ = refl

-- leaf is not a fork
_ : U.unify sc U.leaf (U.fork U.leaf U.leaf) ≡ nothing
_ = refl
