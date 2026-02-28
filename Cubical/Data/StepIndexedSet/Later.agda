{-

  Later modality on ω+Sets

  The later modality ▷ shifts the indexing:
    (▷X)₀ = Unit*, (▷X)ₙ₊₁ = Xₙ
  The limit is unchanged: (▷X)ω = Xω.

  This gives an endofunctor ▷ on ω+SET, together with a
  natural transformation next : Id ⟹ ▷.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Data.StepIndexedSet.Later where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding

open import Cubical.Data.Nat
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Unit.Properties
  using (isSetUnit*)
open import Cubical.Data.StepIndexedSet
open import Cubical.Data.StepIndexedSet.CartesianClosedCategory

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base

open Category
open Functor
open NatTrans
open ω+Type
open ω+Hom
open ωType
open ωHom
open ωChain

private
  variable
    ℓ : Level

-- ▷ on ωTypes: shift the chain by one
▷-ωType : ωType ℓ → ωType ℓ
▷-ωType X .Xᵢ zero = Unit*
▷-ωType X .Xᵢ (suc n) = X .Xᵢ n
▷-ωType X .πᵢ zero _ = tt*
▷-ωType X .πᵢ (suc n) = X .πᵢ n

isωSet-▷ : {X : ωType ℓ}
  → isωSet X → isωSet (▷-ωType X)
isωSet-▷ Xset zero = isSetUnit*
isωSet-▷ Xset (suc n) = Xset n

-- Shifting chains back and forth
shiftChain : {X : ωType ℓ}
  → ωChain (▷-ωType X) → ωChain X
shiftChain c .xᵢ n = c .xᵢ (suc n)
shiftChain c .xᵢ-nat n = c .xᵢ-nat (suc n)

unshiftChain : {X : ωType ℓ}
  → ωChain X → ωChain (▷-ωType X)
unshiftChain c .xᵢ zero = tt*
unshiftChain c .xᵢ (suc n) = c .xᵢ n
unshiftChain c .xᵢ-nat zero = refl
unshiftChain c .xᵢ-nat (suc n) = c .xᵢ-nat n

-- ▷ on ω+Types
▷-ω+Type : ω+Type ℓ → ω+Type ℓ
▷-ω+Type X .Xfin = ▷-ωType (X .Xfin)
▷-ω+Type X .Xω = X .Xω
▷-ω+Type X .π x = unshiftChain (X .π x)
▷-ω+Type X .isLimit =
  snd (compEquiv (X .π , X .isLimit)
    (isoToEquiv chainShiftIso))
  where
    chainShiftIso :
      Iso (ωChain (X .Xfin))
          (ωChain (▷-ωType (X .Xfin)))
    chainShiftIso .Iso.fun = unshiftChain
    chainShiftIso .Iso.inv = shiftChain
    chainShiftIso .Iso.ret c = refl
    chainShiftIso .Iso.sec c i .xᵢ zero =
      tt*
    chainShiftIso .Iso.sec c i .xᵢ (suc n) =
      c .xᵢ (suc n)
    chainShiftIso .Iso.sec c i .xᵢ-nat zero =
      isSetUnit* _ _
        refl (c .xᵢ-nat zero) i
    chainShiftIso .Iso.sec c i .xᵢ-nat
      (suc n) = c .xᵢ-nat (suc n)

-- ▷ on ωHoms
▷-ωHom : {X Y : ωType ℓ}
  → ωHom X Y → ωHom (▷-ωType X) (▷-ωType Y)
▷-ωHom f .fᵢ zero _ = tt*
▷-ωHom f .fᵢ (suc n) = f .fᵢ n
▷-ωHom f .fᵢ-nat zero _ = refl
▷-ωHom f .fᵢ-nat (suc n) = f .fᵢ-nat n

-- ▷ on ω+Homs
▷-ω+Hom : {X Y : ω+Type ℓ}
  → ω+Hom X Y
  → ω+Hom (▷-ω+Type X) (▷-ω+Type Y)
▷-ω+Hom {X = X} {Y = Y} f = h where
  module F = ω+Hom f
  h : ω+Hom (▷-ω+Type X) (▷-ω+Type Y)
  h .ω+Hom.fFin = ▷-ωHom F.fFin
  h .ω+Hom.fω = F.fω
  h .ω+Hom.fω-nat zero x = refl
  h .ω+Hom.fω-nat (suc n) = F.fω-nat n

-- ▷ as an endofunctor on ω+SET
▷ : Functor (ω+SET ℓ) (ω+SET ℓ)
▷ .F-ob (X , Xset) =
  ▷-ω+Type X , isωSet-▷ Xset
▷ .F-hom = ▷-ω+Hom
▷ .F-id {x = _ , Xset} =
  makeω+HomPath (isωSet-▷ Xset)
    (funExt λ { zero → funExt (λ _ → refl)
              ; (suc n) → refl })
▷ .F-seq {z = _ , Zset} f g =
  makeω+HomPath (isωSet-▷ Zset)
    (funExt λ { zero → funExt (λ _ → refl)
              ; (suc n) → refl })

-- next on ωTypes (apply restriction once)
next-ωHom : (X : ωType ℓ)
  → ωHom X (▷-ωType X)
next-ωHom X .fᵢ zero _ = tt*
next-ωHom X .fᵢ (suc n) = X .πᵢ n
next-ωHom X .fᵢ-nat zero _ = refl
next-ωHom X .fᵢ-nat (suc n) x = refl

-- next on ω+Types
next-ω+Hom : (X : ω+Type ℓ)
  → ω+Hom X (▷-ω+Type X)
next-ω+Hom X .ω+Hom.fFin =
  next-ωHom (X .Xfin)
next-ω+Hom X .ω+Hom.fω x = x
next-ω+Hom X .ω+Hom.fω-nat zero x = refl
next-ω+Hom X .ω+Hom.fω-nat (suc n) x =
  sym (X .π x .xᵢ-nat n)

-- next as a natural transformation Id ⟹ ▷
next : NatTrans (Id {C = ω+SET ℓ}) ▷
next .N-ob X+ =
  next-ω+Hom (X+ .fst)
next .N-hom {x = X+} {y = Y+} f =
  makeω+HomPath (isωSet-▷ (Y+ .snd))
    (funExt λ { zero → funExt (λ _ → refl)
              ; (suc n) → funExt λ x →
                  F.fᵢ-nat n x })
  where module F = ω+Hom f

-- Guarded fixed point operator
-- Given f : ▷X → X, iterate to build a chain and take
-- its limit.
module _ {X : ω+Type ℓ} where
  private module X = ω+Type X

  -- Build the chain by iteration:
  --   x₀ = f 0 tt*
  --   xₙ₊₁ = f (suc n) xₙ
  gfix-iter : ω+Hom (▷-ω+Type X) X
    → (n : ℕ) → X.Xᵢ n
  gfix-iter f zero =
    f .ω+Hom.fFin .fᵢ 0 tt*
  gfix-iter f (suc n) =
    f .ω+Hom.fFin .fᵢ (suc n)
      (gfix-iter f n)

  gfix-iter-nat : (f : ω+Hom (▷-ω+Type X) X)
    → ∀ n
    → X.πᵢ n (gfix-iter f (suc n))
      ≡ gfix-iter f n
  gfix-iter-nat f zero =
    f .ω+Hom.fFin .fᵢ-nat 0
      (gfix-iter f 0)
  gfix-iter-nat f (suc n) =
    f .ω+Hom.fFin .fᵢ-nat (suc n)
      (gfix-iter f (suc n))
    ∙ cong (f .ω+Hom.fFin .fᵢ (suc n))
        (gfix-iter-nat f n)

  gfix-chain : ω+Hom (▷-ω+Type X) X
    → ωChain X.Xfin
  gfix-chain f .xᵢ = gfix-iter f
  gfix-chain f .xᵢ-nat = gfix-iter-nat f

  gfix : ω+Hom (▷-ω+Type X) X → X.Xω
  gfix f = invIsEq X.isLimit (gfix-chain f)

  -- Fixed point equation: f (gfix f) ≡ gfix f
  gfix-eq : isωSet X.Xfin
    → (f : ω+Hom (▷-ω+Type X) X)
    → f .ω+Hom.fω (gfix f) ≡ gfix f
  gfix-eq Xset f =
    isEmbedding→Inj
      {f = X.π}
      (isEquiv→isEmbedding X.isLimit) _ _
      (makeωChainPath {X = X} {Y = X}
        Xset
        (funExt (pointwise f)))
    where
      module F = ω+Hom f
      sec : (g : ω+Hom (▷-ω+Type X) X)
        → X.π (gfix g) ≡ gfix-chain g
      sec g =
        secIsEq X.isLimit (gfix-chain g)

      pointwise : (g : ω+Hom (▷-ω+Type X) X)
        → ∀ i
        → X.π (g .ω+Hom.fω (gfix g)) .xᵢ i
        ≡ X.π (gfix g) .xᵢ i
      pointwise g i =
        g .ω+Hom.fω-nat i (gfix g)
        ∙ cong (λ c →
            g .ω+Hom.fFin .fᵢ i
              (unshiftChain c .xᵢ i))
            (sec g)
        ∙ step₂ i
        where
          step₂ : ∀ j
            → g .ω+Hom.fFin .fᵢ j
                (unshiftChain
                  (gfix-chain g) .xᵢ j)
            ≡ X.π (gfix g) .xᵢ j
          step₂ zero =
            cong (λ c → c .xᵢ zero)
              (sym (sec g))
          step₂ (suc n) =
            cong (λ c → c .xᵢ (suc n))
              (sym (sec g))

  -- gfix as an ω+Hom from the exponential [▷X, X] to X
  --
  -- At finite level n, given a truncated natural
  -- transformation (▷X)ᵢ → Xᵢ for i ≤ n, we iterate
  -- to produce an element of Xₙ.
  gfix-iter≤ : (Xset : isωSet X.Xfin)
    → (n : ℕ)
    → ωHom≤ (▷-ωType X.Xfin) X.Xfin n
    → X.Xᵢ n
  gfix-iter≤ Xset zero h = h tt*
  gfix-iter≤ Xset (suc n) (rest , f , _) =
    f (gfix-iter≤ Xset n rest)

  -- Helper: topωHom≤ applied to the restriction of
  -- gfix-iter≤ returns gfix-iter≤ itself.
  -- This is needed because the naturality condition
  -- in ωHom≤ relates f to topωHom≤ of the restriction,
  -- not directly to gfix-iter≤.
  top-gfix : (Xset : isωSet X.Xfin)
    → (n : ℕ)
    → (h : ωHom≤ (▷-ωType X.Xfin) X.Xfin n)
    → topωHom≤ (▷-ωType X.Xfin) X.Xfin n h
        (▷-ωType X.Xfin .πᵢ n
          (gfix-iter≤ Xset n h))
      ≡ gfix-iter≤ Xset n h
  top-gfix Xset zero h = refl
  top-gfix Xset (suc m) (rest , f , nat) =
    cong f
      (nat (gfix-iter≤ Xset m rest)
      ∙ top-gfix Xset m rest)

  gfix-iter≤-nat :
    (Xset : isωSet X.Xfin)
    → (n : ℕ)
    → (h : ωHom≤ (▷-ωType X.Xfin) X.Xfin
              (suc n))
    → X.πᵢ n
        (gfix-iter≤ Xset (suc n) h)
      ≡ gfix-iter≤ Xset n
          (restrictωHom≤
            (▷-ωType X.Xfin) X.Xfin n h)
  gfix-iter≤-nat Xset n
    (rest , f , nat) =
    nat (gfix-iter≤ Xset n rest)
    ∙ top-gfix Xset n rest

  -- gfix-iter agrees with gfix-iter≤ on truncated homs
  gfix-iter≡iter≤ :
    (Xset : isωSet X.Xfin)
    → (f : ω+Hom (▷-ω+Type X) X)
    → ∀ n
    → gfix-iter f n
      ≡ gfix-iter≤ Xset n
          (truncωHom (▷-ωType X.Xfin) X.Xfin
            (f .ω+Hom.fFin) n)
  gfix-iter≡iter≤ Xset f zero = refl
  gfix-iter≡iter≤ Xset f (suc n) =
    cong (f .ω+Hom.fFin .fᵢ (suc n))
      (gfix-iter≡iter≤ Xset f n)

  gfix-ω+Hom :
    (Xset : isωSet X.Xfin)
    → ω+Hom (Exp-ω+Type (▷-ω+Type X) X Xset) X
  gfix-ω+Hom Xset .ω+Hom.fFin .fᵢ =
    gfix-iter≤ Xset
  gfix-ω+Hom Xset .ω+Hom.fFin .fᵢ-nat =
    gfix-iter≤-nat Xset
  gfix-ω+Hom Xset .ω+Hom.fω = gfix
  gfix-ω+Hom Xset .ω+Hom.fω-nat n f =
    cong (λ c → c .xᵢ n)
      (secIsEq X.isLimit (gfix-chain f))
    ∙ gfix-iter≡iter≤ Xset f n
