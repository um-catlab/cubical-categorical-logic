{-

  Displayed ω-types and ω+types.

  A displayed ωType over X consists of dependent types Xᵢᴰ over
  each Xᵢ, with dependent restriction maps πᵢᴰ lying over πᵢ.

  A displayed ω+Type additionally has a displayed limit type Xωᴰ
  and a displayed projection πᴰ lying over π, with a fiberwise
  equivalence condition (isEquivOver).

-}
module Cubical.Data.StepIndexedSet.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.StepIndexedSet.Base

open ωType
open ωHom
open ωChain
open ω+Type
open ω+Hom

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Displayed ωType over X: dependent types with dependent
-- restriction maps.
record ωTypeᴰ (X : ωType ℓ) (ℓ' : Level) :
    Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    Xᵢᴰ : ∀ n → X .Xᵢ n → Type ℓ'
    πᵢᴰ : ∀ n {x} → Xᵢᴰ (suc n) x
      → Xᵢᴰ n (X .πᵢ n x)

-- Displayed ωChain over a chain c in X: dependent elements
-- with naturality over the chain compatibility.
record ωChainᴰ {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ')
    (c : ωChain X) : Type ℓ' where
  open ωTypeᴰ Xᴰ
  field
    xᵢᴰ : ∀ i → Xᵢᴰ i (c .xᵢ i)
    xᵢ-natᴰ : ∀ i →
      PathP (λ j → Xᵢᴰ i (c .xᵢ-nat i j))
        (πᵢᴰ i (xᵢᴰ (suc i)))
        (xᵢᴰ i)

-- Dependent sum ωType: ΣωType Xᴰ bundles a displayed
-- ωType into a plain ωType over Σ-types.
ΣωType : {X : ωType ℓ} → ωTypeᴰ X ℓ' → ωType (ℓ-max ℓ ℓ')
ΣωType {X = X} Xᴰ .Xᵢ n =
  Σ[ x ∈ X .Xᵢ n ] Xᴰ .ωTypeᴰ.Xᵢᴰ n x
ΣωType {X = X} Xᴰ .πᵢ n (x , xᴰ) =
  X .πᵢ n x , Xᴰ .ωTypeᴰ.πᵢᴰ n xᴰ

-- Displayed ωHom over f : ωHom X Y, between displayed
-- ωTypes Xᴰ over X and Yᴰ over Y.
record ωHomᴰ {X : ωType ℓ} {Y : ωType ℓ'}
    (Xᴰ : ωTypeᴰ X ℓ'') (Yᴰ : ωTypeᴰ Y ℓ'')
    (f : ωHom X Y) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  open ωTypeᴰ Xᴰ renaming (Xᵢᴰ to Xᵢᴰ; πᵢᴰ to πᵢᴰX)
  open ωTypeᴰ Yᴰ renaming (Xᵢᴰ to Yᵢᴰ; πᵢᴰ to πᵢᴰY)
  field
    fᵢᴰ : ∀ i {x} → Xᵢᴰ i x → Yᵢᴰ i (f .fᵢ i x)
    fᵢ-natᴰ : ∀ n {x} (xᴰ : Xᵢᴰ (suc n) x) →
      PathP (λ j → Yᵢᴰ n (f .fᵢ-nat n x j))
        (πᵢᴰY n (fᵢᴰ (suc n) xᴰ))
        (fᵢᴰ n (πᵢᴰX n xᴰ))

-- Section of a displayed ωType Xᴰ along f : ωHom Y X.
record ωSectionᴰ {X : ωType ℓ} {Y : ωType ℓ'}
    (Xᴰ : ωTypeᴰ X ℓ'') (f : ωHom Y X) :
    Type (ℓ-max ℓ' ℓ'') where
  open ωTypeᴰ Xᴰ
  field
    sᵢ : ∀ n (y : Y .Xᵢ n) → Xᵢᴰ n (f .fᵢ n y)
    sᵢ-nat : ∀ n y →
      PathP (λ j → Xᵢᴰ n (f .fᵢ-nat n y j))
        (πᵢᴰ n (sᵢ (suc n) y))
        (sᵢ n (Y .πᵢ n y))

-- Dependent sum ωChain: bundle a displayed chain into a
-- plain chain over the sum ωType.
ΣωChain : {X : ωType ℓ} {Xᴰ : ωTypeᴰ X ℓ'}
  {c : ωChain X} → ωChainᴰ Xᴰ c → ωChain (ΣωType Xᴰ)
ΣωChain {c = c} cᴰ .xᵢ i =
  c .xᵢ i , cᴰ .ωChainᴰ.xᵢᴰ i
ΣωChain {c = c} cᴰ .xᵢ-nat i j =
  c .xᵢ-nat i j , cᴰ .ωChainᴰ.xᵢ-natᴰ i j

-- Displayed ω+Type over X: displayed finite part, displayed
-- limit type, displayed projection, fiberwise equivalence.
record ω+Typeᴰ (X : ω+Type ℓ) (ℓ' : Level) :
    Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    Xfinᴰ : ωTypeᴰ (X .Xfin) ℓ'
  open ωTypeᴰ Xfinᴰ public
  field
    Xωᴰ : X .Xω → Type ℓ'
    πᴰ : ∀ x → Xωᴰ x → ωChainᴰ Xfinᴰ (X .π x)
    isLimitᴰ : isEquivOver
      {Q = ωChainᴰ Xfinᴰ} πᴰ

-- Displayed ω+Hom over f : ω+Hom X Y, between displayed
-- ω+Types Xᴰ over X and Yᴰ over Y.
record ω+Homᴰ {X : ω+Type ℓ} {Y : ω+Type ℓ'}
    (Xᴰ : ω+Typeᴰ X ℓ'') (Yᴰ : ω+Typeᴰ Y ℓ'')
    (f : ω+Hom X Y) :
    Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  private
    module Xᴰ = ω+Typeᴰ Xᴰ
    module Yᴰ = ω+Typeᴰ Yᴰ
  field
    fFinᴰ : ωHomᴰ Xᴰ.Xfinᴰ Yᴰ.Xfinᴰ (f .fFin)
  open ωHomᴰ fFinᴰ public
  field
    fωᴰ : ∀ {x} → Xᴰ.Xωᴰ x → Yᴰ.Xωᴰ (f .fω x)
    fω-natᴰ : ∀ i {x} (xᴰ : Xᴰ.Xωᴰ x) →
      PathP
        (λ j → Yᴰ.Xᵢᴰ i (f .fω-nat i x j))
        (Yᴰ.πᴰ (f .fω x) (fωᴰ xᴰ)
          .ωChainᴰ.xᵢᴰ i)
        (fᵢᴰ i (Xᴰ.πᴰ x xᴰ .ωChainᴰ.xᵢᴰ i))

-- Section of a displayed ω+Type Xᴰ along
-- f : ω+Hom Y X.
record ω+Sectionᴰ {X : ω+Type ℓ} {Y : ω+Type ℓ'}
    (Xᴰ : ω+Typeᴰ X ℓ'') (f : ω+Hom Y X) :
    Type (ℓ-max ℓ' ℓ'') where
  private
    module Xᴰ = ω+Typeᴰ Xᴰ
  field
    sFinᴰ : ωSectionᴰ Xᴰ.Xfinᴰ (f .fFin)
  open ωSectionᴰ sFinᴰ public
  field
    sωᴰ : ∀ y → Xᴰ.Xωᴰ (f .fω y)
    sω-natᴰ : ∀ i y →
      PathP
        (λ j → Xᴰ.Xᵢᴰ i (f .fω-nat i y j))
        (Xᴰ.πᴰ (f .fω y) (sωᴰ y)
          .ωChainᴰ.xᵢᴰ i)
        (sᵢ i (Y .π y .xᵢ i))

-- Iso between Σ (ωChain X) (ωChainᴰ Xᴰ) and
-- ωChain (ΣωType Xᴰ)
ΣωChainIso : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ')
  → Iso (Σ[ c ∈ ωChain X ] ωChainᴰ Xᴰ c)
        (ωChain (ΣωType Xᴰ))
ΣωChainIso Xᴰ .Iso.fun (c , cᴰ) = ΣωChain cᴰ
ΣωChainIso {X = X} Xᴰ .Iso.inv cΣ .fst .xᵢ i =
  cΣ .xᵢ i .fst
ΣωChainIso {X = X} Xᴰ .Iso.inv cΣ .fst .xᵢ-nat i =
  cong fst (cΣ .xᵢ-nat i)
ΣωChainIso {X = X} Xᴰ .Iso.inv cΣ .snd
  .ωChainᴰ.xᵢᴰ i = cΣ .xᵢ i .snd
ΣωChainIso {X = X} Xᴰ .Iso.inv cΣ .snd
  .ωChainᴰ.xᵢ-natᴰ i =
  cong snd (cΣ .xᵢ-nat i)
ΣωChainIso Xᴰ .Iso.ret _ = refl
ΣωChainIso Xᴰ .Iso.sec _ = refl

-- Dependent sum ω+Type: bundle displayed ω+Type into a
-- plain ω+Type.
Σω+Type : {X : ω+Type ℓ} → ω+Typeᴰ X ℓ'
  → ω+Type (ℓ-max ℓ ℓ')
Σω+Type {X = X} Xᴰ .Xfin = ΣωType (Xᴰ .ω+Typeᴰ.Xfinᴰ)
Σω+Type {X = X} Xᴰ .Xω =
  Σ[ x ∈ X .Xω ] Xᴰ .ω+Typeᴰ.Xωᴰ x
Σω+Type {X = X} Xᴰ .π (x , xᴰ) =
  ΣωChain (Xᴰ .ω+Typeᴰ.πᴰ x xᴰ)
Σω+Type {X = X} Xᴰ .isLimit =
  compEquiv
    (Σ-cong-equiv
      (X .π , X .isLimit)
      (λ x → Xᴰ .ω+Typeᴰ.πᴰ x ,
              Xᴰ .ω+Typeᴰ.isLimitᴰ x))
    (isoToEquiv (ΣωChainIso (Xᴰ .ω+Typeᴰ.Xfinᴰ)))
    .snd

-- Projection: ΣωType Xᴰ → X
ΣωType-fst : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ')
  → ωHom (ΣωType Xᴰ) X
ΣωType-fst Xᴰ .fᵢ _ = fst
ΣωType-fst Xᴰ .fᵢ-nat _ _ = refl

-- Projection: Σω+Type Xᴰ → X
Σω+Type-fst : {X : ω+Type ℓ} (Xᴰ : ω+Typeᴰ X ℓ')
  → ω+Hom (Σω+Type Xᴰ) X
Σω+Type-fst Xᴰ .fFin = ΣωType-fst _
Σω+Type-fst Xᴰ .fω = fst
Σω+Type-fst Xᴰ .fω-nat _ _ = refl

-- Second projection: section of Xᴰ along ΣωType-fst.
ΣωType-snd : {X : ωType ℓ} (Xᴰ : ωTypeᴰ X ℓ')
  → ωSectionᴰ Xᴰ (ΣωType-fst Xᴰ)
ΣωType-snd Xᴰ .ωSectionᴰ.sᵢ _ = snd
ΣωType-snd Xᴰ .ωSectionᴰ.sᵢ-nat _ _ = refl

-- Second projection: section of Xᴰ along Σω+Type-fst.
Σω+Type-snd : {X : ω+Type ℓ} (Xᴰ : ω+Typeᴰ X ℓ')
  → ω+Sectionᴰ Xᴰ (Σω+Type-fst Xᴰ)
Σω+Type-snd Xᴰ .ω+Sectionᴰ.sFinᴰ =
  ΣωType-snd _
Σω+Type-snd Xᴰ .ω+Sectionᴰ.sωᴰ = snd
Σω+Type-snd Xᴰ .ω+Sectionᴰ.sω-natᴰ _ _ = refl

-- Displayed set condition: all fibers are sets
isωSetᴰ : {X : ωType ℓ} → ωTypeᴰ X ℓ' → Type (ℓ-max ℓ ℓ')
isωSetᴰ {X = X} Xᴰ =
  ∀ n (x : X .Xᵢ n) → isSet (Xᴰ .ωTypeᴰ.Xᵢᴰ n x)

-- Equality combinator for ωChainᴰ
makeωChainPathᴰ : {X : ωType ℓ} {Xᴰ : ωTypeᴰ X ℓ'}
  → isωSetᴰ Xᴰ
  → {c d : ωChain X} (p : c ≡ d)
  → {cᴰ : ωChainᴰ Xᴰ c} {dᴰ : ωChainᴰ Xᴰ d}
  → PathP (λ i → ∀ j → Xᴰ .ωTypeᴰ.Xᵢᴰ j (p i .xᵢ j))
      (cᴰ .ωChainᴰ.xᵢᴰ) (dᴰ .ωChainᴰ.xᵢᴰ)
  → PathP (λ i → ωChainᴰ Xᴰ (p i)) cᴰ dᴰ
makeωChainPathᴰ Xᴰset p xᵢᴰ≡ i .ωChainᴰ.xᵢᴰ = xᵢᴰ≡ i
makeωChainPathᴰ {X = X} {Xᴰ = Xᴰ} Xᴰset p
  {cᴰ = cᴰ} {dᴰ = dᴰ} xᵢᴰ≡ i .ωChainᴰ.xᵢ-natᴰ n =
  isProp→PathP propPathP
    (cᴰ .ωChainᴰ.xᵢ-natᴰ n)
    (dᴰ .ωChainᴰ.xᵢ-natᴰ n) i
  where
  propPathP : ∀ k →
    isProp (PathP
      (λ j → Xᴰ .ωTypeᴰ.Xᵢᴰ n (p k .xᵢ-nat n j))
      (Xᴰ .ωTypeᴰ.πᵢᴰ n (xᵢᴰ≡ k (suc n)))
      (xᵢᴰ≡ k n))
  propPathP k = isOfHLevelPathP' 1
    (Xᴰset n (p k .xᵢ-nat n i1))
    (Xᴰ .ωTypeᴰ.πᵢᴰ n (xᵢᴰ≡ k (suc n)))
    (xᵢᴰ≡ k n)

-- Equality combinator for ωHomᴰ
makeωHomPathᴰ : {X : ωType ℓ} {Y : ωType ℓ'}
  {Xᴰ : ωTypeᴰ X ℓ''} {Yᴰ : ωTypeᴰ Y ℓ''}
  → isωSetᴰ Yᴰ
  → {f g : ωHom X Y} (p : f ≡ g)
  → {fᴰ : ωHomᴰ Xᴰ Yᴰ f} {gᴰ : ωHomᴰ Xᴰ Yᴰ g}
  → PathP (λ i → ∀ j {x} → Xᴰ .ωTypeᴰ.Xᵢᴰ j x
      → Yᴰ .ωTypeᴰ.Xᵢᴰ j (p i .ωHom.fᵢ j x))
      (fᴰ .ωHomᴰ.fᵢᴰ) (gᴰ .ωHomᴰ.fᵢᴰ)
  → PathP (λ i → ωHomᴰ Xᴰ Yᴰ (p i)) fᴰ gᴰ
makeωHomPathᴰ Yᴰset p fᵢᴰ≡ i .ωHomᴰ.fᵢᴰ = fᵢᴰ≡ i
makeωHomPathᴰ {Xᴰ = Xᴰ} {Yᴰ = Yᴰ} Yᴰset p
  {fᴰ = fᴰ} {gᴰ = gᴰ} fᵢᴰ≡ i .ωHomᴰ.fᵢ-natᴰ n xᴰ =
  isProp→PathP propPathP
    (fᴰ .ωHomᴰ.fᵢ-natᴰ n xᴰ)
    (gᴰ .ωHomᴰ.fᵢ-natᴰ n xᴰ) i
  where
  propPathP : ∀ k →
    isProp (PathP
      (λ j → Yᴰ .ωTypeᴰ.Xᵢᴰ n
        (p k .ωHom.fᵢ-nat n _ j))
      (Yᴰ .ωTypeᴰ.πᵢᴰ n (fᵢᴰ≡ k (suc n) xᴰ))
      (fᵢᴰ≡ k n (Xᴰ .ωTypeᴰ.πᵢᴰ n xᴰ)))
  propPathP k = isOfHLevelPathP' 1
    (Yᴰset n (p k .ωHom.fᵢ-nat n _ i1))
    (Yᴰ .ωTypeᴰ.πᵢᴰ n (fᵢᴰ≡ k (suc n) xᴰ))
    (fᵢᴰ≡ k n (Xᴰ .ωTypeᴰ.πᵢᴰ n xᴰ))

-- Equality combinator for ω+Homᴰ
makeω+HomPathᴰ : {X : ω+Type ℓ} {Y : ω+Type ℓ'}
  {Xᴰ : ω+Typeᴰ X ℓ''} {Yᴰ : ω+Typeᴰ Y ℓ''}
  → isωSetᴰ (Yᴰ .ω+Typeᴰ.Xfinᴰ)
  → {f g : ω+Hom X Y} (p : f ≡ g)
  → {fᴰ : ω+Homᴰ Xᴰ Yᴰ f} {gᴰ : ω+Homᴰ Xᴰ Yᴰ g}
  → PathP (λ i →
      ωHomᴰ (Xᴰ .ω+Typeᴰ.Xfinᴰ)
        (Yᴰ .ω+Typeᴰ.Xfinᴰ) (p i .ω+Hom.fFin))
      (fᴰ .ω+Homᴰ.fFinᴰ) (gᴰ .ω+Homᴰ.fFinᴰ)
  → PathP (λ i → ∀ {x}
      → Xᴰ .ω+Typeᴰ.Xωᴰ x
      → Yᴰ .ω+Typeᴰ.Xωᴰ (p i .ω+Hom.fω x))
      (fᴰ .ω+Homᴰ.fωᴰ) (gᴰ .ω+Homᴰ.fωᴰ)
  → PathP (λ i → ω+Homᴰ Xᴰ Yᴰ (p i)) fᴰ gᴰ
makeω+HomPathᴰ Yᴰset p fFinᴰ≡ fωᴰ≡ i .ω+Homᴰ.fFinᴰ =
  fFinᴰ≡ i
makeω+HomPathᴰ Yᴰset p fFinᴰ≡ fωᴰ≡ i .ω+Homᴰ.fωᴰ =
  fωᴰ≡ i
makeω+HomPathᴰ {Xᴰ = Xᴰ} {Yᴰ = Yᴰ} Yᴰset p
  {fᴰ = fᴰ} {gᴰ = gᴰ} fFinᴰ≡ fωᴰ≡ i
  .ω+Homᴰ.fω-natᴰ n xᴰ =
  isProp→PathP propPathP
    (fᴰ .ω+Homᴰ.fω-natᴰ n xᴰ)
    (gᴰ .ω+Homᴰ.fω-natᴰ n xᴰ) i
  where
  propPathP : ∀ k →
    isProp (PathP
      (λ j → Yᴰ .ω+Typeᴰ.Xᵢᴰ n
        (p k .ω+Hom.fω-nat n _ j))
      (Yᴰ .ω+Typeᴰ.πᴰ (p k .ω+Hom.fω _)
        (fωᴰ≡ k xᴰ) .ωChainᴰ.xᵢᴰ n)
      (fFinᴰ≡ k .ωHomᴰ.fᵢᴰ n
        (Xᴰ .ω+Typeᴰ.πᴰ _ xᴰ .ωChainᴰ.xᵢᴰ n)))
  propPathP k = isOfHLevelPathP' 1
    (Yᴰset n (p k .ω+Hom.fω-nat n _ i1)) _ _
