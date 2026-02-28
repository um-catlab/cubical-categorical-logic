{-

  Step-Indexed Sets

  A step-indexed set is equivalent to a sheaf over the ordinal ω + 1.

  Concretely, it consists of:
  1. A family of sets Xₙ indexed by natural numbers
  2. Restriction maps rest : Xₙ₊₁ → Xₙ
  3. A set X∞ with projections πₙ : X∞ → Xₙ
  4. Coherence: rest n ∘ π (suc n) ≡ π n
  5. Limit condition: X∞ is the limit of the chain

-}
module Cubical.Data.StepIndexedSet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Unit.Properties using (isSetUnit*)

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

open Category
open Functor

private
  variable
    ℓ ℓ' ℓ'' : Level

-- An ωType (inverse system indexed by ℕ): a sequence of Types with
-- restriction maps going "downward".
--
-- The intuition for programming semantics is that this is an infinite
-- sequence of increasingly refined approximations of some
-- (coinductive) type.
record ωType ℓ : Type (ℓ-suc ℓ) where
  field
    Xᵢ   : ℕ → Type ℓ
    πᵢ  : ∀ n → Xᵢ (suc n) → Xᵢ n

-- A homomorphism of ωTypes: a level-wise family of maps that
-- commutes with the restriction maps.
record ωHom (X : ωType ℓ) (Y : ωType ℓ') : Type (ℓ-max ℓ ℓ') where
  private
    module X = ωType X
    module Y = ωType Y
  field
    fᵢ     : ∀ i → X.Xᵢ i → Y.Xᵢ i
    fᵢ-nat : ∀ n x → Y.πᵢ n (fᵢ (suc n) x) ≡ fᵢ n (X.πᵢ n x)

-- An ωChain is a compatible sequence of elements in an ωType.
--
-- The intuition for semantics is that this is an infinite sequence of
-- approximations to an element of the coinductive type.
--
-- In fact, the type of ωChains itself can serve as the "completed"
-- type, it is the limit of the ωType.
record ωChain (X : ωType ℓ) : Type ℓ where
  open ωType X
  field
    xᵢ : ∀ i → Xᵢ i
    xᵢ-nat : ∀ i → πᵢ i (xᵢ (suc i)) ≡ xᵢ i

-- An ω+Type is an ωType with a *choice* of limit.

-- This may seem redundant because the type of ωChains is always
-- available to use as a choice, but often we can have a much simpler
-- definition of Xω.
record ω+Type ℓ : Type (ℓ-suc ℓ) where
  field
    Xfin : ωType ℓ
  open ωType Xfin public
  field
    Xω : Type ℓ
    π : Xω → ωChain Xfin
    isLimit : isEquiv π

-- A homomorphism of ω+Types: an ωHom on the finite part together with
-- a map on the limit types, commuting with the projections.
record ω+Hom (X : ω+Type ℓ) (Y : ω+Type ℓ') : Type (ℓ-max ℓ ℓ') where
  private
    module X = ω+Type X
    module Y = ω+Type Y
  field
    fFin : ωHom X.Xfin Y.Xfin
  open ωHom fFin public
  field
    fω     : X.Xω → Y.Xω
    fω-nat : ∀ i x → Y.π (fω x) .ωChain.xᵢ i ≡ fᵢ i (X.π x .ωChain.xᵢ i)

-- Identity and composition for ωHom

ωHom-id : (X : ωType ℓ) → ωHom X X
ωHom-id X .ωHom.fᵢ i x = x
ωHom-id X .ωHom.fᵢ-nat n x = refl

ωHom-comp : {X : ωType ℓ} {Y : ωType ℓ'} {Z : ωType ℓ''} → ωHom X Y → ωHom Y Z → ωHom X Z
ωHom-comp f g .ωHom.fᵢ i x = g .ωHom.fᵢ i (f .ωHom.fᵢ i x)
ωHom-comp f g .ωHom.fᵢ-nat n x =
  g .ωHom.fᵢ-nat n (f .ωHom.fᵢ (suc n) x)
  ∙ cong (g .ωHom.fᵢ n) (f .ωHom.fᵢ-nat n x)

-- Action of an ωHom on an ωChain
ωHom-applyChain : {X : ωType ℓ} {Y : ωType ℓ'} → ωHom X Y → ωChain X → ωChain Y
ωHom-applyChain f c .ωChain.xᵢ i = f .ωHom.fᵢ i (c .ωChain.xᵢ i)
ωHom-applyChain f c .ωChain.xᵢ-nat i =
  f .ωHom.fᵢ-nat i (c .ωChain.xᵢ (suc i))
  ∙ cong (f .ωHom.fᵢ i) (c .ωChain.xᵢ-nat i)

-- Identity and composition for ω+Hom

ω+Hom-id : (X : ω+Type ℓ) → ω+Hom X X
ω+Hom-id X .ω+Hom.fFin = ωHom-id (X .ω+Type.Xfin)
ω+Hom-id X .ω+Hom.fω x = x
ω+Hom-id X .ω+Hom.fω-nat i x = refl

ω+Hom-comp : {X : ω+Type ℓ} {Y : ω+Type ℓ'} {Z : ω+Type ℓ''} → ω+Hom X Y → ω+Hom Y Z → ω+Hom X Z
ω+Hom-comp f g .ω+Hom.fFin = ωHom-comp (f .ω+Hom.fFin) (g .ω+Hom.fFin)
ω+Hom-comp f g .ω+Hom.fω x = g .ω+Hom.fω (f .ω+Hom.fω x)
ω+Hom-comp f g .ω+Hom.fω-nat i x =
  g .ω+Hom.fω-nat i (f .ω+Hom.fω x)
  ∙ cong (g .ω+Hom.fᵢ i) (f .ω+Hom.fω-nat i x)

isωSet : ωType ℓ → Type _
isωSet X = ∀ i → isSet (X .ωType.Xᵢ i)

-- Equality combinators for ωHom

module _ {X : ωType ℓ} {Y : ωType ℓ'} where
  private
    module Y = ωType Y

  ωHomΣ : Type (ℓ-max ℓ ℓ')
  ωHomΣ = Σ[ f ∈ (∀ i → X .ωType.Xᵢ i → Y.Xᵢ i) ]
            (∀ n x → Y.πᵢ n (f (suc n) x) ≡ f n (X .ωType.πᵢ n x))

  ωHomΣIso : Iso (ωHom X Y) ωHomΣ
  unquoteDef ωHomΣIso = defineRecordIsoΣ ωHomΣIso (quote (ωHom))

  isProp-fᵢ-nat : (fᵢ : ∀ i → X .ωType.Xᵢ i → Y.Xᵢ i)
    → isωSet Y
    → isProp (∀ n x → Y.πᵢ n (fᵢ (suc n) x) ≡ fᵢ n (X .ωType.πᵢ n x))
  isProp-fᵢ-nat fᵢ Yset =
    isPropΠ λ n → isPropΠ λ x → Yset n _ _

  makeωHomPath : isωSet Y → {f g : ωHom X Y}
    → f .ωHom.fᵢ ≡ g .ωHom.fᵢ → f ≡ g
  makeωHomPath Yset fᵢ≡ =
    isoFunInjective ωHomΣIso _ _ (ΣPathPProp (λ f → isProp-fᵢ-nat f Yset) fᵢ≡)

  isSetωHom : isωSet Y → isSet (ωHom X Y)
  isSetωHom Yset = isOfHLevelRetractFromIso 2 ωHomΣIso
    (isSetΣ (isSetΠ λ i → isSet→ (Yset i))
      λ f → isProp→isSet (isProp-fᵢ-nat f Yset))

-- Equality combinators for ω+Hom

module _ {X : ω+Type ℓ} {Y : ω+Type ℓ'} where
  private
    module X = ω+Type X
    module Y = ω+Type Y

  ω+HomΣ : Type (ℓ-max ℓ ℓ')
  ω+HomΣ = Σ[ fFin ∈ ωHom X.Xfin Y.Xfin ]
            Σ[ fω ∈ (X.Xω → Y.Xω) ]
            (∀ i x → Y.π (fω x) .ωChain.xᵢ i ≡ ωHom.fᵢ fFin i (X.π x .ωChain.xᵢ i))

  ω+HomΣIso : Iso (ω+Hom X Y) ω+HomΣ
  unquoteDef ω+HomΣIso = defineRecordIsoΣ ω+HomΣIso (quote (ω+Hom))

  isProp-fω-nat : (fFin : ωHom X.Xfin Y.Xfin) (fω : X.Xω → Y.Xω)
    → isωSet Y.Xfin
    → isProp (∀ i x → Y.π (fω x) .ωChain.xᵢ i ≡ ωHom.fᵢ fFin i (X.π x .ωChain.xᵢ i))
  isProp-fω-nat fFin fω Yset =
    isPropΠ λ i → isPropΠ λ x → Yset i _ _

  -- Helper: build an ωChain path from pointwise xᵢ equality
  ωChainΣ : Type ℓ'
  ωChainΣ =
    Σ[ xᵢ ∈ (∀ i → Y.Xᵢ i) ]
      (∀ i → Y.πᵢ i (xᵢ (suc i)) ≡ xᵢ i)

  ωChainΣIso : Iso (ωChain Y.Xfin) ωChainΣ
  unquoteDef ωChainΣIso = defineRecordIsoΣ ωChainΣIso (quote (ωChain))

  makeωChainPath : isωSet Y.Xfin → {c d : ωChain Y.Xfin}
    → c .ωChain.xᵢ ≡ d .ωChain.xᵢ
    → c ≡ d
  makeωChainPath Yset xᵢ≡ =
    isoFunInjective ωChainΣIso _ _
      (ΣPathPProp (λ xᵢ → isPropΠ λ i → Yset i _ _) xᵢ≡)

  -- The fω component is determined by fFin via the limit property
  private
    fFin→fω≡ : isωSet Y.Xfin → {f g : ω+Hom X Y}
      → f .ω+Hom.fFin ≡ g .ω+Hom.fFin
      → f .ω+Hom.fω ≡ g .ω+Hom.fω
    fFin→fω≡ Yset {f} {g} fFin≡ = funExt λ x →
      isEmbedding→Inj {f = Y.π} (isEquiv→isEmbedding Y.isLimit)
        (f .ω+Hom.fω x) (g .ω+Hom.fω x)
        (makeωChainPath Yset
          (funExt λ i →
            f .ω+Hom.fω-nat i x
            ∙ cong (λ h → ωHom.fᵢ h i (X.π x .ωChain.xᵢ i)) fFin≡
            ∙ sym (g .ω+Hom.fω-nat i x)))

  makeω+HomPath : isωSet Y.Xfin → {f g : ω+Hom X Y}
    → f .ω+Hom.fᵢ ≡ g .ω+Hom.fᵢ
    → f ≡ g
  makeω+HomPath Yset {f} {g} fᵢ≡ = path where
    fFin≡ : f .ω+Hom.fFin ≡ g .ω+Hom.fFin
    fFin≡ = makeωHomPath Yset fᵢ≡
    fω≡ : f .ω+Hom.fω ≡ g .ω+Hom.fω
    fω≡ = fFin→fω≡ Yset {f = f}{g = g} fFin≡
    nat≡ : PathP (λ i → ∀ j x →
               Y.π (fω≡ i x) .ωChain.xᵢ j ≡
               ωHom.fᵢ (fFin≡ i) j (X.π x .ωChain.xᵢ j))
              (f .ω+Hom.fω-nat) (g .ω+Hom.fω-nat)
    nat≡ = isProp→PathP (λ i → isProp-fω-nat (fFin≡ i) (fω≡ i) Yset)
              (f .ω+Hom.fω-nat) (g .ω+Hom.fω-nat)
    path : f ≡ g
    path i .ω+Hom.fFin = fFin≡ i
    path i .ω+Hom.fω = fω≡ i
    path i .ω+Hom.fω-nat = nat≡ i

  isEmbedding-ω+Hom-fFin : isωSet Y.Xfin
    → isEmbedding (ω+Hom.fFin {X = X} {Y = Y})
  isEmbedding-ω+Hom-fFin Yset =
    injEmbedding (isSetωHom Yset)
      (λ p → makeω+HomPath Yset (cong ωHom.fᵢ p))

  isSetω+Hom : isωSet Y.Xfin → isSet X.Xω → isSet Y.Xω → isSet (ω+Hom X Y)
  isSetω+Hom Yset XωSet YωSet = isOfHLevelRetractFromIso 2 ω+HomΣIso
    (isSetΣ (isSetωHom Yset)
      λ fFin → isSetΣ (isSet→ YωSet)
        λ fω → isProp→isSet (isProp-fω-nat fFin fω Yset))

ωSet : ∀ ℓ → Type (ℓ-suc ℓ)
ωSet = λ ℓ → Σ[ X ∈ ωType ℓ ] isωSet X

-- Note: the Xω is automatically a set if all of the Xfins are because
-- it is equivalent to the ωChains.
ω+Set : ∀ ℓ → Type (ℓ-suc ℓ)
ω+Set ℓ = Σ[ X ∈ ω+Type ℓ ] isωSet (X .ω+Type.Xfin)

-- Category of ωSets

ωSET : ∀ ℓ → Category (ℓ-suc ℓ) ℓ
ωSET ℓ .ob = ωSet ℓ
ωSET ℓ .Hom[_,_] (X , _) (Y , _) = ωHom X Y
ωSET ℓ .id {x = _ , Xset} = ωHom-id _
ωSET ℓ ._⋆_ f g = ωHom-comp f g
ωSET ℓ .⋆IdL {x = _ , Xset} {y = _ , Yset} f = makeωHomPath Yset refl
ωSET ℓ .⋆IdR {x = _ , Xset} {y = _ , Yset} f = makeωHomPath Yset refl
ωSET ℓ .⋆Assoc {x = _ , Xset} {y = _ , Yset} {z = _ , Zset} {w = _ , Wset} f g h = makeωHomPath Wset refl
ωSET ℓ .isSetHom {x = _ , Xset} {y = _ , Yset} = isSetωHom Yset

-- Category of ω+Sets

ω+SET : ∀ ℓ → Category (ℓ-suc ℓ) ℓ
ω+SET ℓ .ob = ω+Set ℓ
ω+SET ℓ .Hom[_,_] (X , _) (Y , _) = ω+Hom X Y
ω+SET ℓ .id {x = _ , Xset} = ω+Hom-id _
ω+SET ℓ ._⋆_ f g = ω+Hom-comp f g
ω+SET ℓ .⋆IdL {x = _ , Xset} {y = _ , Yset} f = makeω+HomPath Yset refl
ω+SET ℓ .⋆IdR {x = _ , Xset} {y = _ , Yset} f = makeω+HomPath Yset refl
ω+SET ℓ .⋆Assoc {x = _ , Xset} {y = _ , Yset} {z = _ , Zset} {w = _ , Wset} f g h = makeω+HomPath Wset refl
ω+SET ℓ .isSetHom {x = _ , Xset} {y = _ , Yset} =
  Embedding-into-hLevel→hLevel 1
    (ω+Hom.fFin , isEmbedding-ω+Hom-fFin Yset)
    (isSetωHom Yset)

-- Forgetful functor from ω+Sets to ωSets

ForgetLimit : ∀ {ℓ} → Functor (ω+SET ℓ) (ωSET ℓ)
ForgetLimit .F-ob (X , Xset) = X .ω+Type.Xfin , Xset
ForgetLimit .F-hom f = f .ω+Hom.fFin
ForgetLimit .F-id = refl
ForgetLimit .F-seq f g = refl

-- ForgetLimit is fully faithful: any ωHom between finite parts
-- lifts uniquely to an ω+Hom via the limit property.

module _ {ℓ} where
  private
    -- Lift an ωHom to an ω+Hom using the limit structure
    liftωHom : (X Y : ω+Type ℓ)
      → ωHom (X .ω+Type.Xfin) (Y .ω+Type.Xfin) → ω+Hom X Y
    liftωHom X Y fFin .ω+Hom.fFin = fFin
    liftωHom X Y fFin .ω+Hom.fω x =
      invIsEq (Y .ω+Type.isLimit) (ωHom-applyChain fFin (X .ω+Type.π x))
    liftωHom X Y fFin .ω+Hom.fω-nat i x =
      cong (λ c → c .ωChain.xᵢ i)
        (secIsEq (Y .ω+Type.isLimit)
          (ωHom-applyChain fFin (X .ω+Type.π x)))

  isFullyFaithfulForgetLimit : Functor.isFullyFaithful (ForgetLimit {ℓ})
  isFullyFaithfulForgetLimit (X , Xset) (Y , Yset) =
    isoToIsEquiv theIso
    where
      theIso : Iso (ω+Hom X Y) (ωHom (X .ω+Type.Xfin) (Y .ω+Type.Xfin))
      theIso .Iso.fun = ω+Hom.fFin
      theIso .Iso.inv = liftωHom X Y
      theIso .Iso.sec fFin = refl
      theIso .Iso.ret f = makeω+HomPath Yset refl

ωChainω+Type : (X : ωType ℓ) → ω+Type ℓ
ωChainω+Type X .ω+Type.Xfin = X
ωChainω+Type X .ω+Type.Xω = ωChain X
ωChainω+Type X .ω+Type.π = λ z → z
ωChainω+Type X .ω+Type.isLimit = idIsEquiv _

module _ {X : ωType ℓ}{Y : ω+Type ℓ'} where
  ωChainω+Type-rec : ωHom X (Y .ω+Type.Xfin) → ω+Hom (ωChainω+Type X) Y
  ωChainω+Type-rec f .ω+Hom.fFin = f
  ωChainω+Type-rec f .ω+Hom.fω c =
    invIsEq (Y .ω+Type.isLimit) (ωHom-applyChain f c)
  ωChainω+Type-rec f .ω+Hom.fω-nat i c =
    cong (λ c → c .ωChain.xᵢ i)
      (secIsEq (Y .ω+Type.isLimit) (ωHom-applyChain f c))

ωCHAIN : ∀ {ℓ} → LeftAdjoint (ForgetLimit {ℓ})
ωCHAIN X .UniversalElement.vertex .fst = ωChainω+Type (X .fst)
ωCHAIN X .UniversalElement.vertex .snd = X .snd
ωCHAIN X .UniversalElement.element = ωHom-id (X .fst)
ωCHAIN X .UniversalElement.universal Y+ = isIsoToIsEquiv
  ( ωChainω+Type-rec
  , (λ b → makeωHomPath (Y+ .snd) refl)
  , (λ a → makeω+HomPath (Y+ .snd) refl))
