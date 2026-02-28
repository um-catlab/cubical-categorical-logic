{-# OPTIONS --lossy-unification #-}
{-

  The category of ω+Sets has an initial object and binary coproducts,
  defined as Terminal' and BinProducts in the opposite category.

-}
module Cubical.Data.StepIndexedSet.Coproducts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
  using (isEmbedding→Inj)

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty as Empty
  renaming (rec to ⊥rec ; rec* to ⊥rec* ; elim* to ⊥elim*)
open import Cubical.Data.Empty.Properties
  using (isProp⊥* ; isContrΠ⊥*)
open import Cubical.Data.Sum as Sum
  renaming (rec to ⊎rec ; map to ⊎map)
open import Cubical.Data.Sum.More

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Data.StepIndexedSet

open Category
open UniversalElement

private
  variable
    ℓ : Level

-- | Initial ω+Type: empty at every level

𝟘-ωType : (ℓ : Level) → ωType ℓ
𝟘-ωType _ .ωType.Xᵢ _ = ⊥*
𝟘-ωType _ .ωType.πᵢ _ = ⊥elim*

𝟘-ω+Type : (ℓ : Level) → ω+Type ℓ
𝟘-ω+Type _ .ω+Type.Xfin = 𝟘-ωType _
𝟘-ω+Type _ .ω+Type.Xω = ⊥*
𝟘-ω+Type _ .ω+Type.π = ⊥elim*
𝟘-ω+Type _ .ω+Type.isLimit = isoToIsEquiv (iso ⊥elim*
    (λ c → c .ωChain.xᵢ 0)
    (λ c → ⊥rec (lower (c .ωChain.xᵢ 0)))
    (λ a → ⊥rec (lower a)))

-- | Unique morphism from 𝟘

¡-ω+Hom : (X : ω+Type ℓ) → ω+Hom (𝟘-ω+Type ℓ) X
¡-ω+Hom X .ω+Hom.fFin .ωHom.fᵢ _ = ⊥elim*
¡-ω+Hom X .ω+Hom.fFin .ωHom.fᵢ-nat _ = ⊥elim*
¡-ω+Hom X .ω+Hom.fω = ⊥elim*
¡-ω+Hom X .ω+Hom.fω-nat _ = ⊥elim*

-- | Initial object in ω+SET via Terminal' in the opposite category

Initialω+SET : ∀ {ℓ} → Terminal' ((ω+SET ℓ) ^op)
Initialω+SET {ℓ} .vertex =
  𝟘-ω+Type ℓ , (λ _ → isProp→isSet isProp⊥*)
Initialω+SET .element = tt
Initialω+SET .universal Y+ = isIsoToIsEquiv
  ( (λ _ → ¡-ω+Hom _)
  , (λ _ → refl)
  , (λ f → makeω+HomPath (Y+ .snd)
      (funExt λ _ → funExt λ x → ⊥rec (lower x))))

-- | Binary coproduct ωType (no setness needed)

module _ (A B : ω+Type ℓ) where
  private
    module A = ω+Type A
    module B = ω+Type B

  +-ωType : ωType ℓ
  +-ωType .ωType.Xᵢ i = A.Xᵢ i ⊎ B.Xᵢ i
  +-ωType .ωType.πᵢ i = ⊎map (A.πᵢ i) (B.πᵢ i)

-- | Binary coproduct ω+Type (setness needed for limit proof)

module _ (A B : ω+Type ℓ)
         (Aset : isωSet (ω+Type.Xfin A))
         (Bset : isωSet (ω+Type.Xfin B)) where
  private
    module A = ω+Type A
    module B = ω+Type B

    +-set : isωSet (+-ωType A B)
    +-set i = isSet⊎ (Aset i) (Bset i)

    -- Standalone π for the coproduct (avoids termination issues)
    π+ : A.Xω ⊎ B.Xω → ωChain (+-ωType A B)
    π+ (inl a) .ωChain.xᵢ i = inl (A.π a .ωChain.xᵢ i)
    π+ (inl a) .ωChain.xᵢ-nat i =
      cong inl (A.π a .ωChain.xᵢ-nat i)
    π+ (inr b) .ωChain.xᵢ i = inr (B.π b .ωChain.xᵢ i)
    π+ (inr b) .ωChain.xᵢ-nat i =
      cong inr (B.π b .ωChain.xᵢ-nat i)

  +-ω+Type : ω+Type ℓ
  +-ω+Type .ω+Type.Xfin = +-ωType A B
  +-ω+Type .ω+Type.Xω = A.Xω ⊎ B.Xω
  +-ω+Type .ω+Type.π = π+
  +-ω+Type .ω+Type.isLimit = isIsoToIsEquiv
    ( (λ c → π-fiber c .fst)
    , (λ c → π-fiber c .snd)
    , ret-limit)
    where
    -- Helper: chain path from pointwise equality
    make+-ChainPath : {c d : ωChain (+-ωType A B)}
      → c .ωChain.xᵢ ≡ d .ωChain.xᵢ → c ≡ d
    make+-ChainPath {c} {d} p i .ωChain.xᵢ = p i
    make+-ChainPath {c} {d} p i .ωChain.xᵢ-nat j =
      isProp→PathP
        (λ i → +-set j
          (⊎map (A.πᵢ j) (B.πᵢ j) (p i (suc j)))
          (p i j))
        (c .ωChain.xᵢ-nat j)
        (d .ωChain.xᵢ-nat j) i

    -- Helper: extract left from ⊎ when map lands left
    extract-inl : ∀ {n} (x : A.Xᵢ (suc n) ⊎ B.Xᵢ (suc n))
      → (a : A.Xᵢ n)
      → ⊎map (A.πᵢ n) (B.πᵢ n) x ≡ inl a
      → Σ[ a' ∈ A.Xᵢ (suc n) ] x ≡ inl a'
    extract-inl (inl a') _ _ = a' , refl
    extract-inl (inr b') a p =
      ⊥rec (lower (⊎Path.encode _ _ p))

    -- By induction: chain on left at all levels
    leftAt : (c : ωChain (+-ωType A B))
      → (a₀ : A.Xᵢ 0) → c .ωChain.xᵢ 0 ≡ inl a₀
      → ∀ n → Σ[ a ∈ A.Xᵢ n ] c .ωChain.xᵢ n ≡ inl a
    leftAt c a₀ p₀ zero = a₀ , p₀
    leftAt c a₀ p₀ (suc n) =
      extract-inl (c .ωChain.xᵢ (suc n))
        (leftAt c a₀ p₀ n .fst)
        (c .ωChain.xᵢ-nat n
          ∙ leftAt c a₀ p₀ n .snd)

    leftChain : (c : ωChain (+-ωType A B))
      → (a₀ : A.Xᵢ 0) → c .ωChain.xᵢ 0 ≡ inl a₀
      → ωChain (ω+Type.Xfin A)
    leftChain c a₀ p₀ .ωChain.xᵢ n =
      leftAt c a₀ p₀ n .fst
    leftChain c a₀ p₀ .ωChain.xᵢ-nat n =
      isEmbedding→Inj
        {f = inl}
        isEmbedding-inl _ _
        (sym (cong (⊎map (A.πᵢ n) (B.πᵢ n))
               (leftAt c a₀ p₀ (suc n) .snd))
         ∙ c .ωChain.xᵢ-nat n
         ∙ leftAt c a₀ p₀ n .snd)

    -- Symmetric: extract right
    extract-inr : ∀ {n}
      (x : A.Xᵢ (suc n) ⊎ B.Xᵢ (suc n))
      → (b : B.Xᵢ n)
      → ⊎map (A.πᵢ n) (B.πᵢ n) x ≡ inr b
      → Σ[ b' ∈ B.Xᵢ (suc n) ] x ≡ inr b'
    extract-inr (inr b') _ _ = b' , refl
    extract-inr (inl a') b p =
      ⊥rec (lower (⊎Path.encode _ _ p))

    rightAt : (c : ωChain (+-ωType A B))
      → (b₀ : B.Xᵢ 0) → c .ωChain.xᵢ 0 ≡ inr b₀
      → ∀ n → Σ[ b ∈ B.Xᵢ n ] c .ωChain.xᵢ n ≡ inr b
    rightAt c b₀ p₀ zero = b₀ , p₀
    rightAt c b₀ p₀ (suc n) =
      extract-inr (c .ωChain.xᵢ (suc n))
        (rightAt c b₀ p₀ n .fst)
        (c .ωChain.xᵢ-nat n
          ∙ rightAt c b₀ p₀ n .snd)

    rightChain : (c : ωChain (+-ωType A B))
      → (b₀ : B.Xᵢ 0) → c .ωChain.xᵢ 0 ≡ inr b₀
      → ωChain (ω+Type.Xfin B)
    rightChain c b₀ p₀ .ωChain.xᵢ n =
      rightAt c b₀ p₀ n .fst
    rightChain c b₀ p₀ .ωChain.xᵢ-nat n =
      isEmbedding→Inj
        {f = inr}
        isEmbedding-inr _ _
        (sym (cong (⊎map (A.πᵢ n) (B.πᵢ n))
               (rightAt c b₀ p₀ (suc n) .snd))
         ∙ c .ωChain.xᵢ-nat n
         ∙ rightAt c b₀ p₀ n .snd)

    -- Bundle inverse + section
    π-fiber : (c : ωChain (+-ωType A B))
      → Σ[ ab ∈ A.Xω ⊎ B.Xω ]
          ω+Type.π +-ω+Type ab ≡ c
    π-fiber c = go (c .ωChain.xᵢ 0) refl where
      go : (x₀ : A.Xᵢ 0 ⊎ B.Xᵢ 0)
        → c .ωChain.xᵢ 0 ≡ x₀
        → Σ[ ab ∈ A.Xω ⊎ B.Xω ]
            ω+Type.π +-ω+Type ab ≡ c
      go (inl a₀) p₀ =
        inl a∞ , make+-ChainPath (funExt sec-xᵢ)
        where
        lc = leftChain c a₀ p₀
        a∞ = invEq (_ , A.isLimit) lc
        sec-xᵢ : ∀ n → inl (A.π a∞ .ωChain.xᵢ n)
                      ≡ c .ωChain.xᵢ n
        sec-xᵢ n =
          cong inl (funExt⁻ (cong ωChain.xᵢ
            (secEq (_ , A.isLimit) lc)) n)
          ∙ sym (leftAt c a₀ p₀ n .snd)
      go (inr b₀) p₀ =
        inr b∞ , make+-ChainPath (funExt sec-xᵢ)
        where
        rc = rightChain c b₀ p₀
        b∞ = invEq (_ , B.isLimit) rc
        sec-xᵢ : ∀ n → inr (B.π b∞ .ωChain.xᵢ n)
                      ≡ c .ωChain.xᵢ n
        sec-xᵢ n =
          cong inr (funExt⁻ (cong ωChain.xᵢ
            (secEq (_ , B.isLimit) rc)) n)
          ∙ sym (rightAt c b₀ p₀ n .snd)

    -- Retraction: inv ∘ π ≡ id
    -- leftAt (π+ (inl a)) ... n .fst = A.π a .xᵢ n
    -- definitionally, so xᵢ path is refl.
    makeAChainPath : {c d : ωChain A.Xfin}
      → c .ωChain.xᵢ ≡ d .ωChain.xᵢ → c ≡ d
    makeAChainPath {c} {d} p i .ωChain.xᵢ = p i
    makeAChainPath {c} {d} p i .ωChain.xᵢ-nat j =
      isProp→PathP
        (λ i → Aset j (A.πᵢ j (p i (suc j))) (p i j))
        (c .ωChain.xᵢ-nat j)
        (d .ωChain.xᵢ-nat j) i

    makeBChainPath : {c d : ωChain B.Xfin}
      → c .ωChain.xᵢ ≡ d .ωChain.xᵢ → c ≡ d
    makeBChainPath {c} {d} p i .ωChain.xᵢ = p i
    makeBChainPath {c} {d} p i .ωChain.xᵢ-nat j =
      isProp→PathP
        (λ i → Bset j (B.πᵢ j (p i (suc j))) (p i j))
        (c .ωChain.xᵢ-nat j)
        (d .ωChain.xᵢ-nat j) i

    ret-limit : ∀ ab → π-fiber (π+ ab) .fst ≡ ab
    ret-limit (inl a) = cong inl
      (cong (invEq (_ , A.isLimit))
        (makeAChainPath
          (funExt λ { zero → refl ; (suc _) → refl }))
      ∙ retEq (_ , A.isLimit) a)
    ret-limit (inr b) = cong inr
      (cong (invEq (_ , B.isLimit))
        (makeBChainPath
          (funExt λ { zero → refl ; (suc _) → refl }))
      ∙ retEq (_ , B.isLimit) b)

  -- | Injections

  inl-ω+Hom : ω+Hom A +-ω+Type
  inl-ω+Hom .ω+Hom.fFin .ωHom.fᵢ _ = inl
  inl-ω+Hom .ω+Hom.fFin .ωHom.fᵢ-nat _ _ = refl
  inl-ω+Hom .ω+Hom.fω = inl
  inl-ω+Hom .ω+Hom.fω-nat _ _ = refl

  inr-ω+Hom : ω+Hom B +-ω+Type
  inr-ω+Hom .ω+Hom.fFin .ωHom.fᵢ _ = inr
  inr-ω+Hom .ω+Hom.fFin .ωHom.fᵢ-nat _ _ = refl
  inr-ω+Hom .ω+Hom.fω = inr
  inr-ω+Hom .ω+Hom.fω-nat _ _ = refl

  -- | Copairing

  copair-ω+Hom : ∀ {Z : ω+Type ℓ}
    → ω+Hom A Z → ω+Hom B Z → ω+Hom +-ω+Type Z
  copair-ω+Hom f g .ω+Hom.fFin .ωHom.fᵢ i =
    ⊎rec (f .ω+Hom.fᵢ i) (g .ω+Hom.fᵢ i)
  copair-ω+Hom f g .ω+Hom.fFin .ωHom.fᵢ-nat i (inl a) =
    f .ω+Hom.fFin .ωHom.fᵢ-nat i a
  copair-ω+Hom f g .ω+Hom.fFin .ωHom.fᵢ-nat i (inr b) =
    g .ω+Hom.fFin .ωHom.fᵢ-nat i b
  copair-ω+Hom f g .ω+Hom.fω =
    ⊎rec (f .ω+Hom.fω) (g .ω+Hom.fω)
  copair-ω+Hom f g .ω+Hom.fω-nat i (inl a) =
    f .ω+Hom.fω-nat i a
  copair-ω+Hom f g .ω+Hom.fω-nat i (inr b) =
    g .ω+Hom.fω-nat i b

-- | Binary coproducts in ω+SET via BinProducts in opposite

BinCoproductsω+SET : ∀ {ℓ} → BinProducts ((ω+SET ℓ) ^op)
BinCoproductsω+SET ((A , Aset) , (B , Bset)) .vertex =
  +-ω+Type A B Aset Bset
  , (λ i → isSet⊎ (Aset i) (Bset i))
BinCoproductsω+SET ((A , Aset) , (B , Bset)) .element =
  inl-ω+Hom A B Aset Bset , inr-ω+Hom A B Aset Bset
BinCoproductsω+SET ((A , Aset) , (B , Bset)) .universal
  (Z , Zset) = isIsoToIsEquiv
    ( (λ (f , g) → copair-ω+Hom A B Aset Bset f g)
    , (λ (f , g) → ΣPathP
        ( makeω+HomPath Zset refl
        , makeω+HomPath Zset refl))
    , (λ h → makeω+HomPath Zset
        (funExt λ n → funExt λ { (inl _) → refl
                                ; (inr _) → refl })))
