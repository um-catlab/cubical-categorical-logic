{-# OPTIONS --lossy-unification #-}
{-

  The category of ω+Sets is cartesian closed: beyond having
  a terminal object and binary products (CartesianCategory),
  every object is exponentiable.

  The exponential B^A is built from "truncated natural
  transformations": at level n, (B^A)ₙ is the type of
  natural families (f₀,...,fₙ) where fᵢ : Aᵢ → Bᵢ.
  The limit level (B^A)ω is the full ωHom(A,B).

-}
module Cubical.Data.StepIndexedSet.CartesianClosedCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Exponentials

open import Cubical.Data.StepIndexedSet
open import Cubical.Data.StepIndexedSet.CartesianCategory

open Category
open UniversalElement

private
  variable
    ℓ : Level

-- Truncated natural transformations: compatible families up to
-- level n. This is the internal hom at finite levels.

module _ (A B : ωType ℓ) where
  private
    module A = ωType A
    module B = ωType B

  -- ωHom≤ n = natural families (f₀,...,fₙ)
  -- topωHom≤ extracts the map at level n
  ωHom≤ : ℕ → Type ℓ
  topωHom≤ : (n : ℕ) → ωHom≤ n → A.Xᵢ n → B.Xᵢ n

  ωHom≤ zero = A.Xᵢ 0 → B.Xᵢ 0
  ωHom≤ (suc n) =
    Σ[ rest ∈ ωHom≤ n ]
    Σ[ f ∈ (A.Xᵢ (suc n) → B.Xᵢ (suc n)) ]
    (∀ x → B.πᵢ n (f x)
          ≡ topωHom≤ n rest (A.πᵢ n x))

  topωHom≤ zero f = f
  topωHom≤ (suc _) (_ , f , _) = f

  -- Restriction: drop the top level
  restrictωHom≤ : ∀ n → ωHom≤ (suc n) → ωHom≤ n
  restrictωHom≤ _ (rest , _) = rest

  -- The exponential as an ωType
  Exp-ωType : ωType ℓ
  Exp-ωType .ωType.Xᵢ = ωHom≤
  Exp-ωType .ωType.πᵢ = restrictωHom≤

  -- Truncate an ωHom to level n
  truncωHom : ωHom A B → (n : ℕ) → ωHom≤ n
  truncωHom-top : (f : ωHom A B) (n : ℕ)
    → topωHom≤ n (truncωHom f n) ≡ f .ωHom.fᵢ n

  truncωHom f zero = f .ωHom.fᵢ 0
  truncωHom f (suc n) =
    truncωHom f n , f .ωHom.fᵢ (suc n)
    , λ x → f .ωHom.fᵢ-nat n x
      ∙ funExt⁻ (sym (truncωHom-top f n))
          (A.πᵢ n x)

  truncωHom-top f zero = refl
  truncωHom-top f (suc _) = refl

  -- Reconstruct an ωHom from a compatible family
  untruncωHom : ωChain Exp-ωType → ωHom A B
  untruncωHom c .ωHom.fᵢ n =
    topωHom≤ n (c .ωChain.xᵢ n)
  untruncωHom c .ωHom.fᵢ-nat n x =
    c .ωChain.xᵢ (suc n) .snd .snd x
    ∙ cong (λ h → topωHom≤ n h (A.πᵢ n x))
        (c .ωChain.xᵢ-nat n)

-- Exponential ω+Type (only needs Bset, not Aset)

module _ (A B : ω+Type ℓ)
         (Bset : isωSet (ω+Type.Xfin B)) where
  private
    module A = ω+Type A
    module B = ω+Type B

  -- ωHom≤ is a set at each level
  isSetωHom≤ :
    ∀ n → isSet (ωHom≤ A.Xfin B.Xfin n)
  isSetωHom≤ zero = isSet→ (Bset 0)
  isSetωHom≤ (suc n) =
    isSetΣ (isSetωHom≤ n) λ _ →
    isSetΣ (isSet→ (Bset (suc n))) λ _ →
    isProp→isSet (isPropΠ λ _ → Bset n _ _)

  Exp-ω+Type : ω+Type ℓ
  Exp-ω+Type .ω+Type.Xfin = Exp-ωType A.Xfin B.Xfin
  Exp-ω+Type .ω+Type.Xω = ω+Hom A B
  Exp-ω+Type .ω+Type.π f .ωChain.xᵢ n =
    truncωHom A.Xfin B.Xfin (f .ω+Hom.fFin) n
  Exp-ω+Type .ω+Type.π f .ωChain.xᵢ-nat n = refl
  Exp-ω+Type .ω+Type.isLimit = isIsoToIsEquiv
    ( untruncω+Hom
    , sec-chain
    , (λ f → makeω+HomPath Bset
        (makeωHomPath Bset
          (funExt
            (truncωHom-top A.Xfin B.Xfin
              (f .ω+Hom.fFin))))))
    where
    untruncω+Hom :
      ωChain (Exp-ωType A.Xfin B.Xfin) → ω+Hom A B
    untruncω+Hom c .ω+Hom.fFin =
      untruncωHom A.Xfin B.Xfin c
    untruncω+Hom c .ω+Hom.fω x =
      invEq (_ , B.isLimit)
        (ωHom-applyChain
          (untruncωHom A.Xfin B.Xfin c) (A.π x))
    untruncω+Hom c .ω+Hom.fω-nat n x =
      cong (λ c → c .ωChain.xᵢ n)
        (secEq (_ , B.isLimit)
          (ωHom-applyChain
            (untruncωHom A.Xfin B.Xfin c)
            (A.π x)))

    sec-xᵢ : (c : ωChain (Exp-ωType A.Xfin B.Xfin))
      → ∀ n → truncωHom A.Xfin B.Xfin
                (untruncωHom A.Xfin B.Xfin c) n
              ≡ c .ωChain.xᵢ n
    sec-xᵢ c zero = refl
    sec-xᵢ c (suc n) = ΣPathP
      ( sec-xᵢ c n
        ∙ sym (c .ωChain.xᵢ-nat n)
      , ΣPathPProp
          (λ _ → isPropΠ λ _ → Bset n _ _)
          refl)

    sec-chain :
      (c : ωChain (Exp-ωType A.Xfin B.Xfin))
      → ω+Type.π Exp-ω+Type
          (untruncω+Hom c) ≡ c
    sec-chain c i .ωChain.xᵢ n =
      sec-xᵢ c n i
    sec-chain c i .ωChain.xᵢ-nat n =
      isProp→PathP
        (λ i → isSetωHom≤ n
          (restrictωHom≤ A.Xfin B.Xfin n
            (sec-xᵢ c (suc n) i))
          (sec-xᵢ c n i))
        refl (c .ωChain.xᵢ-nat n) i

-- Evaluation and currying (need both Aset and Bset)

module _ (A B : ω+Type ℓ)
         (Aset : isωSet (ω+Type.Xfin A))
         (Bset : isωSet (ω+Type.Xfin B)) where
  private
    module A = ω+Type A
    module B = ω+Type B

  -- Evaluation map: (B^A) × A → B
  eval-ω+Hom : ω+Hom
    (×-ω+Type (Exp-ω+Type A B Bset) A
      (isSetωHom≤ A B Bset) Aset)
    B
  eval-ω+Hom .ω+Hom.fFin .ωHom.fᵢ n (h , a) =
    topωHom≤ A.Xfin B.Xfin n h a
  eval-ω+Hom .ω+Hom.fFin .ωHom.fᵢ-nat n (h , a) =
    h .snd .snd a
  eval-ω+Hom .ω+Hom.fω (f , a) =
    f .ω+Hom.fω a
  eval-ω+Hom .ω+Hom.fω-nat n (f , a) =
    f .ω+Hom.fω-nat n a
    ∙ funExt⁻
        (sym (truncωHom-top A.Xfin B.Xfin
          (f .ω+Hom.fFin) n))
        (A.π a .ωChain.xᵢ n)

  -- Lambda (currying): given g : Γ × A → B, produce Γ → B^A
  --
  -- At finite levels, curry-fᵢ builds the truncated hom
  -- inductively. curry-fᵢ-top provides the propositional
  -- correction (same pattern as truncωHom/truncωHom-top).
  module _ {Γ : ω+Type ℓ}
    (Γset : isωSet (ω+Type.Xfin Γ))
    (g : ω+Hom (×-ω+Type Γ A Γset Aset) B) where
    private
      module Γ = ω+Type Γ

    curry-fᵢ : ∀ n → Γ.Xᵢ n
      → ωHom≤ A.Xfin B.Xfin n
    curry-fᵢ-top : ∀ n (γ : Γ.Xᵢ n)
      → topωHom≤ A.Xfin B.Xfin n (curry-fᵢ n γ)
      ≡ λ a → g .ω+Hom.fFin .ωHom.fᵢ n (γ , a)

    curry-fᵢ zero γ a =
      g .ω+Hom.fFin .ωHom.fᵢ 0 (γ , a)
    curry-fᵢ (suc n) γ =
      curry-fᵢ n (Γ.πᵢ n γ)
      , (λ a → g .ω+Hom.fFin .ωHom.fᵢ (suc n) (γ , a))
      , λ a → g .ω+Hom.fFin .ωHom.fᵢ-nat n (γ , a)
        ∙ funExt⁻ (sym (curry-fᵢ-top n (Γ.πᵢ n γ)))
            (A.πᵢ n a)

    curry-fᵢ-top zero γ = refl
    curry-fᵢ-top (suc n) γ = refl

    curry-fᵢ-nat : ∀ n γ
      → curry-fᵢ (suc n) γ .fst
      ≡ curry-fᵢ n (Γ.πᵢ n γ)
    curry-fᵢ-nat n γ = refl

    -- Curry at the limit level
    curry-fω : Γ.Xω → ω+Hom A B
    curry-fω γ .ω+Hom.fFin .ωHom.fᵢ n a =
      g .ω+Hom.fFin .ωHom.fᵢ n
        (Γ.π γ .ωChain.xᵢ n , a)
    curry-fω γ .ω+Hom.fFin .ωHom.fᵢ-nat n a =
      g .ω+Hom.fFin .ωHom.fᵢ-nat n
        (Γ.π γ .ωChain.xᵢ (suc n) , a)
      ∙ cong (λ γn →
          g .ω+Hom.fFin .ωHom.fᵢ n (γn , A.πᵢ n a))
          (Γ.π γ .ωChain.xᵢ-nat n)
    curry-fω γ .ω+Hom.fω a =
      g .ω+Hom.fω (γ , a)
    curry-fω γ .ω+Hom.fω-nat n a =
      g .ω+Hom.fω-nat n (γ , a)

    -- truncωHom of curry-fω agrees with curry-fᵢ
    curry-fω-nat : ∀ n (γ : Γ.Xω)
      → truncωHom A.Xfin B.Xfin
          (curry-fω γ .ω+Hom.fFin) n
      ≡ curry-fᵢ n (Γ.π γ .ωChain.xᵢ n)
    curry-fω-nat zero γ = refl
    curry-fω-nat (suc n) γ = ΣPathP
      ( curry-fω-nat n γ
        ∙ cong (curry-fᵢ n)
            (sym (Γ.π γ .ωChain.xᵢ-nat n))
      , ΣPathPProp
          (λ _ → isPropΠ λ _ → Bset n _ _)
          refl)

  λ-ω+Hom : ∀ {Γ : ω+Type ℓ}
    (Γset : isωSet (ω+Type.Xfin Γ))
    → ω+Hom (×-ω+Type Γ A Γset Aset) B
    → ω+Hom Γ (Exp-ω+Type A B Bset)
  λ-ω+Hom Γset g .ω+Hom.fFin .ωHom.fᵢ n γ =
    curry-fᵢ Γset g n γ
  λ-ω+Hom Γset g .ω+Hom.fFin .ωHom.fᵢ-nat n γ =
    curry-fᵢ-nat Γset g n γ
  λ-ω+Hom Γset g .ω+Hom.fω γ =
    curry-fω Γset g γ
  λ-ω+Hom Γset g .ω+Hom.fω-nat n γ =
    curry-fω-nat Γset g n γ

-- AllExponentiable for ω+SET

Exponentiableω+SET :
  ∀ {ℓ} → AllExponentiable (ω+SET ℓ) BinProductsω+SET
Exponentiableω+SET (A , Aset) (B , Bset) .vertex =
  Exp-ω+Type A B Bset
  , isSetωHom≤ A B Bset
Exponentiableω+SET (A , Aset) (B , Bset) .element =
  eval-ω+Hom A B Aset Bset
Exponentiableω+SET (A , Aset) (B , Bset)
  .universal (Y+ , Yset) = isIsoToIsEquiv
    ( (λ g → λ-ω+Hom A B Aset Bset Yset g)
    , (λ g → makeω+HomPath Bset
        (makeωHomPath Bset
          (funExt λ n → funExt λ (y , a) →
            funExt⁻
              (curry-fᵢ-top A B Aset Bset Yset g n y)
              a)))
    , (λ f → makeω+HomPath
        (isSetωHom≤ A B Bset)
        (makeωHomPath (isSetωHom≤ A B Bset)
          (funExt λ n → funExt λ y →
            λ-η f n y))))
    where
    λ-η : (f : ω+Hom Y+ (Exp-ω+Type A B Bset))
      → ∀ n y
      → curry-fᵢ A B Aset Bset Yset
          (ω+Hom-comp
            (pair-ω+Hom (Exp-ω+Type A B Bset) A
              (isSetωHom≤ A B Bset) Aset
              (ω+Hom-comp (π₁-ω+Hom Y+ A Yset Aset) f)
              (π₂-ω+Hom Y+ A Yset Aset))
            (eval-ω+Hom A B Aset Bset))
          n y
        ≡ f .ω+Hom.fFin .ωHom.fᵢ n y
    λ-η f zero y = refl
    λ-η f (suc n) y =
      ΣPathP
        ( λ-η f n _
          ∙ sym (f .ω+Hom.fFin .ωHom.fᵢ-nat n y)
        , ΣPathPProp
            (λ _ → isPropΠ λ _ → Bset n _ _)
            refl)

-- Cartesian Closed Category

ω+SETCCC : ∀ ℓ → CartesianClosedCategory (ℓ-suc ℓ) ℓ
ω+SETCCC ℓ .CartesianClosedCategory.CC = ω+SETCC ℓ
ω+SETCCC ℓ .CartesianClosedCategory.exps =
  Exponentiableω+SET
