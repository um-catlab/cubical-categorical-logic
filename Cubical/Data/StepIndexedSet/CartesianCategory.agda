{-# OPTIONS --lossy-unification #-}
{-

  The category of ω+Sets is cartesian: it has a terminal object
  and binary products.

-}
module Cubical.Data.StepIndexedSet.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Unit.Properties using (isSetUnit*)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Data.StepIndexedSet

open Category
open UniversalElement

private
  variable
    ℓ : Level

-- Terminal ω+Type: constant Unit* at every level

𝟙-ωType : (ℓ : Level) → ωType ℓ
𝟙-ωType _ .ωType.Xᵢ _ = Unit*
𝟙-ωType _ .ωType.πᵢ _ _ = tt*

𝟙-ω+Type : (ℓ : Level) → ω+Type ℓ
𝟙-ω+Type _ .ω+Type.Xfin = 𝟙-ωType _
𝟙-ω+Type _ .ω+Type.Xω = Unit*
𝟙-ω+Type _ .ω+Type.π _ .ωChain.xᵢ _ = tt*
𝟙-ω+Type _ .ω+Type.π _ .ωChain.xᵢ-nat _ = refl
𝟙-ω+Type _ .ω+Type.isLimit = isIsoToIsEquiv
  ( (λ _ → tt*)
  , (λ _ → refl)
  , (λ _ → refl))

-- Unique morphism into 𝟙

!-ω+Hom : (X : ω+Type ℓ) → ω+Hom X (𝟙-ω+Type ℓ)
!-ω+Hom X .ω+Hom.fFin = record
  { fᵢ = λ _ _ → tt* ; fᵢ-nat = λ _ _ → refl }
!-ω+Hom X .ω+Hom.fω _ = tt*
!-ω+Hom X .ω+Hom.fω-nat _ _ = refl

Terminalω+SET : ∀ {ℓ} → Terminal' (ω+SET ℓ)
Terminalω+SET {ℓ} .vertex = 𝟙-ω+Type ℓ , (λ _ → isSetUnit*)
Terminalω+SET .element = tt
Terminalω+SET .universal Y+ = isIsoToIsEquiv
  ( (λ _ → !-ω+Hom _)
  , (λ _ → refl)
  , (λ a → makeω+HomPath {Y = 𝟙-ω+Type _}
      (λ _ → isSetUnit*)
      (makeωHomPath {Y = 𝟙-ωType _}
        (λ _ → isSetUnit*) refl)))

-- Binary product of ω+Types

module _ (A B : ω+Type ℓ)
         (Aset : isωSet (ω+Type.Xfin A))
         (Bset : isωSet (ω+Type.Xfin B)) where
  private
    module A = ω+Type A
    module B = ω+Type B

  ×-ωType : ωType ℓ
  ×-ωType .ωType.Xᵢ i = A.Xᵢ i × B.Xᵢ i
  ×-ωType .ωType.πᵢ i (a , b) = A.πᵢ i a , B.πᵢ i b

  private
    ×-set : isωSet ×-ωType
    ×-set i = isSet× (Aset i) (Bset i)

    make×ChainPath : {c d : ωChain ×-ωType}
      → c .ωChain.xᵢ ≡ d .ωChain.xᵢ → c ≡ d
    make×ChainPath {c} {d} p i .ωChain.xᵢ = p i
    make×ChainPath {c} {d} p i .ωChain.xᵢ-nat j =
      isProp→PathP
        (λ i → ×-set j
          (×-ωType .ωType.πᵢ j (p i (suc j)))
          (p i j))
        (c .ωChain.xᵢ-nat j) (d .ωChain.xᵢ-nat j) i

  ×-ω+Type : ω+Type ℓ
  ×-ω+Type .ω+Type.Xfin = ×-ωType
  ×-ω+Type .ω+Type.Xω = A.Xω × B.Xω
  ×-ω+Type .ω+Type.π (a , b) .ωChain.xᵢ i =
    A.π a .ωChain.xᵢ i , B.π b .ωChain.xᵢ i
  ×-ω+Type .ω+Type.π (a , b) .ωChain.xᵢ-nat i =
    ΣPathP (A.π a .ωChain.xᵢ-nat i , B.π b .ωChain.xᵢ-nat i)
  ×-ω+Type .ω+Type.isLimit = isIsoToIsEquiv
    ( (λ c → invEq (_ , A.isLimit) (record
        { xᵢ = λ i → c .ωChain.xᵢ i .fst
        ; xᵢ-nat = λ i → cong fst (c .ωChain.xᵢ-nat i) })
      , invEq (_ , B.isLimit) (record
        { xᵢ = λ i → c .ωChain.xᵢ i .snd
        ; xᵢ-nat = λ i → cong snd (c .ωChain.xᵢ-nat i) }))
    , (λ c → make×ChainPath
        (funExt λ i → ΣPathP
          ( funExt⁻ (cong ωChain.xᵢ (secEq (_ , A.isLimit) _)) i
          , funExt⁻ (cong ωChain.xᵢ (secEq (_ , B.isLimit) _)) i)))
    , (λ ab → ΣPathP
        ( retEq (_ , A.isLimit) (ab .fst)
        , retEq (_ , B.isLimit) (ab .snd))))

  -- Projections
  π₁-ω+Hom : ω+Hom ×-ω+Type A
  π₁-ω+Hom .ω+Hom.fFin .ωHom.fᵢ _ = fst
  π₁-ω+Hom .ω+Hom.fFin .ωHom.fᵢ-nat _ _ = refl
  π₁-ω+Hom .ω+Hom.fω = fst
  π₁-ω+Hom .ω+Hom.fω-nat _ _ = refl

  π₂-ω+Hom : ω+Hom ×-ω+Type B
  π₂-ω+Hom .ω+Hom.fFin .ωHom.fᵢ _ = snd
  π₂-ω+Hom .ω+Hom.fFin .ωHom.fᵢ-nat _ _ = refl
  π₂-ω+Hom .ω+Hom.fω = snd
  π₂-ω+Hom .ω+Hom.fω-nat _ _ = refl

  -- Pairing
  pair-ω+Hom : ∀ {X : ω+Type ℓ}
    → ω+Hom X A → ω+Hom X B → ω+Hom X ×-ω+Type
  pair-ω+Hom f g .ω+Hom.fFin .ωHom.fᵢ i x =
    f .ω+Hom.fFin .ωHom.fᵢ i x , g .ω+Hom.fFin .ωHom.fᵢ i x
  pair-ω+Hom f g .ω+Hom.fFin .ωHom.fᵢ-nat i x =
    ΣPathP (f .ω+Hom.fFin .ωHom.fᵢ-nat i x
           , g .ω+Hom.fFin .ωHom.fᵢ-nat i x)
  pair-ω+Hom f g .ω+Hom.fω x =
    f .ω+Hom.fω x , g .ω+Hom.fω x
  pair-ω+Hom f g .ω+Hom.fω-nat i x =
    ΣPathP (f .ω+Hom.fω-nat i x , g .ω+Hom.fω-nat i x)

BinProductsω+SET : ∀ {ℓ} → BinProducts (ω+SET ℓ)
BinProductsω+SET {ℓ} ((A , Aset) , (B , Bset)) .vertex =
  ×-ω+Type A B Aset Bset , λ i → isSet× (Aset i) (Bset i)
BinProductsω+SET {ℓ} ((A , Aset) , (B , Bset)) .element =
  π₁-ω+Hom A B Aset Bset , π₂-ω+Hom A B Aset Bset
BinProductsω+SET {ℓ} ((A , Aset) , (B , Bset)) .universal Y+ =
  isIsoToIsEquiv
    ( (λ (f , g) → pair-ω+Hom A B Aset Bset f g)
    , (λ (f , g) → ΣPathP
        ( makeω+HomPath {Y = A} Aset
            (makeωHomPath Aset refl)
        , makeω+HomPath {Y = B} Bset
            (makeωHomPath Bset refl)))
    , (λ a → makeω+HomPath {Y = ×-ω+Type A B Aset Bset}
        (λ i → isSet× (Aset i) (Bset i))
        (makeωHomPath (λ i → isSet× (Aset i) (Bset i))
          refl)))

-- Assembly

ω+SETCC : ∀ ℓ → CartesianCategory (ℓ-suc ℓ) ℓ
ω+SETCC ℓ .CartesianCategory.C = ω+SET ℓ
ω+SETCC ℓ .CartesianCategory.term = Terminalω+SET
ω+SETCC ℓ .CartesianCategory.bp = BinProductsω+SET
