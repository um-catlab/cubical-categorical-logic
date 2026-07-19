-- Lists and thinnings as a non-thin direct category
--
-- McBride, "Everybody's Got To Be Somewhere"
-- https://arxiv.org/abs/1807.04085
module Cubical.Categories.Direct.Instances.Thinnings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order.Recursive using (_≤_ ; _<_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

private
  variable
    ℓ : Level

data Thin {A : Type ℓ} : List A → List A → Type ℓ where
  done : Thin [] []
  keep : ∀ {xs ys} (a : A) → Thin xs ys → Thin (a ∷ xs) (a ∷ ys)
  skip : ∀ {xs ys} (a : A) → Thin xs ys → Thin xs (a ∷ ys)

module _ {A : Type ℓ} where
  private
    variable
      xs ys zs : List A

  idThin : (xs : List A) → Thin xs xs
  idThin []       = done
  idThin (a ∷ xs) = keep a (idThin xs)

  seqThin : Thin xs ys → Thin ys zs → Thin xs zs
  seqThin θ          (skip a φ) = skip a (seqThin θ φ)
  seqThin (keep _ θ) (keep a φ) = keep a (seqThin θ φ)
  seqThin (skip _ θ) (keep a φ) = skip a (seqThin θ φ)
  seqThin done       done       = done

  seqIdL : (θ : Thin xs ys) → seqThin (idThin xs) θ ≡ θ
  seqIdL done       = refl
  seqIdL (keep a θ) = cong (keep a) (seqIdL θ)
  seqIdL (skip a θ) = cong (skip a) (seqIdL θ)

  seqIdR : (θ : Thin xs ys) → seqThin θ (idThin ys) ≡ θ
  seqIdR done       = refl
  seqIdR (keep a θ) = cong (keep a) (seqIdR θ)
  seqIdR (skip a θ) = cong (skip a) (seqIdR θ)

  seqAssoc : {ws : List A} (θ : Thin xs ys) (φ : Thin ys zs) (ψ : Thin zs ws)
           → seqThin (seqThin θ φ) ψ ≡ seqThin θ (seqThin φ ψ)
  seqAssoc θ          φ          (skip a ψ) = cong (skip a) (seqAssoc θ φ ψ)
  seqAssoc (keep _ θ) (keep _ φ) (keep a ψ) = cong (keep a) (seqAssoc θ φ ψ)
  seqAssoc (skip _ θ) (keep _ φ) (keep a ψ) = cong (skip a) (seqAssoc θ φ ψ)
  seqAssoc θ          (skip _ φ) (keep a ψ) = cong (skip a) (seqAssoc θ φ ψ)
  seqAssoc done       done       done       = refl

  isPropEqList : isSet A → (xs ys : List A) → isProp (xs Eq.≡ ys)
  isPropEqList sA xs ys = isOfHLevelRetract 1
    Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath
    (isOfHLevelList 0 sA xs ys)

  private
    ThinRep : List A → List A → Type _
    ThinRep xs []       = xs Eq.≡ []
    ThinRep xs (y ∷ ys) =
      (Σ[ xs' ∈ List A ] (xs Eq.≡ (y ∷ xs')) × ThinRep xs' ys) ⊎ ThinRep xs ys

    toRep : Thin xs ys → ThinRep xs ys
    toRep done              = Eq.refl
    toRep (keep {xs = xs} a θ) = inl (xs , Eq.refl , toRep θ)
    toRep (skip a θ)           = inr (toRep θ)

    fromRep : (xs ys : List A) → ThinRep xs ys → Thin xs ys
    fromRep .[] [] Eq.refl = done
    fromRep .(y ∷ xs') (y ∷ ys) (inl (xs' , Eq.refl , r)) =
      keep y (fromRep xs' ys r)
    fromRep xs (y ∷ ys) (inr r) = skip y (fromRep xs ys r)

    fromRep-toRep : (θ : Thin xs ys) → fromRep xs ys (toRep θ) ≡ θ
    fromRep-toRep done       = refl
    fromRep-toRep (keep a θ) = cong (keep a) (fromRep-toRep θ)
    fromRep-toRep (skip a θ) = cong (skip a) (fromRep-toRep θ)

    isSetThinRep : isSet A → (xs ys : List A) → isSet (ThinRep xs ys)
    isSetThinRep sA xs []       = isProp→isSet (isPropEqList sA xs [])
    isSetThinRep sA xs (y ∷ ys) = isSet⊎
      (isSetΣ (isOfHLevelList 0 sA) λ xs' → isSet×
        (isProp→isSet (isPropEqList sA xs (y ∷ xs')))
        (isSetThinRep sA xs' ys))
      (isSetThinRep sA xs ys)

  isSetThin : isSet A → isSet (Thin xs ys)
  isSetThin sA =
    isOfHLevelRetract 2 toRep (fromRep _ _) fromRep-toRep
      (isSetThinRep sA _ _)

  -- this category is genuinely not thin
  keep≢skip : {a : A} {θ : Thin xs ys} {φ : Thin (a ∷ xs) ys}
            → keep a θ ≡ skip a φ → ⊥
  keep≢skip {a = a} e = subst disc (cong toRep e) tt
    where
      disc : ThinRep (a ∷ xs) (a ∷ ys) → Type
      disc (inl _) = Unit
      disc (inr _) = ⊥

  thin-length : Thin xs ys → length xs ≤ length ys
  thin-length done       = tt
  thin-length (keep a θ) = thin-length θ
  thin-length (skip {xs = xs} {ys = ys} a θ) =
    ≤-up {length xs} {length ys} (thin-length θ)
    where
      ≤-up : ∀ {m n} → m ≤ n → m ≤ suc n
      ≤-up {zero}          _  = tt
      ≤-up {suc m} {zero}  le = ⊥.rec le
      ≤-up {suc m} {suc n} le = ≤-up {m} {n} le

  thin≤ : (θ : Thin xs ys) → (length xs < length ys) ⊎ (xs Eq.≡ ys)
  thin≤ done       = inr Eq.refl
  thin≤ (keep a θ) = Sum.map (λ lt → lt) (Eq.ap (a ∷_)) (thin≤ θ)
  thin≤ (skip a θ) = inl (thin-length θ)

Var : {A : Type ℓ} → List A → Type
Var []       = ⊥
Var (a ∷ xs) = Unit ⊎ Var xs

pattern vz   = inl tt
pattern vs x = inr x

module _ {A : Type ℓ} where
  isSetVar : (xs : List A) → isSet (Var xs)
  isSetVar []       = isProp→isSet ⊥.isProp⊥
  isSetVar (a ∷ xs) = isSet⊎ (isProp→isSet isPropUnit) (isSetVar xs)

  delete : (xs : List A) → Var xs → List A
  delete (a ∷ xs) vz     = xs
  delete (a ∷ xs) (vs x) = a ∷ delete xs x

  faceThin : {xs : List A} (x : Var xs) → Thin (delete xs x) xs
  faceThin {xs = a ∷ xs} vz     = skip a (idThin xs)
  faceThin {xs = a ∷ xs} (vs x) = keep a (faceThin x)

  length-delete : (xs : List A) (x : Var xs)
                → suc (length (delete xs x)) ≡ length xs
  length-delete (a ∷ xs) vz     = refl
  length-delete (a ∷ xs) (vs x) = cong suc (length-delete xs x)

  thick : {xs : List A} (x y : Var xs) → (x ≡ y) ⊎ Var (delete xs x)
  thick {xs = a ∷ xs} vz     vz     = inl refl
  thick {xs = a ∷ xs} vz     (vs y) = inr y
  thick {xs = a ∷ xs} (vs x) vz     = inr vz
  thick {xs = a ∷ xs} (vs x) (vs y) = Sum.map (cong inr) inr (thick x y)

module _ (A : Type ℓ) (isSetA : isSet A) where
  open Category

  THIN : Category ℓ ℓ
  THIN .ob        = List A
  THIN .Hom[_,_]  = Thin
  THIN .id {xs}   = idThin xs
  THIN ._⋆_       = seqThin
  THIN .⋆IdL      = seqIdL
  THIN .⋆IdR      = seqIdR
  THIN .⋆Assoc    = seqAssoc
  THIN .isSetHom  = isSetThin isSetA

  ThinWFOrder : WFOrder ℓ ℓ-zero
  ThinWFOrder = pullbackWFOrder ℕWFOrder (isOfHLevelList 0 isSetA) length

  ThinDirect : DirectStr {C = THIN} ThinWFOrder
  ThinDirect = mkDirectStr ThinWFOrder (λ xs → xs) thin≤
