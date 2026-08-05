{-

  The sketch whose models are objects equipped with a binary
  operation.

  The index category has two objects `⟨X⟩` and `⟨X²⟩`, three
  non-identity arrows `p₁ p₂ op : ⟨X²⟩ → ⟨X⟩`, and no equations
  (nothing is composable except with identities).  There is a single
  designated cone, of shape the discrete category on `Bool`, exhibiting
  `⟨X²⟩` as the product of two copies of `⟨X⟩` with projections `p₁`
  and `p₂`.  There are no designated cocones.

  A model in `SET` is therefore a set `A` together with an isomorphism
  `M ⟨X²⟩ ≅ A × A` and a map `M op : M ⟨X²⟩ → A`, i.e. a magma.

-}
module Cubical.Algebra.Sketch.Instances.Magma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Sets

open import Cubical.Algebra.Sketch.Base

private
  variable
    ℓ : Level

open Category
open Functor
open Cone

-- the three generating arrows ⟨X²⟩ → ⟨X⟩
data Gen : Type ℓ-zero where
  p₁ p₂ op : Gen

Gen→ℕ : Gen → ℕ
Gen→ℕ p₁ = 0
Gen→ℕ p₂ = 1
Gen→ℕ op = 2

ℕ→Gen : ℕ → Gen
ℕ→Gen zero = p₁
ℕ→Gen (suc zero) = p₂
ℕ→Gen (suc (suc _)) = op

isSetGen : isSet Gen
isSetGen = isSetRetract Gen→ℕ ℕ→Gen ret isSetℕ
  where
  ret : (g : Gen) → ℕ→Gen (Gen→ℕ g) ≡ g
  ret p₁ = refl
  ret p₂ = refl
  ret op = refl

data MagmaOb : Type ℓ-zero where
  ⟨X⟩ ⟨X²⟩ : MagmaOb

MagmaHom : MagmaOb → MagmaOb → Type ℓ-zero
MagmaHom ⟨X⟩ ⟨X⟩ = Unit
MagmaHom ⟨X⟩ ⟨X²⟩ = ⊥
MagmaHom ⟨X²⟩ ⟨X⟩ = Gen
MagmaHom ⟨X²⟩ ⟨X²⟩ = Unit

MagmaId : {x : MagmaOb} → MagmaHom x x
MagmaId {⟨X⟩} = tt
MagmaId {⟨X²⟩} = tt

MagmaSeq : {x y z : MagmaOb}
         → MagmaHom x y → MagmaHom y z → MagmaHom x z
MagmaSeq {⟨X⟩} {⟨X⟩} {⟨X⟩} f g = tt
MagmaSeq {⟨X⟩} {⟨X⟩} {⟨X²⟩} f g = g
MagmaSeq {⟨X⟩} {⟨X²⟩} ()
MagmaSeq {⟨X²⟩} {⟨X⟩} {⟨X⟩} f g = f
MagmaSeq {⟨X²⟩} {⟨X⟩} {⟨X²⟩} f ()
MagmaSeq {⟨X²⟩} {⟨X²⟩} {⟨X⟩} f g = g
MagmaSeq {⟨X²⟩} {⟨X²⟩} {⟨X²⟩} f g = tt

isSetMagmaHom : {x y : MagmaOb} → isSet (MagmaHom x y)
isSetMagmaHom {⟨X⟩} {⟨X⟩} = isSetUnit
isSetMagmaHom {⟨X⟩} {⟨X²⟩} = isProp→isSet isProp⊥
isSetMagmaHom {⟨X²⟩} {⟨X⟩} = isSetGen
isSetMagmaHom {⟨X²⟩} {⟨X²⟩} = isSetUnit

MagmaInd : Category ℓ-zero ℓ-zero
MagmaInd .ob = MagmaOb
MagmaInd .Hom[_,_] = MagmaHom
MagmaInd .id = MagmaId
MagmaInd ._⋆_ = MagmaSeq
MagmaInd .⋆IdL {⟨X⟩} {⟨X⟩} f = refl
MagmaInd .⋆IdL {⟨X⟩} {⟨X²⟩} ()
MagmaInd .⋆IdL {⟨X²⟩} {⟨X⟩} f = refl
MagmaInd .⋆IdL {⟨X²⟩} {⟨X²⟩} f = refl
MagmaInd .⋆IdR {⟨X⟩} {⟨X⟩} f = refl
MagmaInd .⋆IdR {⟨X⟩} {⟨X²⟩} ()
MagmaInd .⋆IdR {⟨X²⟩} {⟨X⟩} f = refl
MagmaInd .⋆IdR {⟨X²⟩} {⟨X²⟩} f = refl
MagmaInd .⋆Assoc {⟨X⟩} {⟨X⟩} {⟨X⟩} {⟨X⟩} f g h = refl
MagmaInd .⋆Assoc {⟨X⟩} {⟨X⟩} {⟨X⟩} {⟨X²⟩} f g ()
MagmaInd .⋆Assoc {⟨X⟩} {⟨X⟩} {⟨X²⟩} {w} f () h
MagmaInd .⋆Assoc {⟨X⟩} {⟨X²⟩} {z} {w} () g h
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X⟩} {⟨X⟩} {⟨X⟩} f g h = refl
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X⟩} {⟨X⟩} {⟨X²⟩} f g ()
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X⟩} {⟨X²⟩} {w} f () h
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X²⟩} {⟨X⟩} {⟨X⟩} f g h = refl
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X²⟩} {⟨X⟩} {⟨X²⟩} f g ()
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X²⟩} {⟨X²⟩} {⟨X⟩} f g h = refl
MagmaInd .⋆Assoc {⟨X²⟩} {⟨X²⟩} {⟨X²⟩} {⟨X²⟩} f g h = refl
MagmaInd .isSetHom = isSetMagmaHom

-- the shape of the single designated cone: two discrete points
Two : Category ℓ-zero ℓ-zero
Two = DiscreteCategory (Bool , isSet→isGroupoid isSetBool)

-- the constant diagram at ⟨X⟩
X² : Functor Two MagmaInd
X² = DiscFunc (λ _ → ⟨X⟩)

-- the two projections
proj : Bool → MagmaHom ⟨X²⟩ ⟨X⟩
proj false = p₁
proj true = p₂

projCone : Cone X² ⟨X²⟩
projCone .Cone.coneOut = proj
projCone .Cone.coneOutCommutes e = cong proj e

MagmaSketch : Sketch ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
MagmaSketch .Sketch.ind = MagmaInd
MagmaSketch .Sketch.LIdx = Unit
MagmaSketch .Sketch.LShape _ = Two
MagmaSketch .Sketch.LDiag _ = X²
MagmaSketch .Sketch.LVtx _ = ⟨X²⟩
MagmaSketch .Sketch.LCone _ = projCone
MagmaSketch .Sketch.CIdx = ⊥
MagmaSketch .Sketch.CShape ()
MagmaSketch .Sketch.CDiag ()
MagmaSketch .Sketch.CVtx ()
MagmaSketch .Sketch.CCone ()

-- Models of `MagmaSketch` in `SET` are magmas: the carrier is the
-- image of ⟨X⟩, and the binary operation is obtained by pairing into
-- the (limit) object `M ⟨X²⟩` and then applying `M op`.
module _ (Mo : Model MagmaSketch (SET ℓ)) where
  private
    M = Mo .fst
    isLim = Mo .snd .fst tt

  Carrier : hSet ℓ
  Carrier = M .F-ob ⟨X⟩

  A : Type ℓ
  A = ⟨ Carrier ⟩

  Sq : hSet ℓ
  Sq = (A × A) , isSet× (Carrier .snd) (Carrier .snd)

  pairOut : Bool → (A × A → A)
  pairOut false = fst
  pairOut true = snd

  pairCone : Cone (funcComp M X²) Sq
  pairCone .coneOut = pairOut
  pairCone .coneOutCommutes {u} e =
    cong (λ (h : A → A) (x : A × A) → h (pairOut u x))
         (M .F-id {⟨X⟩})
    ∙ cong pairOut e

  pair : A × A → ⟨ M .F-ob ⟨X²⟩ ⟩
  pair = isLim Sq pairCone .fst .fst

  magmaOp : A → A → A
  magmaOp a b = M .F-hom {⟨X²⟩} {⟨X⟩} op (pair (a , b))

  -- the two projections really are the projections
  pair-fst : (a b : A) → M .F-hom {⟨X²⟩} {⟨X⟩} p₁ (pair (a , b)) ≡ a
  pair-fst a b = funExt⁻ (isLim Sq pairCone .fst .snd false) (a , b)

  pair-snd : (a b : A) → M .F-hom {⟨X²⟩} {⟨X⟩} p₂ (pair (a , b)) ≡ b
  pair-snd a b = funExt⁻ (isLim Sq pairCone .fst .snd true) (a , b)

-- Conversely, every set with a binary operation is a model.
module _ {A : hSet ℓ} (m : ⟨ A ⟩ → ⟨ A ⟩ → ⟨ A ⟩) where
  A² : hSet ℓ
  A² = (⟨ A ⟩ × ⟨ A ⟩) , isSet× (A .snd) (A .snd)

  magmaOb : MagmaOb → hSet ℓ
  magmaOb ⟨X⟩ = A
  magmaOb ⟨X²⟩ = A²

  magmaHom : {x y : MagmaOb} → MagmaHom x y → ⟨ magmaOb x ⟩ → ⟨ magmaOb y ⟩
  magmaHom {⟨X⟩} {⟨X⟩} f = idfun _
  magmaHom {⟨X⟩} {⟨X²⟩} ()
  magmaHom {⟨X²⟩} {⟨X⟩} p₁ = fst
  magmaHom {⟨X²⟩} {⟨X⟩} p₂ = snd
  magmaHom {⟨X²⟩} {⟨X⟩} op p = m (p .fst) (p .snd)
  magmaHom {⟨X²⟩} {⟨X²⟩} f = idfun _

  magmaFunctor : Functor MagmaInd (SET ℓ)
  magmaFunctor .F-ob = magmaOb
  magmaFunctor .F-hom = magmaHom
  magmaFunctor .F-id {⟨X⟩} = refl
  magmaFunctor .F-id {⟨X²⟩} = refl
  magmaFunctor .F-seq {⟨X⟩} {⟨X⟩} {⟨X⟩} f g = refl
  magmaFunctor .F-seq {⟨X⟩} {⟨X⟩} {⟨X²⟩} f ()
  magmaFunctor .F-seq {⟨X⟩} {⟨X²⟩} ()
  magmaFunctor .F-seq {⟨X²⟩} {⟨X⟩} {⟨X⟩} f g = refl
  magmaFunctor .F-seq {⟨X²⟩} {⟨X⟩} {⟨X²⟩} f ()
  magmaFunctor .F-seq {⟨X²⟩} {⟨X²⟩} {⟨X⟩} f g = refl
  magmaFunctor .F-seq {⟨X²⟩} {⟨X²⟩} {⟨X²⟩} f g = refl

  magmaIsLim : isLimCone (funcComp magmaFunctor X²) A²
                         (F-cone magmaFunctor projCone)
  magmaIsLim c cc =
    uniqueExists
      (λ x → cc .coneOut false x , cc .coneOut true x)
      isConeMorPair
      (isPropIsConeMor cc (F-cone magmaFunctor projCone))
      uniq
    where
    isConeMorPair : isConeMor cc (F-cone magmaFunctor projCone) _
    isConeMorPair false = refl
    isConeMorPair true = refl

    uniq : (g : SET ℓ [ c , A² ])
         → isConeMor cc (F-cone magmaFunctor projCone) g
         → (λ x → cc .coneOut false x , cc .coneOut true x) ≡ g
    uniq g p = funExt λ x →
      ΣPathP (sym (funExt⁻ (p false) x) , sym (funExt⁻ (p true) x))

  magmaModel : Model MagmaSketch (SET ℓ)
  magmaModel .fst = magmaFunctor
  magmaModel .snd .fst _ = magmaIsLim
  magmaModel .snd .snd ()

  -- the operation read back off `magmaModel` is the one we started
  -- with, so `magmaOp` really does recover the magma structure
  pairMagmaModel : pair magmaModel ≡ idfun (⟨ A ⟩ × ⟨ A ⟩)
  pairMagmaModel =
    cong fst (magmaIsLim (Sq magmaModel) (pairCone magmaModel) .snd
                         (idfun _ , isConeMorId'))
    where
    isConeMorId' : isConeMor (pairCone magmaModel)
                             (F-cone magmaFunctor projCone) (idfun _)
    isConeMorId' false = refl
    isConeMorId' true = refl

  magmaOp≡ : (a b : ⟨ A ⟩) → magmaOp magmaModel a b ≡ m a b
  magmaOp≡ a b = cong (λ h → magmaHom {⟨X²⟩} {⟨X⟩} op (h (a , b)))
                      pairMagmaModel
