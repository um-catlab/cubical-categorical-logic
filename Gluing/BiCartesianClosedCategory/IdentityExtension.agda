{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.IdentityExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sigma using () renaming (_×_ to _Σ×_)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Sum.More
open import Cubical.Data.Unit

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV
import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties as UUP
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation

open Functor
open Section

private
  variable
    ℓ ℓQ ℓQ' : Level

module _
  (Q : +×⇒Quiver ℓQ ℓQ')
  (I J : Interpretation Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}))
  (generators :
    LogicalRelationGenerators Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}) I J)
  where

  private
    Left = interpretation Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}) I
    Right = interpretation Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}) J
    LR =
      logicalRelation Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ})
        I J generators

    fromPull : ∀ {X Y : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {R} {z}
      → Fib ℓ (Pull f R) z → Fib ℓ R (f z)
    fromPull {f = f} ((_ , w , q') , q) = w , q' ∙ cong f q

    toPull : ∀ {X Y : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {R} {z}
      → Fib ℓ R (f z) → Fib ℓ (Pull f R) z
    toPull {z = z} u = (z , u) , refl

    adjust : ∀ {Y : hSet ℓ} {R} {y y' : ⟨ Y ⟩}
      → Fib ℓ {Y = Y} R y → y ≡ y' → Fib ℓ R y'
    adjust (u , p) q = u , p ∙ q

    fromPullAt : ∀ {X Y : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {R} {w z}
      → Fib ℓ (Pull f R) w → w ≡ z → Fib ℓ R (f z)
    fromPullAt {f = f} r p = adjust (fromPull r) (cong f p)

    inlPath : ∀ {ℓa ℓb} {X X' : Type ℓa} {Y Y' : Type ℓb} {a x b y}
      → Path ((X ⊎ Y) Σ× (X' ⊎ Y')) (inl a , inl b) (inl x , inl y)
      → (a , b) ≡ (x , y)
    inlPath e = ΣPathP
      ( lower (⊎Path.encode _ _ (cong fst e))
      , lower (⊎Path.encode _ _ (cong snd e)))

    inrPath : ∀ {ℓa ℓb} {X X' : Type ℓa} {Y Y' : Type ℓb} {a x b y}
      → Path ((X ⊎ Y) Σ× (X' ⊎ Y')) (inr a , inr b) (inr x , inr y)
      → (a , b) ≡ (x , y)
    inrPath e = ΣPathP
      ( lower (⊎Path.encode _ _ (cong fst e))
      , lower (⊎Path.encode _ _ (cong snd e)))

    LRMotive =
      FreeBiCCC.elimLocalMotive Q
        (pointwise Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}) I J)
        (SETCodBCCCⱽ {ℓ})

    module LRMotive = BiCartesianClosedCategoryᴰ LRMotive
    module Syntax = BiCartesianClosedCategory
      (FreeBiCCC.FreeBiCartesianClosedCategory Q)

  private
    embedClosed : BiCCCExpr Empty.⊥ → BiCCCExpr (Q .+×⇒Quiver.ob)
    embedClosed = recBiCCCExpr λ ()

  closedInterpretation≡ :
    (A : BiCCCExpr Empty.⊥) →
    ⟨ Left .fst .F-ob (embedClosed A) ⟩ ≡
    ⟨ Right .fst .F-ob (embedClosed A) ⟩
  closedInterpretation≡ (↑ ())
  closedInterpretation≡ (A × B) i =
    Σ (closedInterpretation≡ A i)
      (λ _ → closedInterpretation≡ B i)
  closedInterpretation≡ (A + B) i =
    closedInterpretation≡ A i ⊎ closedInterpretation≡ B i
  closedInterpretation≡ (A ⇒ B) i =
    closedInterpretation≡ A i → closedInterpretation≡ B i
  closedInterpretation≡ ⊥ = refl
  closedInterpretation≡ ⊤ = refl

  identityExtensionFib :
    (A : BiCCCExpr Empty.⊥) →
    {x : ⟨ Left .fst .F-ob (embedClosed A) ⟩}
    {y : ⟨ Right .fst .F-ob (embedClosed A) ⟩} →
    Fib ℓ (LR .F-obᴰ (embedClosed A)) (x , y) →
    PathP (λ i → closedInterpretation≡ A i) x y

  identityExtension⁻ :
    (A : BiCCCExpr Empty.⊥) →
    (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
    (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
    PathP (λ i → closedInterpretation≡ A i) x y →
    ⟨ LR .F-obᴰ (embedClosed A) (x , y) ⟩

  identityExtensionFib (↑ ())
  identityExtensionFib ⊤ {tt*} {tt*} _ = refl
  identityExtensionFib ⊥ {()}
  identityExtensionFib (A × B) ((_ , rx , ry) , p) =
    ΣPathP
      ( identityExtensionFib A (fromPullAt rx p)
      , identityExtensionFib B (fromPullAt ry p))
  identityExtensionFib (A + B) {inl x} {inl y}
    ((_ , inl (((a , b) , r) , e)) , p) i =
    inl (identityExtensionFib A (((a , b) , r) , inlPath (e ∙ p)) i)
  identityExtensionFib (A + B) {inl x} {inl y} ((_ , inr (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong fst (e ∙ p))))
  identityExtensionFib (A + B) {inr x} {inr y} ((_ , inl (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong fst (e ∙ p))))
  identityExtensionFib (A + B) {inr x} {inr y}
    ((_ , inr (((a , b) , r) , e)) , p) i =
    inr (identityExtensionFib B (((a , b) , r) , inrPath (e ∙ p)) i)
  identityExtensionFib (A + B) {inl x} {inr y} ((_ , inl (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong snd (e ∙ p))))
  identityExtensionFib (A + B) {inl x} {inr y} ((_ , inr (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong fst (e ∙ p))))
  identityExtensionFib (A + B) {inr x} {inl y} ((_ , inl (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong fst (e ∙ p))))
  identityExtensionFib (A + B) {inr x} {inl y} ((_ , inr (_ , e)) , p) =
    Empty.rec (lower (⊎Path.encode _ _ (cong snd (e ∙ p))))
  identityExtensionFib (A ⇒ B) ((w , rel) , p) =
    funExtDep λ {x}{y} q →
      identityExtensionFib B
        (adjust
          (pt ℓ (LR .F-homᴰ (FreeBiCCC.eval' Q))
            (((w .fst , x) , (w .snd , y))
            , toPull ((_ , rel) , refl)
            , toPull ((_ , identityExtension⁻ A x y q) , refl)))
          (cong (λ h → h .fst x , h .snd y) p))

  identityExtension :
    (A : BiCCCExpr Empty.⊥) →
    (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
    (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
    ⟨ LR .F-obᴰ (embedClosed A) (x , y) ⟩ →
    PathP (λ i → closedInterpretation≡ A i) x y
  identityExtension A x y r = identityExtensionFib A ((_ , r) , refl)

  identityExtension⁻ (↑ ())
  identityExtension⁻ ⊤ tt* tt* _ = tt*
  identityExtension⁻ ⊥ ()
  identityExtension⁻ (A × B) (x , y) (x' , y') r =
    toPull ((_ , identityExtension⁻ A x x' (PathPΣ.fst r)) , refl) ,
    toPull ((_ , identityExtension⁻ B y y' (λ i → r i .snd)) , refl)
  identityExtension⁻ (A + B) (inl x) (inl y) r =
    inl (((x , y) , identityExtension⁻ A x y (PathP-inl-inj r)) , refl)
  identityExtension⁻ (A + B) (inr x) (inr y) r =
    inr (((x , y) , identityExtension⁻ B x y (PathP-inr-inj r)) , refl)
  identityExtension⁻ (A + B) (inl x) (inr y) r =
    Empty.rec (PathP-inl≢inr r)
  identityExtension⁻ (A + B) (inr x) (inl y) r =
    Empty.rec (PathP-inr≢inl r)
  identityExtension⁻ (A ⇒ B) f g r =
    subst (λ hk → ⟨ LR .F-obᴰ (embedClosed (A ⇒ B)) hk ⟩) (lamPt .snd)
      (lamPt .fst .snd)
    where
    Point : LRMotive.Cᴰ.ob[ embedClosed (A ⇒ B) ]
    Point hk =
      (hk ≡ (f , g)) ,
      isProp→isSet (pointwise Q (SETBiCCC {ℓ}) (SETCodBCCCⱽ {ℓ}) I J
        .fst .F-ob (embedClosed (A ⇒ B)) .snd hk (f , g))

    module Point×A = UUP.BinProductᴰNotation LRMotive.Cᴰ
      (Syntax.bp (embedClosed (A ⇒ B) , embedClosed A))
      (LRMotive.bpᴰ Point (LR .F-obᴰ (embedClosed A)))

    body : Categoryᴰ.Hom[_][_,_] LRMotive.Cᴰ (FreeBiCCC.eval' Q)
      (LRMotive.bpᴰ Point (LR .F-obᴰ (embedClosed A)) .fst)
      (LR .F-obᴰ (embedClosed B))
    body = mk ℓ λ (((h , x) , (k , y)) , zr) →
      let ((_ , e) , q) = pt ℓ Point×A.πᴰ₁ (((h , x) , (k , y)) , zr)
      in (_ , identityExtension⁻ B (f x) (g y)
            (invEq funExtDepEquiv r
              (identityExtensionFib A
                (pt ℓ Point×A.πᴰ₂ (((h , x) , (k , y)) , zr)))))
         , cong (λ hk → hk .fst x , hk .snd y) (sym e ∙ q)

    lamPt = pt ℓ (LRMotive.λᴰ {f = FreeBiCCC.eval' Q} body) ((f , g) , refl)

  identityExtensionHom :
    (A B : BiCCCExpr Empty.⊥)
      (e : FreeBiCCC.Expr Q (embedClosed A) (embedClosed B))
      (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
      (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
    PathP (λ i → closedInterpretation≡ A i) x y →
    PathP (λ i → closedInterpretation≡ B i)
      (Left .fst .F-hom e x) (Right .fst .F-hom e y)
  identityExtensionHom A B e x y p =
    identityExtensionFib B
      (pt ℓ (LR .F-homᴰ e) ((x , y) , identityExtension⁻ A x y p))
