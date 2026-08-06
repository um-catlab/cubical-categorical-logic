{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.IdentityExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sigma.Properties
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
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC
open import Gluing.BiCartesianClosedCategory.BinaryLogicalRelation

open Functor
open Section

private
  variable
    ℓ ℓQ ℓQ' : Level

data BaseFree {O : Type ℓQ} : BiCCCExpr O → Type ℓQ where
  ⊤-free : BaseFree ⊤
  ⊥-free : BaseFree ⊥
  _×-free_ : ∀ {A B} → BaseFree A → BaseFree B → BaseFree (A × B)
  _+-free_ : ∀ {A B} → BaseFree A → BaseFree B → BaseFree (A + B)
  _⇒-free_ : ∀ {A B} → BaseFree A → BaseFree B → BaseFree (A ⇒ B)


module _
  (Q : +×⇒Quiver ℓQ ℓQ')
  (I J : Interpretation Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}))
  (generators :
    LogicalRelationGenerators Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) I J)
  where

  private
    Left = interpretation Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) I
    Right = interpretation Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) J
    LR =
      logicalRelation Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ})
        I J generators
    LRMotive =
      FreeBiCCC.elimLocalMotive Q
        (pointwise Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) I J)
        (EqSETᴰBCCCⱽ {ℓ})

    module LRMotive = BiCartesianClosedCategoryᴰ LRMotive
    module RelCat = Categoryᴰ LRMotive.Cᴰ
    module Syntax = BiCartesianClosedCategory
      (FreeBiCCC.FreeBiCartesianClosedCategory Q)

  baseFreeInterpretation≡ :
    ∀ {A} → BaseFree A →
      ⟨ Left .fst .F-ob A ⟩ ≡ ⟨ Right .fst .F-ob A ⟩
  baseFreeInterpretation≡ ⊤-free = refl
  baseFreeInterpretation≡ ⊥-free = refl
  baseFreeInterpretation≡ (p ×-free q) i =
    Σ (baseFreeInterpretation≡ p i)
      (λ _ → baseFreeInterpretation≡ q i)
  baseFreeInterpretation≡ (p +-free q) i =
    baseFreeInterpretation≡ p i ⊎ baseFreeInterpretation≡ q i
  baseFreeInterpretation≡ (p ⇒-free q) i =
    baseFreeInterpretation≡ p i → baseFreeInterpretation≡ q i
  open import Cubical.Functions.FunExtEquiv

  mutual
    identityExtension :
      ∀ {A} → (free : BaseFree A) →
      (x : ⟨ Left .fst .F-ob A ⟩)
      (y : ⟨ Right .fst .F-ob A ⟩) →
      ⟨ LR .F-obᴰ A (x , y) ⟩ →
      PathP (λ i → baseFreeInterpretation≡ free i) x y
    identityExtension {A = ⊤} ⊤-free tt* tt* _ = refl
    identityExtension {A = ⊥} ⊥-free ()
    identityExtension {A = A × B} (p ×-free q) (x , y) (x' , y')
      (rx , ry) =
      ΣPathP
        ( identityExtension {A = A} p x x' rx
        , identityExtension {A = B} q y y' ry)
    identityExtension {A = A + B} (p +-free q) (inl x) (inl y) = forward
      where
      forward : ⟨ LR .F-obᴰ (A + B) (inl x , inl y) ⟩ → _
      forward (inl ((a , b) , e , r)) i =
        inl
          (identityExtension {A = A} p x y
            (subst (λ z → ⟨ LR .F-obᴰ A z ⟩)
              (ΣPathP
                ( lower (⊎Path.encode _ _ (cong fst e))
                , lower (⊎Path.encode _ _ (cong snd e))))
              r)
            i)
      forward (inr ((_ , _) , e , _)) = 
        Empty.rec (lower (⊎Path.encode _ _ (cong fst e)))
    identityExtension {A = A + B} (p +-free q) (inr x) (inr y) = forward
      where
      forward : ⟨ LR .F-obᴰ (A + B) (inr x , inr y) ⟩ → _
      forward (inl ((_ , _) , e , _)) = 
        Empty.rec (lower (⊎Path.encode _ _ (cong fst e)))
      forward (inr ((a , b) , e , r)) i =
        inr
          (identityExtension {A = B} q x y
            (subst (λ z → ⟨ LR .F-obᴰ B z ⟩)
              (ΣPathP
                ( lower (⊎Path.encode _ _ (cong fst e))
                , lower (⊎Path.encode _ _ (cong snd e))))
              r)
            i)
    identityExtension {A = A + B} (p +-free q) (inl x) (inr y) r =
      Empty.rec (sourceEmpty r)
      where
      sourceEmpty : ⟨ LR .F-obᴰ (A + B) (inl x , inr y) ⟩ → Empty.⊥
      sourceEmpty (inl ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong snd e))
      sourceEmpty (inr ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong fst e))
    identityExtension {A = A + B} (p +-free q) (inr x) (inl y) r =
      Empty.rec (sourceEmpty r)
      where
      sourceEmpty : ⟨ LR .F-obᴰ (A + B) (inr x , inl y) ⟩ → Empty.⊥
      sourceEmpty (inl ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong fst e))
      sourceEmpty (inr ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong snd e))
    identityExtension {A = A₀ ⇒ B₀} (A ⇒-free B) f g rel =
      funExtDep λ {x}{y} p →
        identityExtension B (f x) (g y)
          (LR .F-homᴰ (FreeBiCCC.eval' Q)
            ((f , x) , (g , y))
            (rel , identityExtension⁻ A x y p))

    identityExtension⁻ :
      ∀ {A} → (free : BaseFree A) →
      (x : ⟨ Left .fst .F-ob A ⟩)
      (y : ⟨ Right .fst .F-ob A ⟩) →
      PathP (λ i → baseFreeInterpretation≡ free i) x y →
      ⟨ LR .F-obᴰ A (x , y) ⟩
    identityExtension⁻ {A = ⊤} ⊤-free tt* tt* _ = tt*
    identityExtension⁻ {A = ⊥} ⊥-free ()
    identityExtension⁻ {A = A × B} (p ×-free q) (x , y) (x' , y') r =
      identityExtension⁻ {A = A} p x x' (PathPΣ.fst r) ,
      identityExtension⁻ {A = B} q y y' (λ i → r i .snd)
    identityExtension⁻ {A = A + B} (p +-free q) (inl x) (inl y) r =
      inl ((x , y) , refl ,
        identityExtension⁻ {A = A} p x y (PathP-inl-inj r))
    identityExtension⁻ {A = A + B} (p +-free q) (inr x) (inr y) r =
      inr ((x , y) , refl ,
        identityExtension⁻ {A = B} q x y (PathP-inr-inj r))
    identityExtension⁻ {A = A + B} (p +-free q) (inl x) (inr y) r =
      Empty.rec (PathP-inl≢inr r)
    identityExtension⁻ {A = A + B} (p +-free q) (inr x) (inl y) r =
      Empty.rec (PathP-inr≢inl r)
    identityExtension⁻ {A = A₀ ⇒ B₀} (A ⇒-free B) f g r =
      LRMotive.λᴰ (body r) (f , g) refl
      where
      Point : LRMotive.Cᴰ.ob[ A₀ ⇒ B₀ ]
      Point hk =
        (hk ≡ (f , g)) ,
        isProp→isSet (pointwise Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) I J
          .fst .F-ob (A₀ ⇒ B₀) .snd hk (f , g))

      module Point×A = UUP.BinProductᴰNotation LRMotive.Cᴰ
        (Syntax.bp ((A₀ ⇒ B₀) , A₀))
        (LRMotive.bpᴰ Point (LR .F-obᴰ A₀))

      body : PathP (λ i → baseFreeInterpretation≡ (A ⇒-free B) i) f g →
        Categoryᴰ.Hom[_][_,_] LRMotive.Cᴰ (FreeBiCCC.eval' Q)
        (LRMotive.bpᴰ Point (LR .F-obᴰ A₀) .fst) (LR .F-obᴰ B₀)
      body r ((h , x) , (k , y)) zr =
        subst
          (λ hk → ⟨ LR .F-obᴰ B₀ (hk .fst x , hk .snd y) ⟩)
          (sym (Point×A.πᴰ₁ ((h , x) , (k , y)) zr))
          (identityExtension⁻ {A = B₀} B (f x) (g y)
            (invEq funExtDepEquiv r
              (identityExtension {A = A₀} A x y
                (Point×A.πᴰ₂ ((h , x) , (k , y)) zr))))

  identityExtensionHom :
    ∀ {A B} (freeA : BaseFree A) (freeB : BaseFree B)
      (e : FreeBiCCC.Expr Q A B)
      (x : ⟨ Left .fst .F-ob A ⟩)
      (y : ⟨ Right .fst .F-ob A ⟩) →
    PathP (λ i → baseFreeInterpretation≡ freeA i) x y →
    PathP (λ i → baseFreeInterpretation≡ freeB i)
      (Left .fst .F-hom e x) (Right .fst .F-hom e y)
  identityExtensionHom freeA freeB e x y p =
    identityExtension freeB _ _
      (LR .F-homᴰ e (x , y) (identityExtension⁻ freeA x y p))
