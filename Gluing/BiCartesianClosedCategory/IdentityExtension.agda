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

  identityExtension :
    ∀ {A} → (free : BaseFree A) →
    (x : ⟨ Left .fst .F-ob A ⟩)
    (y : ⟨ Right .fst .F-ob A ⟩) →
      ⟨ LR .F-obᴰ A (x , y) ⟩ ≃
      PathP (λ i → baseFreeInterpretation≡ free i) x y
  identityExtension {A = ⊤} ⊤-free tt* tt* =
    propBiimpl→Equiv
      isPropUnit*
      (isOfHLevelPathP' 1 isSetUnit* tt* tt*)
      (λ _ → refl)
      (λ _ → tt*)
  identityExtension {A = ⊥} ⊥-free ()
  identityExtension {A = A × B} (p ×-free q) (x , y) (x' , y') =
    propBiimpl→Equiv
      (isProp×
        (isOfHLevelRespectEquiv 1
          (invEquiv (identityExtension {A = A} p x x'))
          (isOfHLevelPathP' 1
            (Right .fst .F-ob A .snd) x x'))
        (isOfHLevelRespectEquiv 1
          (invEquiv (identityExtension {A = B} q y y'))
          (isOfHLevelPathP' 1
            (Right .fst .F-ob B .snd) y y')))
      (isOfHLevelPathP' 1
        (Right .fst .F-ob (A × B) .snd)
        (x , y) (x' , y'))
      (λ (rx , ry) →
        ΣPathP
          ( identityExtension {A = A} p x x' .fst rx
          , identityExtension {A = B} q y y' .fst ry))
      (λ r →
        invEq (identityExtension {A = A} p x x') (PathPΣ.fst r) ,
        invEq (identityExtension {A = B} q y y') (λ i → r i .snd))
  identityExtension {A = A + B} (p +-free q) (inl x) (inl y) =
    propBiimpl→Equiv
      sourceProp
      (isOfHLevelPathP' 1 (Right .fst .F-ob (A + B) .snd) _ _)
      forward
      backward
    where
    relProp : ∀ a b → isProp ⟨ LR .F-obᴰ A (a , b) ⟩
    relProp a b =
      isOfHLevelRespectEquiv 1
        (invEquiv (identityExtension {A = A} p a b))
        (isOfHLevelPathP' 1 (Right .fst .F-ob A .snd) a b)

    leftEmb : isEmbedding (map-× (inl {B = ⟨ Left .fst .F-ob B ⟩})
                              (inl {B = ⟨ Right .fst .F-ob B ⟩}))
    leftEmb = ×Monotone↪
      (_ , isEmbedding-inl) (_ , isEmbedding-inl) .snd

    leftProp : isProp _
    leftProp =
      isOfHLevelRespectEquiv 1 Σ-assoc-≃
        (isPropΣ
          (isEmbedding→hasPropFibers leftEmb (inl x , inl y))
          (λ z → relProp (z .fst .fst) (z .fst .snd)))

    rightEmpty : _ → Empty.⊥
    rightEmpty ((_ , _) , e , _) =
      lower (⊎Path.encode _ _ (cong fst e))

    sourceProp : isProp ⟨ LR .F-obᴰ (A + B) (inl x , inl y) ⟩
    sourceProp =
      isProp⊎ leftProp
        (λ u v → Empty.rec (rightEmpty u))
        (λ _ r → rightEmpty r)

    forward : ⟨ LR .F-obᴰ (A + B) (inl x , inl y) ⟩ → _
    forward (inl ((a , b) , e , r)) i =
      inl
        (identityExtension {A = A} p x y .fst
          (subst (λ z → ⟨ LR .F-obᴰ A z ⟩)
            (ΣPathP
              ( lower (⊎Path.encode _ _ (cong fst e))
              , lower (⊎Path.encode _ _ (cong snd e))))
            r)
          i)
    forward (inr r) = Empty.rec (rightEmpty r)

    backward : PathP (λ i → baseFreeInterpretation≡ (p +-free q) i)
                       (inl x) (inl y) → _
    backward r =
      inl ((x , y) , refl ,
        invEq (identityExtension {A = A} p x y) (PathP-inl-inj r))
  identityExtension {A = A + B} (p +-free q) (inr x) (inr y) =
    propBiimpl→Equiv
      sourceProp
      (isOfHLevelPathP' 1 (Right .fst .F-ob (A + B) .snd) _ _)
      forward
      backward
    where
    relProp : ∀ a b → isProp ⟨ LR .F-obᴰ B (a , b) ⟩
    relProp a b =
      isOfHLevelRespectEquiv 1
        (invEquiv (identityExtension {A = B} q a b))
        (isOfHLevelPathP' 1 (Right .fst .F-ob B .snd) a b)

    rightEmb : isEmbedding (map-× (inr {A = ⟨ Left .fst .F-ob A ⟩})
                               (inr {A = ⟨ Right .fst .F-ob A ⟩}))
    rightEmb = ×Monotone↪
      (_ , isEmbedding-inr) (_ , isEmbedding-inr) .snd

    rightProp : isProp _
    rightProp =
      isOfHLevelRespectEquiv 1 Σ-assoc-≃
        (isPropΣ
          (isEmbedding→hasPropFibers rightEmb (inr x , inr y))
          (λ z → relProp (z .fst .fst) (z .fst .snd)))

    leftEmpty : _ → Empty.⊥
    leftEmpty ((_ , _) , e , _) =
      lower (⊎Path.encode _ _ (cong fst e))

    sourceProp : isProp ⟨ LR .F-obᴰ (A + B) (inr x , inr y) ⟩
    sourceProp =
      isProp⊎
        (λ u v → Empty.rec (leftEmpty u))
        rightProp
        (λ l _ → leftEmpty l)

    forward : ⟨ LR .F-obᴰ (A + B) (inr x , inr y) ⟩ → _
    forward (inl r) = Empty.rec (leftEmpty r)
    forward (inr ((a , b) , e , r)) i =
      inr
        (identityExtension {A = B} q x y .fst
          (subst (λ z → ⟨ LR .F-obᴰ B z ⟩)
            (ΣPathP
              ( lower (⊎Path.encode _ _ (cong fst e))
              , lower (⊎Path.encode _ _ (cong snd e))))
            r)
          i)

    backward : PathP (λ i → baseFreeInterpretation≡ (p +-free q) i)
                       (inr x) (inr y) → _
    backward r =
      inr ((x , y) , refl ,
        invEq (identityExtension {A = B} q x y) (PathP-inr-inj r))
  identityExtension {A = A + B} (p +-free q) (inl x) (inr y) =
    Empty.uninhabEquiv sourceEmpty PathP-inl≢inr
    where
    sourceEmpty : ⟨ LR .F-obᴰ (A + B) (inl x , inr y) ⟩ → Empty.⊥
    sourceEmpty (inl ((_ , _) , e , _)) =
      lower (⊎Path.encode _ _ (cong snd e))
    sourceEmpty (inr ((_ , _) , e , _)) =
      lower (⊎Path.encode _ _ (cong fst e))
  identityExtension {A = A + B} (p +-free q) (inr x) (inl y) =
    Empty.uninhabEquiv sourceEmpty PathP-inr≢inl
    where
    sourceEmpty : ⟨ LR .F-obᴰ (A + B) (inr x , inl y) ⟩ → Empty.⊥
    sourceEmpty (inl ((_ , _) , e , _)) =
      lower (⊎Path.encode _ _ (cong fst e))
    sourceEmpty (inr ((_ , _) , e , _)) =
      lower (⊎Path.encode _ _ (cong snd e))
  identityExtension {A = A₀ ⇒ B₀} (A ⇒-free B) f g =
    propBiimpl→Equiv
      (isPropΠ λ _ → isPropΠ λ _ →
        isOfHLevelRespectEquiv 1
          (invEquiv (identityExtension {A = B₀} B _ _))
          (isOfHLevelPathP' 1 (Right .fst .F-ob B₀ .snd) _ _))
      (isOfHLevelPathP' 1 (Right .fst .F-ob (A₀ ⇒ B₀) .snd) f g)
      forward
      backward
    where
    forward : ⟨ LR .F-obᴰ (A₀ ⇒ B₀) (f , g) ⟩ → _
    forward rel = funExtDep λ {x}{y} p →
      equivFun (identityExtension B (f x) (g y))
        (LR .F-homᴰ (FreeBiCCC.eval' Q)
          ((f , x) , (g , y))
          (rel , invEq (identityExtension A x y) p))

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
        (invEq (identityExtension {A = B₀} B (f x) (g y))
          (invEq funExtDepEquiv r
            (equivFun (identityExtension {A = A₀} A x y)
              (Point×A.πᴰ₂ ((h , x) , (k , y)) zr))))

    backward : _ → ⟨ LR .F-obᴰ (A₀ ⇒ B₀) (f , g) ⟩
    backward r = LRMotive.λᴰ (body r) (f , g) refl

  identityExtensionHom :
    ∀ {A B} (freeA : BaseFree A) (freeB : BaseFree B)
      (e : FreeBiCCC.Expr Q A B)
      (x : ⟨ Left .fst .F-ob A ⟩)
      (y : ⟨ Right .fst .F-ob A ⟩) →
    PathP (λ i → baseFreeInterpretation≡ freeA i) x y →
    PathP (λ i → baseFreeInterpretation≡ freeB i)
      (Left .fst .F-hom e x) (Right .fst .F-hom e y)
  identityExtensionHom freeA freeB e x y p =
    equivFun (identityExtension freeB _ _)
      (LR .F-homᴰ e (x , y) (invEq (identityExtension freeA x y) p))
   
