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
open import Cubical.Functions.FunExtEquiv


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

  mutual
    identityExtension :
      (A : BiCCCExpr Empty.⊥) →
      (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
      (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
      ⟨ LR .F-obᴰ (embedClosed A) (x , y) ⟩ →
      PathP (λ i → closedInterpretation≡ A i) x y
    identityExtension (↑ ())
    identityExtension ⊤ tt* tt* _ = refl
    identityExtension ⊥ ()
    identityExtension (A × B) (x , y) (x' , y') (rx , ry) =
      ΣPathP
        ( identityExtension A x x' rx
        , identityExtension B y y' ry)
    identityExtension (A + B) (inl x) (inl y) = forward
      where
      forward : ⟨ LR .F-obᴰ (embedClosed (A + B)) (inl x , inl y) ⟩ → _
      forward (inl ((a , b) , e , r)) i =
        inl
          (identityExtension A x y
            (subst (λ z → ⟨ LR .F-obᴰ (embedClosed A) z ⟩)
              (ΣPathP
                ( lower (⊎Path.encode _ _ (cong fst e))
                , lower (⊎Path.encode _ _ (cong snd e))))
              r)
            i)
      forward (inr ((_ , _) , e , _)) =
        Empty.rec (lower (⊎Path.encode _ _ (cong fst e)))
    identityExtension (A + B) (inr x) (inr y) = forward
      where
      forward : ⟨ LR .F-obᴰ (embedClosed (A + B)) (inr x , inr y) ⟩ → _
      forward (inl ((_ , _) , e , _)) =
        Empty.rec (lower (⊎Path.encode _ _ (cong fst e)))
      forward (inr ((a , b) , e , r)) i =
        inr
          (identityExtension B x y
            (subst (λ z → ⟨ LR .F-obᴰ (embedClosed B) z ⟩)
              (ΣPathP
                ( lower (⊎Path.encode _ _ (cong fst e))
                , lower (⊎Path.encode _ _ (cong snd e))))
              r)
            i)
    identityExtension (A + B) (inl x) (inr y) r =
      Empty.rec (sourceEmpty r)
      where
      sourceEmpty :
        ⟨ LR .F-obᴰ (embedClosed (A + B)) (inl x , inr y) ⟩ → Empty.⊥
      sourceEmpty (inl ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong snd e))
      sourceEmpty (inr ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong fst e))
    identityExtension (A + B) (inr x) (inl y) r =
      Empty.rec (sourceEmpty r)
      where
      sourceEmpty :
        ⟨ LR .F-obᴰ (embedClosed (A + B)) (inr x , inl y) ⟩ → Empty.⊥
      sourceEmpty (inl ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong fst e))
      sourceEmpty (inr ((_ , _) , e , _)) =
        lower (⊎Path.encode _ _ (cong snd e))
    identityExtension (A ⇒ B) f g rel =
      funExtDep λ {x}{y} p →
        identityExtension B (f x) (g y)
          (LR .F-homᴰ (FreeBiCCC.eval' Q)
            ((f , x) , (g , y))
            (rel , identityExtension⁻ A x y p))

    identityExtension⁻ :
      (A : BiCCCExpr Empty.⊥) →
      (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
      (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
      PathP (λ i → closedInterpretation≡ A i) x y →
      ⟨ LR .F-obᴰ (embedClosed A) (x , y) ⟩
    identityExtension⁻ (↑ ())
    identityExtension⁻ ⊤ tt* tt* _ = tt*
    identityExtension⁻ ⊥ ()
    identityExtension⁻ (A × B) (x , y) (x' , y') r =
      identityExtension⁻ A x x' (PathPΣ.fst r) ,
      identityExtension⁻ B y y' (λ i → r i .snd)
    identityExtension⁻ (A + B) (inl x) (inl y) r =
      inl ((x , y) , refl ,
        identityExtension⁻ A x y (PathP-inl-inj r))
    identityExtension⁻ (A + B) (inr x) (inr y) r =
      inr ((x , y) , refl ,
        identityExtension⁻ B x y (PathP-inr-inj r))
    identityExtension⁻ (A + B) (inl x) (inr y) r =
      Empty.rec (PathP-inl≢inr r)
    identityExtension⁻ (A + B) (inr x) (inl y) r =
      Empty.rec (PathP-inr≢inl r)
    identityExtension⁻ (A ⇒ B) f g r =
      LRMotive.λᴰ (body r) (f , g) refl
      where
      Point : LRMotive.Cᴰ.ob[ embedClosed (A ⇒ B) ]
      Point hk =
        (hk ≡ (f , g)) ,
        isProp→isSet (pointwise Q (SETBiCCC {ℓ}) (EqSETᴰBCCCⱽ {ℓ}) I J
          .fst .F-ob (embedClosed (A ⇒ B)) .snd hk (f , g))

      module Point×A = UUP.BinProductᴰNotation LRMotive.Cᴰ
        (Syntax.bp (embedClosed (A ⇒ B) , embedClosed A))
        (LRMotive.bpᴰ Point (LR .F-obᴰ (embedClosed A)))

      body : PathP (λ i → closedInterpretation≡ (A ⇒ B) i) f g →
        Categoryᴰ.Hom[_][_,_] LRMotive.Cᴰ (FreeBiCCC.eval' Q)
        (LRMotive.bpᴰ Point (LR .F-obᴰ (embedClosed A)) .fst)
        (LR .F-obᴰ (embedClosed B))
      body r ((h , x) , (k , y)) zr =
        subst
          (λ hk → ⟨ LR .F-obᴰ (embedClosed B) (hk .fst x , hk .snd y) ⟩)
          (sym (Point×A.πᴰ₁ ((h , x) , (k , y)) zr))
          (identityExtension⁻ B (f x) (g y)
            (invEq funExtDepEquiv r
              (identityExtension A x y
                (Point×A.πᴰ₂ ((h , x) , (k , y)) zr))))

  identityExtensionHom :
    (A B : BiCCCExpr Empty.⊥)
      (e : FreeBiCCC.Expr Q (embedClosed A) (embedClosed B))
      (x : ⟨ Left .fst .F-ob (embedClosed A) ⟩)
      (y : ⟨ Right .fst .F-ob (embedClosed A) ⟩) →
    PathP (λ i → closedInterpretation≡ A i) x y →
    PathP (λ i → closedInterpretation≡ B i)
      (Left .fst .F-hom e x) (Right .fst .F-hom e y)
  identityExtensionHom A B e x y p =
    identityExtension B _ _
      (LR .F-homᴰ e (x , y) (identityExtension⁻ A x y p))
