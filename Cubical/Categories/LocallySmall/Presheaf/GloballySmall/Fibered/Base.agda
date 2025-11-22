{-# OPTIONS --lossy-unification #-}
{-- A globally small presheaf on a small category C
-- is a contravariant functor from C to the category
-- of sets *at a fixed universe level*
--
-- For a globally small presheaf P, not only are all sets
-- in its image small but they are the *same* level.
--}
module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.Fibered.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category.Base as SmallCat
import Cubical.Categories.Presheaf.Base as SmallPsh
import Cubical.Categories.Presheaf.More as SmallPsh
import Cubical.Categories.Functor.Base as SmallFunctor
import Cubical.Categories.Instances.Sets as SmallCatSets

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Constructions.ChangeOfObjects
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Σω
open Liftω

private
  module SET = CategoryᴰNotation SET

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module C^op = SmallCategory (C ^opsmall)

  open FibNatTransDefs (C ^opsmall) SET
  Presheaf : (ℓP : Level) → Typeω
  Presheaf ℓP = FiberedFunctorEq Eq.refl (liftω ℓP)

  PRESHEAF : Categoryᴰ LEVEL (FiberedFunctorEq Eq.refl) _
  PRESHEAF = FIBERED-FUNCTOR-EQ (C ^opsmall) SET Eq.refl

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    C' = SmallLocallySmallCategory→SmallCategory C
  SmallPresheaf : (ℓP : Level) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP))
  SmallPresheaf = SmallPsh.Presheaf C'

  -- A small presheaf (as in Cubical.Categories.Presheaf.Base)
  -- is definitionally isomorphic to a globally small presheaf on
  -- a small category
  module _ ℓP where
    open Functor
    private
      module SFunctor = SmallFunctor.Functor

    SmallPresheaf→Presheaf : SmallPresheaf ℓP → Presheaf C ℓP
    SmallPresheaf→Presheaf P .F-ob = λ z → liftω (P .SFunctor.F-ob (z .lowerω))
    SmallPresheaf→Presheaf P .F-hom f = P .SFunctor.F-hom f
    SmallPresheaf→Presheaf P .F-id  = P .SFunctor.F-id
    SmallPresheaf→Presheaf P .F-seq {x = x} {z = z} f g = P .SFunctor.F-seq f g

    Presheaf→SmallPresheaf : Presheaf C ℓP → SmallPresheaf ℓP
    Presheaf→SmallPresheaf P .SFunctor.F-ob = λ z → F-ob P (liftω z) .lowerω
    Presheaf→SmallPresheaf P .SFunctor.F-hom f = F-hom P f
    Presheaf→SmallPresheaf P .SFunctor.F-id  = P .F-id
    Presheaf→SmallPresheaf P .SFunctor.F-seq f g = P .F-seq f g

    Presheaf→SmallPresheaf→Presheaf-F-ob :
      ∀ (P : Presheaf C ℓP) →
      (c : C .SmallCategory.small-ob) →
      P .F-ob (liftω c) .lowerω ≡ Presheaf→SmallPresheaf P .SFunctor.F-ob c
    Presheaf→SmallPresheaf→Presheaf-F-ob P c = refl

    Presheaf→SmallPresheaf→Presheaf-F-hom :
      ∀ (P : Presheaf C ℓP) →
         {c c' : C .SmallCategory.small-ob} →
      P .F-hom {x = liftω c} {y = liftω c'} ≡
        Presheaf→SmallPresheaf P .SFunctor.F-hom
    Presheaf→SmallPresheaf→Presheaf-F-hom P = refl

    SmallPresheaf→Presheaf→SmallPresheaf : ∀ (P : SmallPresheaf ℓP) →
      Presheaf→SmallPresheaf (SmallPresheaf→Presheaf P) ≡ P
    SmallPresheaf→Presheaf→SmallPresheaf P =
      SmallFunctor.Functor≡ (λ _ → refl) λ _ → refl

open Functor
module _
  (C : SmallCategory ℓC ℓC')
  (c : C .SmallCategory.small-ob)
  where

  open FibNatTransDefs (C ^opsmall) SET
  private
    module C = SmallCategory C

  _[-,_] : Presheaf C ℓC'
  _[-,_] =
    SmallPresheaf→Presheaf C ℓC'
      (SmallCatSets._[-,_] (SmallLocallySmallCategory→SmallCategory C) c)

module _
  {C : SmallCategory ℓC ℓC'}
  where
  private
    module C = SmallCategory C
  open Categoryᴰ

  open FibNatTransDefs (C ^opsmall) SET
  open FibNatTrans

  HomLevelF : Functor C.cat LEVEL
  HomLevelF = Constant (liftω ℓC')

  open Section
  YONEDA-S : Section HomLevelF (PRESHEAF C)
  YONEDA-S .F-obᴰ c = C [-, c .lowerω ]
  YONEDA-S .F-homᴰ f .N-ob c g = g C.⋆ f
  YONEDA-S .F-homᴰ {d = x}{d' = y} f .N-hom g =
    N-hom'→N-hom _ _ _ _ λ i → _ , λ h → C.⋆Assoc g h f i
  YONEDA-S .F-idᴰ =
    makeFibNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → C.⋆IdR _))
  YONEDA-S .F-seqᴰ f g =
    makeFibNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → sym $ C.⋆Assoc _ _ _ ))

  YONEDA : Functor C.cat (∫C (PRESHEAF C))
  YONEDA = intro YONEDA-S

module _ {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
  module PresheafNotation {ℓP} (P : Presheaf C ℓP) where
    P' = Presheaf→SmallPresheaf C ℓP P
    open SmallPsh.PresheafNotation P' public

module _ where
  open SmallCategoryVariables
  open SmallCategory


  module _ {C : SmallCategory ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
    module PSH = CategoryᴰNotation (PRESHEAF C)
    module PSHISO = CategoryᴰNotation PSH.ISOCᴰ
    PshHom : Type _
    PshHom = PSH.Homᴰ[ P , Q ]

    PshIso : Type _
    PshIso = PSHISO.Homᴰ[_,_] {f = iso _ _ refl refl} P Q

  -- An attempt at briding the gap between the naturality conditions
  -- of Presheaf.Morphism.Alt.PshHom and FibNatTrans as defined in
  -- LocallySmall.NaturalTransformation.Fibered, but it's not as
  -- helpful as expected. I thought using these constructs would remove
  -- transports, but it actually seems to add more of them :(
  -- I'm keeping this in because I think we want principles like
  -- this that are indeed usable
  -- module _ {C : SmallCategory ℓC ℓC'}
  --   {P : Presheaf C ℓP} (Q : Presheaf C ℓQ) where
  --   open FibNatTransDefs (C ^opsmall) SET
  --   open FibNatTrans

  --   private
  --     module C = SmallCategory C
  --     module P = PresheafNotation P
  --     module Q = PresheafNotation Q
  --   module _ (α : ∀ (x : C.small-ob) → P.p[ x ] → Q.p[ x ]) where
  --     PshHom-N-homTy : Type _
  --     PshHom-N-homTy =
  --       ∀ {x y : C.small-ob} → (f : C.Hom[ liftω x , liftω y ])
  --         (p : P.p[ y ]) →
  --         α x (f P.⋆ p) ≡ (f Q.⋆ α y p)

  --     mkPshHom-N-hom :
  --       PshHom-N-homTy →
  --       ∀ {x y : C.small-ob} →
  --         (f : C.Hom[ liftω x , liftω y ]) →
  --       N-homTy _
  --         (FiberedFunctorEq→FiberedFunctor Eq.refl (liftω ℓP) P)
  --         (FiberedFunctorEq→FiberedFunctor Eq.refl (liftω ℓQ) Q)
  --         α f
  --     mkPshHom-N-hom PshHom-N-hom f =
  --       N-hom'→N-hom _ _ _ _
  --         (λ i → _ , λ p → PshHom-N-hom f p i)

  --     mkPshHom :
  --       PshHom-N-homTy →
  --       PshHom P Q
  --     mkPshHom PshHom-N-hom .N-ob = α
  --     mkPshHom PshHom-N-hom .N-hom = mkPshHom-N-hom PshHom-N-hom

  module _
    (F : Functor (C .cat) (D .cat))
    (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) where
    PshHet : Type _
    PshHet = PshHom P (Q ∘F (F ^opF))

  module _ (F : Functor (C .cat) (D .cat)) where
    open FibNatTransDefs (C ^opsmall) SET
    open FibNatTrans

    Functor→PshHet :  (c : C .small-ob)
      → PshHet F (C [-, c ]) (D [-, F .F-ob (liftω c) .lowerω ])
    Functor→PshHet c .N-ob = λ _ → F-hom F
    Functor→PshHet c .N-hom f =
      N-hom'→N-hom _ _ _ _
        (λ i → _ , λ h → F .F-seq f h i)
