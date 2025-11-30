{-# OPTIONS --lossy-unification #-}
{- TODO: move this to LocallySmall.Presheaf.GloballySmall.Base -}

{-- A globally small presheaf on a small category C
-- is a contravariant functor from C to the category
-- of sets *at a fixed universe level*
--
-- For a globally small presheaf P, not only are all sets
-- in its image small but they are the *same* level.
--}
module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base where

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
import Cubical.Categories.Presheaf.Morphism.Alt as SmallPsh
import Cubical.Categories.Functor.Base as SmallFunctor
import Cubical.Categories.Instances.Sets as SmallCatSets

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Functor using (_∘F_ ; _^opF)
import Cubical.Categories.LocallySmall.Functor as LocallySmallF
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory

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
open LocallySmallF.Functor

private
  module SET = CategoryᴰNotation SET

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module C^op = SmallCategory (C ^opsmall)

  open NatTransDefs (C ^opsmall) SET
  Presheaf : (ℓP : Level) → Typeω
  Presheaf ℓP = FunctorEq Eq.refl (liftω ℓP)

  PRESHEAF : Categoryᴰ LEVEL (λ ℓP → Presheaf (ℓP .lowerω)) _
  PRESHEAF = FUNCTOR-EQ (C ^opsmall) SET Eq.refl

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    C' = SmallLocallySmallCategory→SmallCategory C
  SmallPresheaf : (ℓP : Level) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP))
  SmallPresheaf = SmallPsh.Presheaf C'

  module _ {ℓP} {ℓQ} (P : SmallPresheaf ℓP) (Q : SmallPresheaf ℓQ) where
    SmallPshHom : Type _
    SmallPshHom = SmallPsh.PshHom P Q

  -- A small presheaf (as in Cubical.Categories.Presheaf.Base)
  -- is definitionally isomorphic to a globally small presheaf on
  -- a small category
  module _ ℓP where
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
      (c : C .SmallCategory.ob) →
      P .F-ob (liftω c) .lowerω ≡ Presheaf→SmallPresheaf P .SFunctor.F-ob c
    Presheaf→SmallPresheaf→Presheaf-F-ob P c = refl

    Presheaf→SmallPresheaf→Presheaf-F-hom :
      ∀ (P : Presheaf C ℓP) →
         {c c' : C .SmallCategory.ob} →
      P .F-hom {x = liftω c} {y = liftω c'} ≡
        Presheaf→SmallPresheaf P .SFunctor.F-hom
    Presheaf→SmallPresheaf→Presheaf-F-hom P = refl

    SmallPresheaf→Presheaf→SmallPresheaf : ∀ (P : SmallPresheaf ℓP) →
      Presheaf→SmallPresheaf (SmallPresheaf→Presheaf P) ≡ P
    SmallPresheaf→Presheaf→SmallPresheaf P =
      SmallFunctor.Functor≡ (λ _ → refl) λ _ → refl

module _
  (C : SmallCategory ℓC ℓC')
  (c : C .SmallCategory.ob)
  where

  open NatTransDefs (C ^opsmall) SET
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

  open NatTransDefs (C ^opsmall) SET
  open NatTrans

  HomLevelF : LocallySmallF.Functor C.cat LEVEL
  HomLevelF = Constant (liftω ℓC')

  open Section
  YONEDA-S : Section HomLevelF (PRESHEAF C)
  YONEDA-S .F-obᴰ c = C [-, c .lowerω ]
  YONEDA-S .F-homᴰ f .N-ob c g = g C.⋆ f
  YONEDA-S .F-homᴰ {d = x}{d' = y} f .N-hom g =
    λ i → _ , λ h → C.⋆Assoc g h f i
  YONEDA-S .F-idᴰ =
    makeNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → C.⋆IdR _))
  YONEDA-S .F-seqᴰ f g =
    makeNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → sym $ C.⋆Assoc _ _ _ ))

  YONEDA : LocallySmallF.Functor C.cat (∫C (PRESHEAF C))
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

  module _ {C : SmallCategory ℓC ℓC'}
    {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} where
    open NatTransDefs (C ^opsmall) SET
    open NatTrans

    private
      module C = SmallCategory C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    module _ (α : ∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) where
      PshHom-N-homTy : Type _
      PshHom-N-homTy =
        ∀ {x y : C.ob} → (f : C.Hom[ liftω x , liftω y ])
          (p : P.p[ y ]) →
          α x (f P.⋆ p) ≡ (f Q.⋆ α y p)

      mkPshHom-N-hom :
        PshHom-N-homTy →
        ∀ {x y : C.ob} →
          (f : C.Hom[ liftω x , liftω y ]) →
        N-homTy _
          (FunctorEq→Functor Eq.refl (liftω ℓP) P)
          (FunctorEq→Functor Eq.refl (liftω ℓQ) Q)
          α f
      mkPshHom-N-hom PshHom-N-hom f =
          (λ i → _ , λ p → PshHom-N-hom f p i)

      mkPshHom :
        PshHom-N-homTy →
        PshHom P Q
      mkPshHom PshHom-N-hom .N-ob = α
      mkPshHom PshHom-N-hom .N-hom = mkPshHom-N-hom PshHom-N-hom

  module _
    (F : LocallySmallF.Functor (C .cat) (D .cat))
    (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) where
    PshHet : Type _
    PshHet = PshHom P (Q ∘F (F ^opF))

  module _ (F : LocallySmallF.Functor (C .cat) (D .cat)) where
    open NatTransDefs (C ^opsmall) SET
    open NatTrans

    Functor→PshHet :  (c : C .ob)
      → PshHet F (C [-, c ]) (D [-, F .F-ob (liftω c) .lowerω ])
    Functor→PshHet c .N-ob = λ _ → F-hom F
    Functor→PshHet c .N-hom f =
        (λ i → _ , λ h → F .F-seq f h i)

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    C' = SmallLocallySmallCategory→SmallCategory C
  open NatTransDefs (C ^opsmall) SET
  open NatTrans
  module _ {ℓP} {ℓQ} {P : SmallPresheaf C ℓP} {Q : SmallPresheaf C ℓQ} where
    SmallPshHom→PshHom :
      SmallPshHom C P Q →
      PshHom (SmallPresheaf→Presheaf C ℓP P) (SmallPresheaf→Presheaf C ℓQ Q)
    SmallPshHom→PshHom α .N-ob = α .SmallPsh.PshHom.N-ob
    SmallPshHom→PshHom α .N-hom f =
      ΣPathP (refl , (funExt (α .SmallPsh.PshHom.N-hom _ _ f)))

  module _ {ℓP} {ℓQ} {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} where
    PshHom→SmallPshHom :
      PshHom P Q →
      SmallPshHom C (Presheaf→SmallPresheaf C ℓP P) (Presheaf→SmallPresheaf C ℓQ Q)
    PshHom→SmallPshHom α .SmallPsh.PshHom.N-ob = α .N-ob
    PshHom→SmallPshHom α .SmallPsh.PshHom.N-hom c c' f p i =
      α .N-hom f i .snd p

  module _ {ℓP} {ℓQ} {P : SmallPresheaf C ℓP} {Q : SmallPresheaf C ℓQ}
    (α : SmallPshHom C P Q) where

    SmallPshHom→PshHom→SmallPshHom-N-ob : ∀ {c} →
      PshHom→SmallPshHom (SmallPshHom→PshHom α) .SmallPsh.PshHom.N-ob c ≡
        (α .SmallPsh.PshHom.N-ob c)
    SmallPshHom→PshHom→SmallPshHom-N-ob = refl

    SmallPshHom→PshHom→SmallPshHom-N-hom : ∀ {f} →
      PshHom→SmallPshHom (SmallPshHom→PshHom α) .SmallPsh.PshHom.N-hom f ≡
        (α .SmallPsh.PshHom.N-hom f)
    SmallPshHom→PshHom→SmallPshHom-N-hom = refl

    SmallPshHom→PshHom→SmallPshHom :
      PathP
        (λ i → SmallPshHom C
          (SmallPresheaf→Presheaf→SmallPresheaf C ℓP P i)
          (SmallPresheaf→Presheaf→SmallPresheaf C ℓQ Q i))
          (PshHom→SmallPshHom (SmallPshHom→PshHom α)) α
    SmallPshHom→PshHom→SmallPshHom i .SmallPsh.PshHom.N-ob c =
      α .SmallPsh.PshHom.N-ob c
    SmallPshHom→PshHom→SmallPshHom i .SmallPsh.PshHom.N-hom c c' f p =
      α .SmallPsh.PshHom.N-hom c c' f p

  module _ {ℓP} {ℓQ} {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHom P Q) where

    PshHom→SmallPshHom→PshHom-N-ob :
      (SmallPshHom→PshHom (PshHom→SmallPshHom α)) .N-ob ≡ α .N-ob
    PshHom→SmallPshHom→PshHom-N-ob = refl

    PshHom→SmallPshHom→PshHom-N-hom : ∀ {x y} {f : C.Hom[ x , y ]} →
      (SmallPshHom→PshHom (PshHom→SmallPshHom α)) .N-hom f ≡ α .N-hom f
    PshHom→SmallPshHom→PshHom-N-hom = refl

    PshHom→SmallPshHom→PshHom :
      SmallPshHom→PshHom (PshHom→SmallPshHom α) ≡ α
    PshHom→SmallPshHom→PshHom = makeNatTransPathP refl refl
