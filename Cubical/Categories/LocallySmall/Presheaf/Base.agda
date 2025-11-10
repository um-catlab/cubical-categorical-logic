module Cubical.Categories.LocallySmall.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category.Base as SmallCat
import Cubical.Categories.Presheaf.Base as SmallPsh
import Cubical.Categories.Functor.Base as SmallFunctor

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
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

  -- A globally small presheaf
  Presheaf : Level → Typeω
  Presheaf ℓP = Functor C^op.cat SET.v[ liftω ℓP ]

  PRESHEAF : Categoryᴰ LEVEL (λ d → Functor C^op.cat SET.v[ d ]) _
  PRESHEAF = FIBER-FUNCTOR (C ^opsmall) SET

module _ {C : SmallCategory ℓC ℓC'} where
  PSH = PRESHEAF C
  module PSH = Categoryᴰ PSH

module _ {C : SmallCategory ℓC ℓC'} where
  open Categoryᴰ
  ⟨_⟩Psh : ∀ {ℓP} → Presheaf C ℓP → Category.Ob (∫C (PRESHEAF C))
  ⟨_⟩Psh = mk∫Ob (PRESHEAF C)

module _ (C : SmallCat.Category ℓC ℓC') where
  private
    module C = SmallCat.Category C
  SmallPresheaf : (ℓP : Level) → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP))
  SmallPresheaf = SmallPsh.Presheaf C

  -- Compatibility of existing construction of
  -- small presheaves with the incoming notion
  -- of globally small presheaf
  module _ ℓP where
    open Functor
    private
      module SFunctor = SmallFunctor.Functor

    SmallPresheaf→Presheaf : SmallPresheaf ℓP → Presheaf (mkSmallCategory C) ℓP
    SmallPresheaf→Presheaf P .F-ob = λ z → liftω (P .SFunctor.F-ob (z .lowerω))
    SmallPresheaf→Presheaf P .F-hom = P .SFunctor.F-hom
    SmallPresheaf→Presheaf P .F-id = P .SFunctor.F-id
    SmallPresheaf→Presheaf P .F-seq {x = liftω x} {z = liftω z} f g =
      P .SFunctor.F-seq f g
      -- I'd like to use reind-filler reasoning principles
      -- but SET.reind-filler requires many implicits to be filled in
      -- ∙ (SET.≡out
      --      {xᴰ = liftω (P .SFunctor.F-ob x)}
      --      {yᴰ = liftω (P .SFunctor.F-ob z)} $
      --      SET.reind-filler
      --        {xᴰ = liftω (P .SFunctor.F-ob x)}
      --        {yᴰ = liftω (P .SFunctor.F-ob z)}
      --         refl _)
      ∙ (sym $ transportRefl _)

    Presheaf→SmallPresheaf : Presheaf (mkSmallCategory C) ℓP → SmallPresheaf ℓP
    Presheaf→SmallPresheaf P .SFunctor.F-ob = λ z → F-ob P (liftω z) .lowerω
    Presheaf→SmallPresheaf P .SFunctor.F-hom = P .F-hom
    Presheaf→SmallPresheaf P .SFunctor.F-id = P .F-id
    Presheaf→SmallPresheaf P .SFunctor.F-seq {x = x} {z = z}
       f g =
      P .F-seq f g
      -- ∙ (SET.≡out
      --      {xᴰ = P .F-ob (liftω x)}
      --      {yᴰ = P .F-ob (liftω z)} $
      --      sym $ SET.reind-filler
      --              {xᴰ = P .F-ob (liftω x)}
      --              {yᴰ = P .F-ob (liftω z)}
      --              refl _)
      ∙ (transportRefl _)

    SmallPresheaf→Presheaf→SmallPresheaf : ∀ (P : SmallPresheaf ℓP) →
      Presheaf→SmallPresheaf (SmallPresheaf→Presheaf P) ≡ P
    SmallPresheaf→Presheaf→SmallPresheaf P =
      SmallFunctor.Functor≡ (λ _ → refl) λ _ → refl

    Presheaf→SmallPresheaf→Presheaf-F-ob :
      ∀ (P : Presheaf (mkSmallCategory C) ℓP) →
      (c : mkSmallCategory C .SmallCategory.small-ob) →
      P .F-ob (liftω c) .lowerω ≡ Presheaf→SmallPresheaf P .SFunctor.F-ob c
    Presheaf→SmallPresheaf→Presheaf-F-ob P c = refl

    Presheaf→SmallPresheaf→Presheaf-F-hom :
      ∀ (P : Presheaf (mkSmallCategory C) ℓP) →
         {c c' : mkSmallCategory C .SmallCategory.small-ob} →
      P .F-hom {x = liftω c} {y = liftω c'} ≡ Presheaf→SmallPresheaf P .SFunctor.F-hom
    Presheaf→SmallPresheaf→Presheaf-F-hom P = refl

open Functor
module _
  (C : SmallCategory ℓC ℓC')
  (c : C .SmallCategory.small-ob)
  where
  private
    module C = SmallCategory C

  _[-,_] : Presheaf C ℓC'
  _[-,_] .F-ob c' = liftω (C.Hom[ c' , liftω c ] , C.isSetHom)
  _[-,_] .F-hom f g = f C.⋆ g
  _[-,_] .F-id = funExt λ g → C.⋆IdL _
  _[-,_] .F-seq {x = x} {y} {z} f g =
    (funExt λ h → C.⋆Assoc g f h)
    ∙ (SET.≡out
         {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
         {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
         $
         SET.reind-filler
           {xᴰ = liftω (C.Hom[ x , liftω c ] , C.isSetHom)}
           {yᴰ = liftω (C.Hom[ z , liftω c ] , C.isSetHom)}
           refl λ h → g C.⋆ (f C.⋆ h))

open SmallFibNatTrans
module _
  {C : SmallCategory ℓC ℓC'}
  where
  private
    module C = SmallCategory C
  open Categoryᴰ

  よ : Functor  C.cat (∫C (PRESHEAF C))
  よ .F-ob (liftω c) = ⟨ C [-, c ] ⟩Psh
  よ .F-hom f .fst = _
  よ .F-hom f .snd .N-ob c g = g C.⋆ f
  よ .F-hom {x = x}{y = y} f .snd .N-hom g =
    N-hom'→N-hom SET _ (C [-, x .lowerω ]) (C [-, y .lowerω ])
      (よ .F-hom f .snd .N-ob) g
      (ΣPathP (refl , funExt λ _ → C.⋆Assoc _ _ _))
  よ .F-id =
    makeSFNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → C.⋆IdR _))
  よ .F-seq f g =
    makeSFNatTransPath refl
      (λ _ → ΣPathP (refl , funExt λ _ → sym $ C.⋆Assoc _ _ _ ))

  HomLevelF : Functor C.cat LEVEL
  HomLevelF = Constant (liftω ℓC')

  open Section
  よS : Section HomLevelF (PRESHEAF C)
  よS .F-obᴰ c = よ .F-ob c .snd
  よS .F-homᴰ f = よ .F-hom f .snd
  よS .F-idᴰ i = _ , よ .F-id i .snd
  よS .F-seqᴰ f g i = _ , よ .F-seq f g i .snd

module _ {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
  module PresheafNotation {ℓP} (P : Presheaf C ℓP) where
    p[_] : C.small-ob → Type ℓP
    p[ x ] = ⟨ P .F-ob (liftω x) .lowerω ⟩

    infixr 9 _⋆_
    _⋆_ : ∀ {x y} (f : C.Hom[ liftω x , liftω y ]) (g : p[ y ]) → p[ x ]
    f ⋆ g = P .F-hom f g

    ⋆IdL : ∀ {x} (g : p[ x ]) → C.id ⋆ g ≡ g
    ⋆IdL = funExt⁻ (P .F-id)

    ⟨_⟩⋆⟨_⟩ : ∀ {x y}
      {f f' : C.Hom[ liftω x , liftω y ]}
      {g g' : p[ y ]}
              → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
    ⟨ f≡f' ⟩⋆⟨ g≡g' ⟩ = cong₂ _⋆_ f≡f' g≡g'

    ⟨⟩⋆⟨_⟩ : ∀ {x y} {f : C.Hom[ liftω x , liftω y ]} {g g' : p[ y ]}
              → g ≡ g' → f ⋆ g ≡ f ⋆ g'
    ⟨⟩⋆⟨_⟩ = ⟨ refl ⟩⋆⟨_⟩

    ⟨_⟩⋆⟨⟩ : ∀ {x y} {f f' : C.Hom[ liftω x , liftω y ]} {g : p[ y ]}
              → f ≡ f' → f ⋆ g ≡ f' ⋆ g
    ⟨_⟩⋆⟨⟩ = ⟨_⟩⋆⟨ refl ⟩

    ⋆Assoc : ∀ {x y z}
      (f : C.Hom[ liftω x , liftω y ])
      (g : C.Hom[ liftω y , liftω z ])(h : p[ z ]) →
      (f C.⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    ⋆Assoc f g h =
      funExt⁻ (P .F-seq g f) h
      ∙ transportRefl _
      ∙ ⟨⟩⋆⟨ ⟨⟩⋆⟨ transportRefl _ ⟩ ⟩

    isSetPsh : ∀ {x} → isSet (p[ x ])
    isSetPsh {x} = P .F-ob (liftω x) .lowerω .snd
