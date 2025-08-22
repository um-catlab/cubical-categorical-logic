{-# OPTIONS --lossy-unification #-}
{- This file takes a long time to type check -}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Displayed.FunctorComprehension

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functorᴰ
open NatTransᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C
  {- Definition #1: Manual, what you would expect -}
  record CartesianLift {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
         where
    field
      f*yᴰ : Cᴰ.ob[ x ]
      π : Cᴰ [ f ][ f*yᴰ , yᴰ ]
      isCartesian : ∀ {z} {zᴰ} {g : C [ z , x ]} →
        isIso λ (gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]) → (gᴰ Cᴰ.⋆ᴰ π)

    introCL : ∀ {z} {zᴰ} {g : C [ z , x ]} →
      Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ] → Cᴰ [ g ][ zᴰ , f*yᴰ ]
    introCL = isCartesian .fst
    opaque
      introCL⟨_⟩ : ∀ {z} {zᴰ} {g g' : C [ z , x ]}
        {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
        {g'fᴰ : Cᴰ [ g' C.⋆ f ][ zᴰ , yᴰ ]}
        → (g , gfᴰ) ≡ (g' , g'fᴰ)
        → (g , introCL gfᴰ) ≡ (g' , introCL g'fᴰ)
      introCL⟨ x ⟩ i .fst = x i .fst
      introCL⟨ x ⟩ i .snd = introCL (x i .snd)

      -- Using this vs introCL⟨_⟩ and manual rectify directly resulted
      -- in about a 5x speedup
      introCL⟨_⟩⟨_⟩ : ∀ {z} {zᴰ} {g g' : C [ z , x ]}
        {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
        {g'fᴰ : Cᴰ [ g' C.⋆ f ][ zᴰ , yᴰ ]}
        → g ≡ g'
        → Path Cᴰ.Hom[ _ , _ ] (g C.⋆ f , gfᴰ) (g' C.⋆ f , g'fᴰ)
        → Path Cᴰ.Hom[ _ , _ ] (g , introCL gfᴰ) (g' , introCL g'fᴰ)
      introCL⟨ p ⟩⟨ pᴰ ⟩ =
        introCL⟨ ΣPathP (p , (Cᴰ.rectify $ Cᴰ.≡out $ pᴰ)) ⟩

      βᴰCL : ∀ {z} {zᴰ} {g : C [ z , x ]} →
        {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
        → introCL gfᴰ Cᴰ.⋆ᴰ π ≡ gfᴰ
      βᴰCL = isCartesian .snd .fst _

      βCL :  ∀ {z} {zᴰ} {g : C [ z , x ]} →
        {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
        → Path Cᴰ.Hom[ (z , zᴰ) , (y , yᴰ) ]
            (g C.⋆ f , introCL gfᴰ Cᴰ.⋆ᴰ π)
            (g C.⋆ f , gfᴰ)
      βCL = Cᴰ.≡in βᴰCL

      ηᴰCL : ∀ {z} {zᴰ} {g : C [ z , x ]} →
        {gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]}
        → gᴰ ≡ introCL (gᴰ Cᴰ.⋆ᴰ π)
      ηᴰCL = sym $ isCartesian .snd .snd _

      ηCL :  ∀ {z} {zᴰ} {g : C [ z , x ]} →
        {gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]}
        → Path Cᴰ.Hom[ _ , _ ] (g , gᴰ) (g , introCL (gᴰ Cᴰ.⋆ᴰ π))
      ηCL = Cᴰ.≡in ηᴰCL

      introCL≡ :
        ∀ {z} {zᴰ} {g : C [ z , x ]}
          {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
          {gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]}
        → Path Cᴰ.Hom[ _ , _ ] (g C.⋆ f , gfᴰ) (g C.⋆ f , gᴰ Cᴰ.⋆ᴰ π)
        → Path Cᴰ.Hom[ _ , _ ] (g , introCL gfᴰ) (g , gᴰ)
      introCL≡ gfᴰ≡gᴰπ =
        introCL⟨ refl ⟩⟨ gfᴰ≡gᴰπ ⟩
        ∙ (sym $ ηCL)

      introCL≡' :
        ∀ {z} {zᴰ} {g g' : C [ z , x ]}
          {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
          {gᴰ : Cᴰ [ g' ][ zᴰ , f*yᴰ ]}
        → g ≡ g'
        → Path Cᴰ.Hom[ _ , _ ] (g C.⋆ f , gfᴰ) (g' C.⋆ f , gᴰ Cᴰ.⋆ᴰ π)
        → Path Cᴰ.Hom[ _ , _ ] (g , introCL gfᴰ) (g' , gᴰ)
      introCL≡' g≡g' gfᴰ≡gᴰπ = introCL⟨ g≡g' ⟩⟨ gfᴰ≡gᴰπ ⟩ ∙ sym ηCL

      introCL≡ᴰ :
        ∀ {z} {zᴰ} {g : C [ z , x ]}
          {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
          {gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]}
        → gfᴰ ≡ gᴰ Cᴰ.⋆ᴰ π
        → introCL gfᴰ ≡ gᴰ
      introCL≡ᴰ gfᴰ≡gᴰπ =
        Cᴰ.rectify $ Cᴰ.≡out (introCL≡ (Cᴰ.≡in gfᴰ≡gᴰπ))

      introCL-natural :
        ∀ {z} {zᴰ} {g : C [ z , x ]}
          {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
          {w}{wᴰ} {h : C [ w , z ]}
          {hᴰ : Cᴰ [ h ][ wᴰ , zᴰ ]}
        → Path Cᴰ.Hom[ _ , _ ]
          (h C.⋆ g , hᴰ Cᴰ.⋆ᴰ introCL gfᴰ)
          (h C.⋆ g , introCL (Cᴰ.reind (sym $ C.⋆Assoc h g f) (hᴰ Cᴰ.⋆ᴰ gfᴰ)))
      introCL-natural =
        sym $ introCL≡ $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym βCL ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)

      introCL-naturalᴰ :
        ∀ {z} {zᴰ} {g : C [ z , x ]}
          {gfᴰ : Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]}
          {w}{wᴰ} {h : C [ w , z ]}
          {hᴰ : Cᴰ [ h ][ wᴰ , zᴰ ]}
        → (hᴰ Cᴰ.⋆ᴰ introCL gfᴰ)
          ≡ introCL (Cᴰ.reind (sym $ C.⋆Assoc h g f) (hᴰ Cᴰ.⋆ᴰ gfᴰ))
      introCL-naturalᴰ = Cᴰ.rectify $ Cᴰ.≡out $ introCL-natural

  isFibration : Type _
  isFibration =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianLift cᴰ' f

  module _ (isFib : isFibration) where
    private
      module Cⱽ = Fibers Cᴰ
    module _ {x}{y}(f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ]) where
      open CartesianLift (isFib yᴰ f)
      fibration→HomᴰRepr : UniversalElement Cⱽ.v[ x ] (Cⱽ.HomᴰProf f ⟅ yᴰ ⟆)
      fibration→HomᴰRepr .UniversalElement.vertex = f*yᴰ
      fibration→HomᴰRepr .UniversalElement.element = π
      fibration→HomᴰRepr .UniversalElement.universal xᴰ = isIsoToIsEquiv
        ( (λ fᴰ → introCL (Cᴰ.idᴰ Cᴰ.⋆ᴰ fᴰ))
        , (λ fᴰ → Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ βCL
          ∙ Cᴰ.⋆IdL _)
        , λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $
          introCL⟨ ΣPathP (refl , (Cᴰ.rectify $ Cᴰ.≡out $
            Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
            ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ Cᴰ.⋆IdL _ ⟩⋆⟨ refl ⟩)) ⟩
          ∙ (sym ηCL)
          )
    CartesianLiftF-fiber : ∀ {x}{y} (f : C [ x , y ]) → Functor Cⱽ.v[ y ] Cⱽ.v[ x ]
    CartesianLiftF-fiber f = FunctorComprehension (Cⱽ.HomᴰProf f) (fibration→HomᴰRepr f)

  module isFibrationNotation (isFib : isFibration) where
    f*F = CartesianLiftF-fiber isFib
    module _ {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) where
      open CartesianLift (isFib yᴰ f) using (f*yᴰ) public
    module _ {x y : C .ob}{yᴰ : Cᴰ.ob[ y ]}{f : C [ x , y ]} where
      open CartesianLift (isFib yᴰ f) hiding (f*yᴰ) public

  -- Definition #2: Semi-manual, but defined as a UniversalElementⱽ -
  -- CartesianLift' is not definitionally equivalent to CartesianLift
  -- because π is over C.id ⋆ f rather than f
  CartesianLiftPsh : ∀ {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
    → Presheafⱽ x Cᴰ ℓCᴰ'
  CartesianLiftPsh {x} {y} yᴰ f .F-obᴰ zᴰ g .fst = Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]
  CartesianLiftPsh {x} {y} yᴰ f .F-obᴰ zᴰ g .snd = Cᴰ.isSetHomᴰ
  CartesianLiftPsh {x} {y} yᴰ f .F-homᴰ gᴰ h hfᴰ =
    Cᴰ.reind (sym $ C.⋆Assoc _ _ _) $ gᴰ Cᴰ.⋆ᴰ hfᴰ
  CartesianLiftPsh {x} {y} yᴰ f .F-idᴰ = funExt λ g → funExt λ gᴰ →
    Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.reind-filler _ _)
      ∙ Cᴰ.⋆IdL _
  CartesianLiftPsh {x} {y} yᴰ f .F-seqᴰ fᴰ gᴰ = funExt λ h → funExt λ hᴰ →
    Cᴰ.rectify $ Cᴰ.≡out $
      (sym $ Cᴰ.reind-filler _ _)
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
      ∙ Cᴰ.reind-filler _ _
  CARTESIANLIFT : Profunctorⱽ (C /C Cᴰ) Cᴰ ℓCᴰ'
  CARTESIANLIFT .F-obᴰ (y , yᴰ , f) = CartesianLiftPsh yᴰ f
  CARTESIANLIFT .F-homᴰ (g , gᴰ , square) .N-obᴰ xᴰ h hᴰ =
    Cᴰ.reind
      (C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym square ⟩
      ∙ sym (C.⋆Assoc _ _ _))
      $ hᴰ Cᴰ.⋆ᴰ gᴰ
  CARTESIANLIFT .F-homᴰ (g , gᴰ , square) .N-homᴰ fᴰ =
    funExt λ h → funExt λ hkᴰ →
    Cᴰ.rectify $ Cᴰ.≡out $
    (sym $ Cᴰ.reind-filler _ _)
    ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ Cᴰ.⋆Assoc _ _ _
    ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
    ∙ Cᴰ.reind-filler _ _
  CARTESIANLIFT .F-idᴰ = makeNatTransPathᴰ (Cᴰ ^opᴰ) (SETᴰ ℓC' ℓCᴰ')
    (makeNatTransPath (funExt λ _ → funExt C.⋆IdR))
    (implicitFunExt $ funExt λ yᴰ → funExt λ f → funExt λ fgᴰ →
      Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ Cᴰ.⋆IdR _)
  CARTESIANLIFT .F-seqᴰ (f , fᴰ , sq-f) (g , gᴰ , sq-g) = makeNatTransPathᴰ _ _
    (makeNatTransPath $ funExt λ _ → funExt λ h → sym $ C.⋆Assoc _ _ _)
    (implicitFunExt $ funExt λ yᴰ → funExt λ h → funExt λ hkᴰ →
      Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
        ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
        ∙ Cᴰ.reind-filler _ _)

  CartesianLift' : {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift' {x} yᴰ f =
    UniversalElementⱽ Cᴰ x (CARTESIANLIFT .F-obᴰ $ _ , yᴰ , f)

  isFibration' : Type _
  isFibration' =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianLift' cᴰ' f

  CartesianLift'F : isFibration' → Functorⱽ (C /C Cᴰ) Cᴰ
  CartesianLift'F cL's = FunctorⱽComprehension {Pᴰ = CARTESIANLIFT}
    λ x (_ , yᴰ , f) → cL's yᴰ f

  -- Definition #3: This is the "textbook" compositional
  -- definition. It suffers from very slow performance
  CartesianLift'' : {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift'' yᴰ f = RightAdjointAtⱽ (Δ/C C Cᴰ) (_ , yᴰ , f)
