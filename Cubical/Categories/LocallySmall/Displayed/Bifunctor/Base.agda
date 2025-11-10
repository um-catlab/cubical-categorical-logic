module Cubical.Categories.LocallySmall.Displayed.Bifunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Bifunctor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open CatIso
open CatIsoᴰ
open Bifunctor

record Bifunctorᴰ
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  (F : Bifunctor C D E)
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ)
  : Typeω where
  no-eta-equality
  constructor bifunctorᴰ
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module E = CategoryNotation E
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module F = Bifunctor F

  field
    Bif-obᴰ : ∀ {c d} → (cᴰ : Cobᴰ c) (dᴰ : Dobᴰ d) → Eobᴰ (F.Bif-ob c d)
    Bif-hom×ᴰ : ∀ {c c' d d'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.Hom[ c , c' ]}{g : D.Hom[ d , d' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.Bif-hom× f g ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
    Bif-homLᴰ : ∀ {c c' d}{cᴰ cᴰ' }
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      dᴰ
      → Eᴰ.Hom[ F.Bif-homL f d ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ ]
    Bif-homRᴰ : ∀ {c d d'}{dᴰ dᴰ'}
      {g : D.Hom[ d , d' ]}
      cᴰ
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.Bif-homR c g ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ dᴰ' ]
    Bif-×-idᴰ : ∀ {c d}{cᴰ : Cobᴰ c}{dᴰ : Dobᴰ d}
      → Bif-hom×ᴰ (Cᴰ.idᴰ {xᴰ = cᴰ}) (Dᴰ.idᴰ {xᴰ = dᴰ}) Eᴰ.∫≡ Eᴰ.idᴰ
    Bif-×-seqᴰ : ∀ {c c' c'' d d' d''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
      {fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]}
      {fᴰ' : Cᴰ.Hom[ f' ][ cᴰ' , cᴰ'' ]}
      {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]}
      {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ' , dᴰ'' ]}
      → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
        Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
    Bif-L×-agreeᴰ : ∀ {c c' d}{cᴰ cᴰ' }
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (dᴰ : Dobᴰ d)
      → Bif-homLᴰ fᴰ dᴰ Eᴰ.∫≡ Bif-hom×ᴰ fᴰ Dᴰ.idᴰ
    Bif-R×-agreeᴰ : ∀ {c d d'}{dᴰ dᴰ'}
      {g : D.Hom[ d , d' ]}
      (cᴰ : Cobᴰ c)
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Bif-homRᴰ cᴰ gᴰ Eᴰ.∫≡ Bif-hom×ᴰ Cᴰ.idᴰ gᴰ

  Bif-hom×ᴰ⟨_⟩⟨_⟩ : ∀ {c c' d d'}{f f' g g'}{cᴰ cᴰ' dᴰ dᴰ'}{fᴰ fᴰ' gᴰ gᴰ'}
    (fᴰ≡fᴰ' : Path Cᴰ.Hom[ (c , cᴰ) , (c' , cᴰ') ] (f , fᴰ) (f' , fᴰ'))
    (gᴰ≡gᴰ' : Path Dᴰ.Hom[ (d , dᴰ) , (d' , dᴰ') ] (g , gᴰ) (g' , gᴰ'))
    → (Bif-hom×ᴰ fᴰ gᴰ) Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ' gᴰ')
  Bif-hom×ᴰ⟨ fᴰ≡fᴰ' ⟩⟨ gᴰ≡gᴰ' ⟩ i =
    (F.Bif-hom× (fᴰ≡fᴰ' i .fst) (gᴰ≡gᴰ' i .fst))
    , (Bif-hom×ᴰ (fᴰ≡fᴰ' i .snd) (gᴰ≡gᴰ' i .snd))

  ∫F : Bifunctor Cᴰ.∫C Dᴰ.∫C Eᴰ.∫C
  ∫F .Bif-ob (c , cᴰ) (d , dᴰ) = _ , Bif-obᴰ cᴰ dᴰ
  ∫F .Bif-hom× (f , fᴰ) (g , gᴰ) = _ , Bif-hom×ᴰ fᴰ gᴰ
  ∫F .Bif-homL (f , fᴰ) (d , dᴰ) = _ , Bif-homLᴰ fᴰ dᴰ
  ∫F .Bif-homR (c , cᴰ) (g , gᴰ) = _ , Bif-homRᴰ cᴰ gᴰ
  ∫F .Bif-×-id = Bif-×-idᴰ
  ∫F .Bif-×-seq = Bif-×-seqᴰ
  ∫F .Bif-L×-agree (_ , fᴰ) (_ , dᴰ) = Bif-L×-agreeᴰ fᴰ dᴰ
  ∫F .Bif-R×-agree (_ , cᴰ) (_ , gᴰ) = Bif-R×-agreeᴰ cᴰ gᴰ

module _
  {C : Category Cob CHom-ℓ} {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ} {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ} {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  where

  open Bifunctorᴰ
  open Functorᴰ

  BifunctorᴰToParFunctorᴰ :
    {F : Bifunctor C D E} → Bifunctorᴰ F Cᴰ Dᴰ Eᴰ →
    Functorᴰ (BifunctorToParFunctor F) (Cᴰ ×Cᴰ Dᴰ) Eᴰ
  BifunctorᴰToParFunctorᴰ Fᴰ .F-obᴰ = λ z → Fᴰ .Bif-obᴰ (z .Σω.fst) (z .Σω.snd)
  BifunctorᴰToParFunctorᴰ Fᴰ .F-homᴰ = λ fᴰ → Fᴰ .Bif-hom×ᴰ (fᴰ .fst) (fᴰ .snd)
  BifunctorᴰToParFunctorᴰ Fᴰ .F-idᴰ = Fᴰ .Bif-×-idᴰ
  BifunctorᴰToParFunctorᴰ Fᴰ .F-seqᴰ = λ fᴰ gᴰ → Fᴰ .Bif-×-seqᴰ

  ParFunctorᴰToBifunctorᴰ :
    {F : Functor (C ×C D) E} →
    Functorᴰ F (Cᴰ ×Cᴰ Dᴰ) Eᴰ →
    Bifunctorᴰ (ParFunctorToBifunctor F) Cᴰ Dᴰ Eᴰ
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-obᴰ = λ cᴰ dᴰ → F-obᴰ Fᴰ (cᴰ , dᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-hom×ᴰ = λ fᴰ gᴰ → F-homᴰ Fᴰ (fᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-homLᴰ = λ fᴰ dᴰ → F-homᴰ Fᴰ (fᴰ , Categoryᴰ.idᴰ Dᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-homRᴰ = λ cᴰ gᴰ → F-homᴰ Fᴰ (Categoryᴰ.idᴰ Cᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-×-idᴰ = F-idᴰ Fᴰ
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-×-seqᴰ = F-seqᴰ Fᴰ (_ , _) (_ , _)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-L×-agreeᴰ _ _ = refl
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-R×-agreeᴰ _ _ = refl

module _
  {C : Category Cob CHom-ℓ}
  {Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  {Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ} {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  where

  open Bifunctorᴰ
  open Functorᴰ

  BifunctorᴰToParFunctorᴰSF :
    {F : Bifunctor C D E} → Bifunctorᴰ F Cᴰ Dᴰ Eᴰ →
    Functorᴰ (BifunctorToParFunctor F) (Cᴰ ×CᴰSF Dᴰ) Eᴰ
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-obᴰ =
    λ z → Fᴰ .Bif-obᴰ (liftω (z .Liftω.lowerω .fst))
                      (liftω (z .Liftω.lowerω .snd))
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-homᴰ =
    λ fᴰ → Fᴰ .Bif-hom×ᴰ (fᴰ .fst) (fᴰ .snd)
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-idᴰ = Fᴰ .Bif-×-idᴰ
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-seqᴰ = λ fᴰ gᴰ → Fᴰ .Bif-×-seqᴰ

  ParFunctorᴰToBifunctorᴰSF :
    {F : Functor (C ×C D) E} →
    Functorᴰ F (Cᴰ ×CᴰSF Dᴰ) Eᴰ →
    Bifunctorᴰ (ParFunctorToBifunctor F) Cᴰ Dᴰ Eᴰ
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-obᴰ =
    λ cᴰ dᴰ → F-obᴰ Fᴰ (liftω (cᴰ .Liftω.lowerω , dᴰ .Liftω.lowerω))
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-hom×ᴰ = λ fᴰ gᴰ → F-homᴰ Fᴰ (fᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-homLᴰ = λ fᴰ dᴰ → F-homᴰ Fᴰ (fᴰ , Categoryᴰ.idᴰ Dᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-homRᴰ = λ cᴰ gᴰ → F-homᴰ Fᴰ (Categoryᴰ.idᴰ Cᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-×-idᴰ = F-idᴰ Fᴰ
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-×-seqᴰ = F-seqᴰ Fᴰ (_ , _) (_ , _)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-L×-agreeᴰ _ _ = refl
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-R×-agreeᴰ _ _ = refl

-- Cᴰ ⇒ⱽ Dᴰ
-- an object over x is a functor F : Cᴰ.v[ x ] → Dᴰ.v[ x ]
-- a morphism from F_x : Cᴰ⇒Dᴰ[ x ] to G_y : Cᴰ⇒Dᴰ[ y ]
--
-- over f : C [ x , y ] is?
-- well it could be a profunctor homomorphism Cᴰ[ f ][ xᴰ , yᴰ ] → Cᴰ [ f ][ F xᴰ , G yᴰ ]
-- if Cᴰ, Dᴰ are fibrations this could be a nat trans F ∘ f* ⇒ f* ∘ G : Cᴰ.v[ y ] → Dᴰ.v[ x ]
--   i.e., for every yᴰ a morphism Dᴰ.v[ x ][ F (f* yᴰ) , f* (G yᴰ) ],
--   i.e., Dᴰ [ f ][ F (f* yᴰ) , yᴰ ]
record Bifunctorⱽ {C : Category Cob CHom-ℓ}{E : Category Eob EHom-ℓ}
  (F : Functor C E)
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ)
  : Typeω where
  no-eta-equality
  constructor bifunctorⱽ
  private
    module C = CategoryNotation C
    module E = CategoryNotation E
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module F = FunctorNotation F

  field
    Bif-obᴰ : ∀ {c} → (cᴰ : Cobᴰ c) (dᴰ : Dobᴰ c) → Eobᴰ (F.F-ob c)
    Bif-hom×ᴰ : ∀ {c c'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.Hom[ f ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.F-hom f ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
    -- -- homL doesn't make sense unless Dᴰ is an (op)fibration
    -- -- does it make sense if Dᴰ is Conduché?
    -- Bif-homLᴰ : ∀ {c c'}{cᴰ cᴰ' }
    --   {f : C.Hom[ c , c' ]}
    --   (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
    --   (dᴰ : Dobᴰ c')
    --   → Eᴰ.Hom[ f ][ Bif-obᴰ cᴰ (f Dᴰ.^* dᴰ) , Bif-obᴰ cᴰ' dᴰ ]
    -- -- vice-versa homR makes sense only if Cᴰ is an (op)fibration

    -- Hm...
    Bif-×-idᴰ : ∀ {c}{cᴰ : Cobᴰ c}{dᴰ : Dobᴰ c}
      → Bif-hom×ᴰ (Cᴰ.idᴰ {xᴰ = cᴰ}) (Dᴰ.idᴰ {xᴰ = dᴰ}) Eᴰ.∫≡ Eᴰ.idᴰ
    Bif-×-seqᴰ : ∀ {c c' c''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]}
      {fᴰ' : Cᴰ.Hom[ f' ][ cᴰ' , cᴰ'' ]}
      {gᴰ : Dᴰ.Hom[ f ][ dᴰ , dᴰ' ]}
      {gᴰ' : Dᴰ.Hom[ f' ][ dᴰ' , dᴰ'' ]}
      → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
        Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
  opaque
    Bif-hom×ᴰ⟨_⟩⟨_⟩ : ∀ {c c'}{f f'}{cᴰ cᴰ' dᴰ dᴰ'}{fᴰ fᴰ' gᴰ gᴰ'}
      (fᴰ≡fᴰ' : Path Cᴰ.Hom[ (c , cᴰ) , (c' , cᴰ') ] (f , fᴰ) (f' , fᴰ'))
      (gᴰ≡gᴰ' : Path Dᴰ.Hom[ (c , dᴰ) , (c' , dᴰ') ] (f , gᴰ) (f' , gᴰ'))
      → (Bif-hom×ᴰ fᴰ gᴰ) Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ' gᴰ')
    Bif-hom×ᴰ⟨_⟩⟨_⟩ {gᴰ = gᴰ} {gᴰ'} fᴰ≡fᴰ' gᴰ≡gᴰ' =
      ΣPathP (F.F-hom⟨ PathPΣ fᴰ≡fᴰ' .fst ⟩
      , (λ i → Bif-hom×ᴰ (fᴰ≡fᴰ' i .snd) (rectified-gᴰ≡gᴰ' i)))
      where
      rectified-gᴰ≡gᴰ' : gᴰ Dᴰ.≡[ PathPΣ fᴰ≡fᴰ' .fst ] gᴰ'
      rectified-gᴰ≡gᴰ' = Dᴰ.rectify $ Dᴰ.≡out $ gᴰ≡gᴰ'

  Bif-iso×ᴰ : ∀ {c c'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.ISOC.Hom[ c , c' ]}
      (fᴰ : Cᴰ.ISOCᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.ISOCᴰ.Hom[ f ][ dᴰ , dᴰ' ])
      → Eᴰ.ISOCᴰ.Hom[ F.F-iso f ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
  Bif-iso×ᴰ fᴰ gᴰ .funᴰ = Bif-hom×ᴰ (fᴰ .funᴰ) (gᴰ .funᴰ)
  Bif-iso×ᴰ fᴰ gᴰ .invᴰ = Bif-hom×ᴰ (fᴰ .invᴰ) (gᴰ .invᴰ)
  Bif-iso×ᴰ fᴰ gᴰ .secᴰ = sym Bif-×-seqᴰ ∙ Bif-hom×ᴰ⟨ fᴰ .secᴰ ⟩⟨ gᴰ .secᴰ ⟩
    ∙ Bif-×-idᴰ
  Bif-iso×ᴰ fᴰ gᴰ .retᴰ = sym Bif-×-seqᴰ ∙ Bif-hom×ᴰ⟨ fᴰ .retᴰ ⟩⟨ gᴰ .retᴰ ⟩
    ∙ Bif-×-idᴰ
