module Cubical.Categories.LocallySmall.Bifunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Functor.Base as LocallySmall

private
  variable
    ℓ ℓ' ℓ1 ℓ2 ℓw ℓx ℓy ℓz ℓC ℓC' : Level
    ℓᴰ ℓᴰ' ℓ1ᴰ ℓ2ᴰ ℓwᴰ ℓxᴰ ℓyᴰ ℓzᴰ ℓCᴰ ℓCᴰ' : Level

    Bob Cob Dob Eob : Typeω
    Bobᴰ : Bob → Typeω
    Cobᴰ : Cob → Typeω
    Dobᴰ : Dob → Typeω
    Eobᴰ : Eob → Typeω

open CatIso
open CatIsoᴰ

-- TODO get this loading
record Bifunctor (C : Category Cob)
                 (D : Category Dob)
                 (E : Category Eob)
       : Typeω where
  no-eta-equality
  constructor bifunctor
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module E = CategoryNotation E

  field
    Bif-ob : Cob → Dob → Eob
    Bif-hom× : ∀ {c c' d d'} (f : C.Hom[ c , c' ])(g : D.Hom[ d , d' ])
      → E.Hom[ Bif-ob c d , Bif-ob c' d' ]
    Bif-homL : ∀ {c c'} (f : C.Hom[ c , c' ]) d
      → E.Hom[ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c (g : D.Hom[ d , d' ])
      → E.Hom[ Bif-ob c d , Bif-ob c d' ]
    Bif-×-id : ∀ {c d} → Bif-hom× (C.id {c}) (D.id {d}) ≡ E.id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
      → Bif-hom× (f C.⋆ f') (g D.⋆ g')
        ≡ Bif-hom× f g E.⋆ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c'} (f : C.Hom[ c , c' ]) d
      → Bif-homL f d ≡ Bif-hom× f D.id
    Bif-R×-agree : ∀ {d d'} c (g : D.Hom[ d , d' ])
      → Bif-homR c g ≡ Bif-hom× C.id g
  Bif-hom×⟨_⟩⟨_⟩ : ∀ {c c' d d'}{f f' g g'}
    (f≡f' : Path C.Hom[ c , c' ] f f')
    (g≡g' : Path D.Hom[ d , d' ] g g')
    → Path E.Hom[ Bif-ob c d , Bif-ob c' d' ] (Bif-hom× f g) (Bif-hom× f' g')
  Bif-hom×⟨ f≡f' ⟩⟨ g≡g' ⟩ = cong₂ Bif-hom× f≡f' g≡g'

  Bif-iso× : ∀ {c c' d d'} (f : C.ISOC.Hom[ c , c' ])(g : D.ISOC.Hom[ d , d' ])
      → E.ISOC.Hom[ Bif-ob c d , Bif-ob c' d' ]
  Bif-iso× f g .fun = Bif-hom× (f .fun) (g .fun)
  Bif-iso× f g .inv = Bif-hom× (f .inv) (g .inv)
  Bif-iso× f g .sec = sym Bif-×-seq ∙ Bif-hom×⟨ f .sec ⟩⟨ g .sec ⟩ ∙ Bif-×-id
  Bif-iso× f g .ret = sym Bif-×-seq ∙ Bif-hom×⟨ f .ret ⟩⟨ g .ret ⟩ ∙ Bif-×-id

open Bifunctor

record Bifunctorᴰ {C : Category Cob}{D : Category Dob}{E : Category Eob}
  (F : Bifunctor C D E)
  (Cᴰ : Categoryᴰ C Cobᴰ)
  (Dᴰ : Categoryᴰ D Dobᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ)
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

-- Cᴰ ⇒ⱽ Dᴰ
-- an object over x is a functor F : Cᴰ.v[ x ] → Dᴰ.v[ x ]
-- a morphism from F_x : Cᴰ⇒Dᴰ[ x ] to G_y : Cᴰ⇒Dᴰ[ y ]
--
-- over f : C [ x , y ] is?
-- well it could be a profunctor homomorphism Cᴰ[ f ][ xᴰ , yᴰ ] → Cᴰ [ f ][ F xᴰ , G yᴰ ]
-- if Cᴰ, Dᴰ are fibrations this could be a nat trans F ∘ f* ⇒ f* ∘ G : Cᴰ.v[ y ] → Dᴰ.v[ x ]
--   i.e., for every yᴰ a morphism Dᴰ.v[ x ][ F (f* yᴰ) , f* (G yᴰ) ],
--   i.e., Dᴰ [ f ][ F (f* yᴰ) , yᴰ ]
record Bifunctorⱽ {C : Category Cob}{E : Category Eob}
  (F : Functor C E)
  (Cᴰ : Categoryᴰ C Cobᴰ)
  (Dᴰ : Categoryᴰ C Dobᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ)
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
