module Cubical.Categories.LocallySmall.Displayed.Section.Bisection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Bifunctor.Base

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base

open Category
open Categoryᴰ
open Functor

module _ (C : Category Cob CHom-ℓ)
         (D : Category Dob DHom-ℓ)
         {E : Category Eob EHom-ℓ}
         (F : Bifunctor C D E)
         (Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ)
         where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module E = CategoryNotation E
    module Eᴰ = CategoryᴰNotation Eᴰ
    module F = Bifunctor F

  record Bisection : Typeω where
    field
      Bif-obᴰ : ∀ c d → Eobᴰ (F.Bif-ob c d)
      Bif-hom×ᴰ : ∀ {c c' d d'}
        (f : C.Hom[ c , c' ])(g : D.Hom[ d , d' ])
        → Eᴰ.Hom[ F.Bif-hom× f g ][ Bif-obᴰ c d , Bif-obᴰ c' d' ]
      Bif-homLᴰ : ∀ {c c'} (f : C.Hom[ c , c' ]) d
        → Eᴰ.Hom[ F.Bif-homL f d ][ Bif-obᴰ c d , Bif-obᴰ c' d ]
      Bif-homRᴰ : ∀ c {d d'} (g : D.Hom[ d , d' ])
        → Eᴰ.Hom[ F.Bif-homR c g ][ Bif-obᴰ c d , Bif-obᴰ c d' ]
      Bif-×-idᴰ : ∀ {c d}
        → Bif-hom×ᴰ (C.id {x = c}) (D.id {x = d}) Eᴰ.∫≡ Eᴰ.idᴰ
      Bif-×-seqᴰ : ∀ {c c' c'' d d' d''}
        {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
        {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
        → Bif-hom×ᴰ (f C.⋆ f') (g D.⋆ g')
          Eᴰ.∫≡ (Bif-hom×ᴰ f g Eᴰ.⋆ᴰ Bif-hom×ᴰ f' g')
      Bif-L×-agreeᴰ : ∀ {c c' d} {f : C.Hom[ c , c' ]}
        → Bif-homLᴰ f d Eᴰ.∫≡ Bif-hom×ᴰ f D.id
      Bif-R×-agreeᴰ : ∀ {c d d'} {g : D.Hom[ d , d' ]}
        → Bif-homRᴰ c g Eᴰ.∫≡ Bif-hom×ᴰ C.id g

    Bif-hom×ᴰ⟨_⟩⟨_⟩ : ∀ {c c' d d'}
      {f f' : C.Hom[ c , c' ]}
      {g g' : D.Hom[ d , d' ]}
      (f≡f' : f ≡ f') (g≡g' : g ≡ g')
      → (Bif-hom×ᴰ f g) Eᴰ.∫≡ (Bif-hom×ᴰ f' g')
    Bif-hom×ᴰ⟨ f≡f' ⟩⟨ g≡g' ⟩ i =
      (F.Bif-hom× (f≡f' i) (g≡g' i))
      , (Bif-hom×ᴰ (f≡f' i) (g≡g' i))

-- module _
--   {C : Category Cob CHom-ℓ}
--   {D : Category Dob DHom-ℓ}
--   {E : Category Eob EHom-ℓ}
--   where

--   BisectionToParSection :
--     {F : Bifunctor C D E} →
--     {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ} →
--     Bisection C D F Eᴰ → Σω[ a ∈ {!!} ] {!!}
--   BisectionToParSection = {!!}
