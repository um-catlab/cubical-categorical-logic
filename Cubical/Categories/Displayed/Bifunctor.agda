{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Bifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct hiding (Fst; Snd; Sym)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import Cubical.Categories.Displayed.Reasoning as Reasoning

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓᴰ ℓᴰ' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'} where
  -- This is based on the BifunctorParAx definition
  record Bifunctorᴰ (F : Bifunctor C D E)
                    (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
                    (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
                    (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ')
     : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD (ℓ-max ℓD' (ℓ-max ℓE (ℓ-max ℓE'
            (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' (ℓ-max ℓDᴰ (ℓ-max ℓDᴰ'
            (ℓ-max ℓEᴰ ℓEᴰ'))))))))))) where

    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ
      module Eᴰ = Categoryᴰ Eᴰ
      module R = Reasoning Eᴰ
      module F = Bifunctor F
  
    field
      Bif-obᴰ : ∀ {c d} → Cᴰ.ob[ c ] → Dᴰ.ob[ d ] → Eᴰ.ob[ F ⟅ c , d ⟆b ]
      Bif-homLᴰ : ∀ {c c' cᴰ cᴰ'} {f : C [ c , c' ]} (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
        {d} (dᴰ : Dᴰ.ob[ d ])
        → Eᴰ [ F ⟪ f ⟫l ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ ]
      Bif-homRᴰ : ∀ {c} (cᴰ : Cᴰ.ob[ c ]) {d d' dᴰ dᴰ'}
        {g : D [ d , d' ]} (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
        → Eᴰ [ F ⟪ g ⟫r ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ dᴰ' ]
      Bif-hom×ᴰ : ∀ {c c' d d'} {f : C [ c , c' ]}{g : D [ d , d' ]}
             {cᴰ cᴰ' dᴰ dᴰ'}
             (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
             (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
             → Eᴰ [ F ⟪ f , g ⟫× ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
      Bif-×-idᴰ : ∀ {c d cᴰ dᴰ}
        → Bif-hom×ᴰ (Cᴰ.idᴰ {p = cᴰ}) (Dᴰ.idᴰ {p = dᴰ})
            Eᴰ.≡[ F.Bif-×-id {c = c}{d = d} ]
          Eᴰ.idᴰ
      Bif-×-seqᴰ :
        ∀ {c c' c'' d d' d''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
        → {f : C [ c , c' ]}{f' : C [ c' , c'' ]}
        → {g : D [ d , d' ]}{g' : D [ d' , d'' ]}
        → (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ]) (fᴰ' : Cᴰ [ f' ][ cᴰ' , cᴰ'' ])
        → (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ]) (gᴰ' : Dᴰ [ g' ][ dᴰ' , dᴰ'' ])
        → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
            Eᴰ.≡[ F.Bif-×-seq f f' g g' ]
          (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
      Bif-L×-agreeᴰ : ∀ {c c' d}{cᴰ cᴰ' dᴰ}
        {f : C [ c , c' ]}
        (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
        → Bif-homLᴰ fᴰ dᴰ Eᴰ.≡[ F.Bif-L×-agree {d = d} f ] Bif-hom×ᴰ fᴰ Dᴰ.idᴰ
      Bif-R×-agreeᴰ : ∀ {c d d'}{cᴰ dᴰ dᴰ'}
        {g : D [ d , d' ]}
        (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
        → Bif-homRᴰ cᴰ gᴰ Eᴰ.≡[ F.Bif-R×-agree {c = c} g ] Bif-hom×ᴰ Cᴰ.idᴰ gᴰ

    Bif-R-idᴰ : ∀ {c d}{cᴰ dᴰ}
      → Bif-homRᴰ cᴰ (Dᴰ.idᴰ {d}{dᴰ})
          Eᴰ.≡[ F.Bif-R-id {c} ]
        Eᴰ.idᴰ
    Bif-R-idᴰ = R.rectify (R.≡out (R.≡in (Bif-R×-agreeᴰ _) ∙ R.≡in Bif-×-idᴰ))

    Bif-R-seqᴰ : ∀ {c d d' d''}{g : D [ d , d' ]}{g' : D [ d' , d'' ]}
                  {cᴰ : Cᴰ.ob[ c ]}{dᴰ dᴰ' dᴰ''}(gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])(gᴰ' : Dᴰ [ g' ][ dᴰ' , dᴰ'' ])
              → Bif-homRᴰ cᴰ (gᴰ Dᴰ.⋆ᴰ gᴰ')
                  Eᴰ.≡[ F.Bif-R-seq g g' ]
                Bif-homRᴰ cᴰ gᴰ Eᴰ.⋆ᴰ Bif-homRᴰ cᴰ gᴰ'
    Bif-R-seqᴰ gᴰ gᴰ' = R.rectify $ R.≡out $
      (R.≡in $ Bif-R×-agreeᴰ _)
      ∙ (R.≡in $ (λ i → Bif-hom×ᴰ (Cᴰ.⋆IdRᴰ Cᴰ.idᴰ (~ i)) (gᴰ Dᴰ.⋆ᴰ gᴰ')))
      ∙ (R.≡in $ Bif-×-seqᴰ _ _ _ _)
      ∙ R.⟨ sym $ R.≡in $ Bif-R×-agreeᴰ _ ⟩⋆⟨ sym $ R.≡in $ Bif-R×-agreeᴰ _ ⟩

private
  variable
    C D E : Category ℓ ℓ'
    Cᴰ Dᴰ Eᴰ : Categoryᴰ C ℓ ℓ'
open Category
open Categoryᴰ
open Functorᴰ
open Bifunctorᴰ
appLᴰ : {F : Bifunctor C D E} (Fᴰ : Bifunctorᴰ F Cᴰ Dᴰ Eᴰ)
  {c : C .ob} (cᴰ : ob[_] Cᴰ c) → Functorᴰ (appL F c) Dᴰ Eᴰ
appLᴰ Fᴰ cᴰ .F-obᴰ dᴰ = Fᴰ .Bif-obᴰ cᴰ dᴰ
appLᴰ Fᴰ cᴰ .F-homᴰ gᴰ = Fᴰ .Bif-homRᴰ cᴰ gᴰ
appLᴰ Fᴰ cᴰ .F-idᴰ = Bif-R-idᴰ Fᴰ
appLᴰ Fᴰ cᴰ .Functorᴰ.F-seqᴰ = Bif-R-seqᴰ Fᴰ

-- To implement:
-- 1. Compositions ∘Flᴰ , ∘Frᴰ , ∘Fbᴰ , ∘Flrᴰ
-- 2. [x] appL
-- 3. BifunctorToParFunctor
-- 2. ×SetsBifᴰ (SETᴰ)
-- 4. ,F-Bif    (×Cᴰ)
