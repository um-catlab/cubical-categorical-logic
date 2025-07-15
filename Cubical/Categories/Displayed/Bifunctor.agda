{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Bifunctor where

open import Cubical.Foundations.Prelude hiding (Path)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct hiding (Fst; Snd; Sym)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓᴰ ℓᴰ' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'} where
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
