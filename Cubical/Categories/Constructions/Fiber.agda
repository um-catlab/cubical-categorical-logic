{-# OPTIONS --safe #-}
{-

  Given a displayed category Cᴰ over C, and any object x in C, we can
  construct the fiber category over x whose objects are the Cᴰ.ob[ x ]
  and whose morphisms are those that are over the identity.

-}

module Cubical.Categories.Constructions.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Constructions.DisplayOverTerminal
open import Cubical.Categories.Instances.Terminal

open import Cubical.Categories.Displayed.Constructions.Reindex.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  fiber : C .ob → Category ℓCᴰ ℓCᴰ'
  fiber x = DispOverTerminal→Category {ℓ* = ℓ-zero}
    (reindex Cᴰ (FunctorFromTerminal x))
  private
    ob-test : ∀ x
      → fiber x .ob ≡ Cᴰ.ob[ x ]
    ob-test x = refl

    hom-test : ∀ x xᴰ yᴰ → fiber x [ xᴰ , yᴰ ] ≡ Cᴰ [ C .id {x} ][ xᴰ , yᴰ ]
    hom-test x xᴰ yᴰ = refl

  seqⱽᴰ : ∀ {x y}{f : C [ x , y ]}
    {xᴰ xᴰ' yᴰ}
    → Cᴰ.Hom[ C .id ][ xᴰ' , xᴰ ]
    → Cᴰ [ f ][ xᴰ , yᴰ ]
    → Cᴰ.Hom[ f ][ xᴰ' , yᴰ ]
  seqⱽᴰ v fᴰ = R.reind (C .⋆IdL _) (v Cᴰ.⋆ᴰ fᴰ)


  infixl 15 seqⱽᴰ
  syntax seqⱽᴰ Cᴰ v fᴰ = v ⋆ⱽᴰ⟨ Cᴰ ⟩ fᴰ

  seqᴰⱽ : ∀ {x y}{f : C [ x , y ]}
    {xᴰ yᴰ yᴰ'}
    → Cᴰ [ f ][ xᴰ , yᴰ ]
    → Cᴰ.Hom[ C .id ][ yᴰ , yᴰ' ]
    → Cᴰ.Hom[ f ][ xᴰ , yᴰ' ]
  seqᴰⱽ fᴰ v = R.reind (C .⋆IdR _) (fᴰ Cᴰ.⋆ᴰ v)

  infixl 15 seqᴰⱽ
  syntax seqᴰⱽ Cᴰ fᴰ v = fᴰ ⋆ᴰⱽ⟨ Cᴰ ⟩ v


module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
  ⋆Assocⱽᴰⱽ : ∀ {x y} {f : C [ x , y ]} {xᴰ' xᴰ yᴰ yᴰ'}
      (u : fiber Cᴰ x [ xᴰ' , xᴰ ])
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      (v : fiber Cᴰ y [ yᴰ , yᴰ' ])
      → (u ⋆ⱽᴰ⟨ Cᴰ ⟩ fᴰ) ⋆ᴰⱽ⟨ Cᴰ ⟩ v ≡ u ⋆ⱽᴰ⟨ Cᴰ ⟩ (fᴰ ⋆ᴰⱽ⟨ Cᴰ ⟩ v)
  ⋆Assocⱽᴰⱽ u fᴰ v = R.rectify $ R.≡out $
    sym (R.reind-filler _ _)
    ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _
    ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
    ∙ R.reind-filler _ _

  ⋆Assocᴰⱽᴰ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {xᴰ yᴰ yᴰ' zᴰ}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      (v : fiber Cᴰ y [ yᴰ , yᴰ' ])
      (gᴰ : Cᴰ.Hom[ g ][ yᴰ' , zᴰ ])
      → (fᴰ ⋆ᴰⱽ⟨ Cᴰ ⟩ v) Cᴰ.⋆ᴰ gᴰ ≡ fᴰ Cᴰ.⋆ᴰ (v ⋆ⱽᴰ⟨ Cᴰ ⟩ gᴰ)
  ⋆Assocᴰⱽᴰ fᴰ v gᴰ = R.rectify $ R.≡out $
    R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _
    ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩

-- Homᴰ : ∀ {x y} → (f : C [ x , y ]) → fiber x o-[ _ ]-* fiber y
  -- Homᴰ f = mkBifunctorSep F where
  --   open BifunctorSep
  --   F : BifunctorSep _ _ _
  --   F .Bif-ob xᴰ yᴰ = (Cᴰ [ f ][ xᴰ , yᴰ ]) , Cᴰ.isSetHomᴰ
  --   F .Bif-homL u d = λ fᴰ → seqⱽᴰ u fᴰ
  --   F .Bif-L-id = funExt λ fᴰ → {!!}
  --   F .Bif-L-seq = {!!}
  --   F .Bif-homR c v = λ fᴰ → seqᴰⱽ fᴰ v
  --   F .Bif-R-id = {!!}
  --   F .Bif-R-seq = {!!}
  --   F .SepBif-RL-commute u v = funExt λ fᴰ → {!!}
