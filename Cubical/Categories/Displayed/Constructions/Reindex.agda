{-

-}

{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Equality
import      Cubical.Data.Equality.Conversion as Equality

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal hiding (intro)
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Magmoid

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where

  private
    module C = Category C
    module R = HomᴰReasoning Cᴰ

    -- todo: generalize upstream somewhere to Data.Equality?
    isPropEqHom : ∀ {a b : C.ob} {f g : C [ a , b ]}
                → isProp (f Equality.≡ g)
    isPropEqHom {f = f}{g} =
      subst isProp (Equality.PathPathEq {x = f}{y = g}) (C.isSetHom f g)

  open Categoryᴰ Cᴰ

  reind' : {a b : C.ob} {f g : C [ a , b ]} (p : f Equality.≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → Hom[ f ][ aᴰ , bᴰ ] → Hom[ g ][ aᴰ , bᴰ ]
  reind' p = Equality.transport Hom[_][ _ , _ ] p

  reind≡reind' : ∀ {a b : C.ob} {f g : C [ a , b ]}
    {p : f ≡ g} {e : f Equality.≡ g}
    {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    → R.reind p fᴰ ≡ reind' e fᴰ
  reind≡reind' {p = p}{e} fᴰ = subst {x = Equality.pathToEq p} (λ e → R.reind p fᴰ ≡ reind' e fᴰ)
    (isPropEqHom _ _)
    lem
    where
    lem : R.reind p fᴰ ≡ reind' (Equality.pathToEq p) fᴰ
    lem = sym (Equality.eqToPath ((Equality.transportPathToEq→transportPath Hom[_][ _ , _ ]) p fᴰ))
    
open Category
open Functor

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (F : Functor C D)
  (F-id'  : {x : C .ob} → D .id {x = F .F-ob x} Equality.≡ F .F-hom (C .id))
  (F-seq' : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → (F .F-hom f) ⋆⟨ D ⟩ (F .F-hom g) Equality.≡ F .F-hom (f ⋆⟨ C ⟩ g))
  where

  private
    module R = HomᴰReasoning Dᴰ
    module C = Category C
    module D = Category D
    module Dᴰ = Categoryᴰ Dᴰ
  open Functor F

  -- I admonish you to use this definition only when F-id' and F-seq'
  -- above are Equality.refl
  reindex' : Categoryᴰ C ℓDᴰ ℓDᴰ'
  reindex' = redefine-id⋆ (reindex Dᴰ F)
    (reind' Dᴰ F-id' Dᴰ.idᴰ , implicitFunExt (λ {x} → implicitFunExt (λ {xᴰ} →
      reind≡reind' Dᴰ Dᴰ.idᴰ)))
    ((λ fᴰ gᴰ → reind' Dᴰ (F-seq' _ _) (Dᴰ._⋆ᴰ_ fᴰ gᴰ))
    , implicitFunExt (λ {x} → implicitFunExt (λ {y} → implicitFunExt (λ {z} →
      implicitFunExt (λ {f} → implicitFunExt (λ {g} → implicitFunExt (λ {xᴰ} →
      implicitFunExt (λ {yᴰ} → implicitFunExt (λ {zᴰ} → funExt (λ fᴰ → funExt λ gᴰ →
      reind≡reind' Dᴰ (fᴰ Dᴰ.⋆ᴰ gᴰ)))))))))))

   -- TODO: it would be really nice to have a macro reindexRefl! that worked like the following:
   -- See Cubical.Categories.Constructions.Quotient.More for an example
   -- reindexRefl! Cᴰ F = reindex' Cᴰ F Equality.refl (λ _ _ → Equality.refl)
