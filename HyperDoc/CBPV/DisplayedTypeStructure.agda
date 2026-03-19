{-# OPTIONS --type-in-type #-}

module HyperDoc.CBPV.DisplayedTypeStructure where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Functor

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.Displayed.Presheaf.Morphism

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.CBPV.TypeStructure
open import HyperDoc.Connectives.Connectives

open TypeStructure
open Category
open Categoryᴰ

module DisplayedCoproducts
  {Σ : Signature }
  {M : CBPVModel Σ}
  (hasO+ : HasO+ M)
  (Mᴰ : CBPVModelᴰ M ) where 

  open CBPVModel M 
  open CBPVModelᴰ Mᴰ

  HasOᴰ+ : Type 
  HasOᴰ+ = 
    {A A' : ob V}
    (P : Vᴰ .ob[_] A)(Q : Vᴰ .ob[_] A') → 
    Σ[ X ∈ ob[ Vᴰ ] (hasO+ A A' .fst) ]
      PshIsoᴰ 
        (hasO+ A A' .snd) 
        ((Collageᴰ ^opᴰ) [-][-, X ]) 
        (((Collageᴰ ^opᴰ) [-][-, P ]) ×ᴰPsh ((Collageᴰ ^opᴰ) [-][-, Q ])) 
