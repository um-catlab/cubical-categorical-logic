{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Arrow.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base
import Cubical.Categories.Displayed.Instances.Arrow.Base as Arrow
open import Cubical.Categories.Limits.Cartesian.Functor
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Presheaf

open UniversalElement
open UniversalElementᴰ

private
  variable
    ℓC ℓC' ℓS : Level

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓS) where
  ue-iso : (ue ue' : UniversalElement C P) →
    CatIso C (ue .vertex) (ue' .vertex)
  ue-iso ue ue' = catiso
    (f .fst)
    (f⁻¹ .fst)
    (sym q ∙ p)
    (sym q' ∙ p')
    where
    f : Σ[ f ∈ C [ ue .vertex , ue' .vertex ] ] (ue' .element) ∘ᴾ⟨ C , P ⟩ f ≡ ue .element
    f = ue' .universal (ue .vertex) .equiv-proof (ue .element) .fst
    f⁻¹ : Σ[ f⁻¹ ∈ C [ ue' .vertex , ue .vertex ] ] (ue .element) ∘ᴾ⟨ C , P ⟩ f⁻¹ ≡ ue' .element
    f⁻¹ = ue .universal (ue' .vertex) .equiv-proof (ue' .element) .fst
    ue'-self : Σ[ u ∈ C [ ue' .vertex , ue' .vertex ] ] (ue' .element) ∘ᴾ⟨ C , P ⟩ u ≡ ue' .element
    ue'-self = ue' .universal (ue' .vertex) .equiv-proof (ue' .element) .fst
    ue'-self-contr : ∀ y → ue'-self ≡ y
    ue'-self-contr = ue' .universal (ue' .vertex) .equiv-proof (ue' .element) .snd
    p : ue'-self .fst ≡ Category.id C
    p = congS fst
      (ue'-self-contr (C .Category.id , funExt⁻ (P .Functor.F-id) _))
    ff⁻¹-fiber : (ue' .element) ∘ᴾ⟨ C , P ⟩ (f .fst ∘⟨ C ⟩ f⁻¹ .fst) ≡ ue' .element
    ff⁻¹-fiber = congS (λ g → g (ue' .element)) (P .Functor.F-seq (f .fst) (f⁻¹ .fst)) ∙
      congS (P ⟪ f⁻¹ .fst ⟫) (f .snd) ∙
      f⁻¹ .snd
    q : ue'-self .fst ≡ f .fst ∘⟨ C ⟩ f⁻¹ .fst
    q = congS fst
      (ue'-self-contr (f .fst ∘⟨ C ⟩ f⁻¹ .fst , ff⁻¹-fiber))
    -- totally symmetric
    ue-self : Σ[ u ∈ C [ ue .vertex , ue .vertex ] ] ue .element ∘ᴾ⟨ C , P ⟩ u ≡ ue .element
    ue-self = ue .universal (ue .vertex) .equiv-proof (ue .element) .fst
    ue-self-contr : ∀ y → ue-self ≡ y
    ue-self-contr = ue .universal (ue .vertex) .equiv-proof (ue .element) .snd
    p' : ue-self .fst ≡ Category.id C
    p' = congS fst
      (ue-self-contr (C .Category.id , funExt⁻ (P .Functor.F-id) _))
    f⁻¹f-fiber : (ue .element) ∘ᴾ⟨ C , P ⟩ (f⁻¹ .fst ∘⟨ C ⟩ f .fst) ≡ ue .element
    f⁻¹f-fiber = congS (λ g → g (ue .element)) (P .Functor.F-seq (f⁻¹ .fst) (f .fst)) ∙
      congS (P ⟪ f .fst ⟫) (f⁻¹ .snd) ∙
      f .snd
    q' : ue-self .fst ≡ f⁻¹ .fst ∘⟨ C ⟩ f .fst
    q' = congS fst
      (ue-self-contr (f⁻¹ .fst ∘⟨ C ⟩ f .fst , f⁻¹f-fiber))

module _ (C : CartesianCategory ℓC ℓC') where
  private
    module C = CartesianCategoryNotation C
  Iso : CartesianCategoryᴰ (C ×CC C) {!!} {!!}
  Iso .fst = Arrow.Iso (C .fst)
  Iso .snd .fst .vertexᴰ = idCatIso
  Iso .snd .fst .elementᴰ = tt
  Iso .snd .fst .universalᴰ {x = (c , c')} {xᴰ = (f , p)} {f = (!c , !c')} .equiv-proof _ = uniqueExists
    (C.𝟙η' , _)
    refl
    (λ _ _ _ → refl)
    λ _ _ → ≡-× (C.isSetHom _ _ _ _) refl
  Iso .snd .snd {d = (c , c') , c'' , c'''} ((f , p) , g , q) .vertexᴰ = ue-iso (BinProductProf _ ⟅ c , c'' ⟆) {!C.CCBinProducts'!} {!!} --{!!} , {!!}
  Iso .snd .snd {d = (c , c') , c'' , c'''} ((f , p) , g , q) .elementᴰ = {!!}
  Iso .snd .snd {d = (c , c') , c'' , c'''} ((f , p) , g , q) .universalᴰ = {!!}
