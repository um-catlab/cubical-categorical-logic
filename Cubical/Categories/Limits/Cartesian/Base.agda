module Cubical.Categories.Limits.Cartesian.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable.More

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

record CartesianCategory (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  no-eta-equality
  field
    C : Category ℓ ℓ'
    term : Terminal' C
    bp   : BinProducts C

  open Category C public
  open TerminalNotation term public
  open BinProductsNotation bp public

  unitor-l : ∀ {a} → CatIso C (𝟙 × a) a
  unitor-l .fst = π₂
  unitor-l .snd .isIso.inv = !t ,p id
  unitor-l .snd .isIso.sec = ×β₂
  unitor-l .snd .isIso.ret =
    π₂ ⋆ (!t ,p id)
      ≡⟨ ×ue.intro-natural _ _ ⟩
    ((π₂ ⋆ !t) ,p (π₂ ⋆ id))
      ≡⟨ ⟨ 𝟙extensionality ⟩,p⟨ ⋆IdR _ ⟩ ⟩
    (π₁ ,p π₂)
      ≡⟨ (sym $ ×ue.weak-η _ _) ⟩
    id
      ∎

record CartesianCategoryRepr (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  no-eta-equality
  field
    C : Category ℓ ℓ'
    term : Representationᵁ C (LiftPsh (UnitPsh {C = C}) ℓ')
  module C = Category C
  field
    bp   : ∀ (c d : C.ob) → Representationᵁ C ((C [-, c ]) ×Psh (C [-, d ]))

CartesianFunctor : (C : CartesianCategory ℓC ℓC') (D : Category ℓD ℓD') → Type _
CartesianFunctor CC D =
  Σ[ F ∈ Functor (CC .C) D ]
  preservesProvidedBinProducts F (CC .bp)
  where open CartesianCategory

open Functor

module _
  {C : CartesianCategory ℓC ℓC'}
  {D : CartesianCategory ℓD ℓD'}
  {E : Category ℓE ℓE'} where
  private
    module C = CartesianCategory C
    module D = CartesianCategory D

  compCF : CartesianFunctor D E → CartesianFunctor C D.C → CartesianFunctor C E
  compCF G F = G .fst ∘F F .fst , goal
    where
    goal : preservesProvidedBinProducts (G .fst ∘F F .fst) C.bp
    goal c c' =
      preservesUniversalElements-⋆PshHet α β
        (preservesUniversalElement→PreservesUniversalElements
          α (C.bp (c , c')) (F .snd c c'))
        (preservesUniversalElement→PreservesUniversalElements
          β (D.bp (F .fst ⟅ c ⟆ , F .fst ⟅ c' ⟆))
          (G .snd (F .fst ⟅ c ⟆) (F .fst ⟅ c' ⟆)))
        (C.bp (c , c'))
      where
      α = preservesBinProdCones (F .fst) c c'
      β = preservesBinProdCones (G .fst) (F .fst ⟅ c ⟆) (F .fst ⟅ c' ⟆)
