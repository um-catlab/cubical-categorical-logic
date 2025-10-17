module Cubical.Categories.WithFamilies.Simple.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Categories.Category
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Product

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Product
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓQ ℓQ' ℓ ℓ' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open Category

module _ (base-ty : Type ℓ) where

  data TypalExpression : Type ℓ where
    1̂ 0̂ : TypalExpression
    ↑ : base-ty → TypalExpression
    _+̂_ _×̂_ _⇒̂_ : base-ty → base-ty → TypalExpression

  record SignatureOver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      funsym : Type ℓ'
      dom : funsym → Σ[ n ∈ ℕ ] (Fin n → base-ty)
      cod : funsym → base-ty

-- Signature : ∀ ℓ ℓ' → Type _
-- Signature ℓ ℓ' = Σ[ base-ty ∈ Type ℓ ] SignatureOver base-ty ℓ'

-- module _ ((base-ty , function-symbols) : Signature ℓ ℓ') (S : SCwF ℓC ℓC' ℓT ℓT') where
--   open SignatureOver function-symbols
--   open SCwFNotation S

--   module _ (↑ty : base-ty → Ty) where
--     ↑tm : base-ty → Presheaf C _
--     ↑tm A = Tm (↑ty A)

--     mkArgs : (f : funsym) → Fin (dom f .fst) → Presheaf C _
--     mkArgs f k = ↑tm (dom f .snd k)

--     ↑dom :  (f : funsym) → Presheaf C _
--     ↑dom f = FinProdPsh $ mkArgs f

--     ↑cod :  (f : funsym) → Presheaf C _
--     ↑cod f = ↑tm (cod f)

--     record Interp : Typeω where
--       field
--         ↑fun : (f : funsym) → PshHom (↑dom f) (↑cod f)

--     module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
--       open SCwFᴰNotation Sᴰ
--       module _ (↑tyᴰ : (A : base-ty) → Tyᴰ (↑ty A)) where
--         ↑tmᴰ : (A : base-ty) → Presheafᴰ (↑tm A) Cᴰ _
--         ↑tmᴰ A = Tmᴰ (↑tyᴰ A)

--         mkArgsᴰ :
--           (f : funsym) → (k : Fin (dom f .fst)) →
--           Presheafᴰ (↑tm (dom f .snd k)) Cᴰ _
--         mkArgsᴰ f k = ↑tmᴰ (dom f .snd k)

--         ↑domᴰ : (f : funsym) → Presheafᴰ (↑dom f) Cᴰ _
--         ↑domᴰ f = FinProdPshᴰ (mkArgs f) (mkArgsᴰ f)

--         ↑codᴰ :  (f : funsym) → Presheafᴰ (↑cod f) Cᴰ _
--         ↑codᴰ f = ↑tmᴰ (cod f)

--         record Interpᴰ (ι : Interp) : Typeω where
--           open Interp ι
--           field
--             ↑funᴰ : (f : funsym) → PshHomᴰ (↑fun f) (↑domᴰ f) (↑codᴰ f)

-- record SCwFOver (sig : Signature ℓ ℓ') ℓC ℓC' ℓT ℓT' : Typeω where
--   field
--     S : SCwF ℓC ℓC' ℓT ℓT'
--   open SCwFNotation S
--   field
--     ↑ty : ⟨ sig ⟩ → Ty
--     interp : Interp sig S ↑ty

-- record SCwFᴰOver
--   (sig : Signature ℓ ℓ')
--   (SOver : SCwFOver sig ℓC ℓC' ℓT ℓT')
--   ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Typeω where
--   open SignatureOver (sig .snd) public
--   open SCwFOver SOver public
--   field
--     Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
--   open SCwFᴰNotation Sᴰ
--   field
--     ↑tyᴰ : (A : ⟨ sig ⟩) → Tyᴰ (↑ty A)
--     interpᴰ : Interpᴰ sig S ↑ty Sᴰ ↑tyᴰ interp

-- module _
--   (sig : Signature ℓ ℓ')
--   (SOver : SCwFOver sig ℓC ℓC' ℓT ℓT')
--   (SᴰOver : SCwFᴰOver sig SOver ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
--   where
--   open SCwFᴰOver SᴰOver

--   module _
--     ((Fᴰ , F-ty , F-tm
--          , presTerm , presLocalRep) : SCwFSection S Sᴰ) where

--     PreservesBaseType : ⟨ sig ⟩ → Type _
--     PreservesBaseType A = F-ty (↑ty A) ≡ ↑tyᴰ A

--     PreservesBaseTypes : Type _
--     PreservesBaseTypes = ∀ (A : ⟨ sig ⟩) → PreservesBaseType A

--     PreservesFunctionSymbol : funsym → Type _
--     PreservesFunctionSymbol f = {!!}

--     PreservesSignature : Type _
--     PreservesSignature = {!!}
