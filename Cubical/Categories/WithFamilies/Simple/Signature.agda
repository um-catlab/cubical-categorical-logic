module Cubical.Categories.WithFamilies.Simple.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.LevelsSyntax
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Categories.Category
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.TypeStructure
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Product
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Empty

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Product
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓQ ℓQ' ℓ ℓ' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open Category

record hasTypeFormers : Type (ℓ-suc ℓ-zero) where
  field
    hasUnit hasEmpty hasProducts hasSums hasFunctions : Type

open hasTypeFormers {{...}} public

module TypeSyntax {{whichTypes : hasTypeFormers}} (base-ty : Type ℓ) where

  data TypalExpression : Type ℓ where
    ↑ : base-ty → TypalExpression
    1̂ : {{ hasUnit }} → TypalExpression
    _×̂_ : {{ hasProducts }} → TypalExpression → TypalExpression → TypalExpression
    _⇒̂_ : {{ hasFunctions }} → TypalExpression → TypalExpression → TypalExpression
    -- 0̂ : {{ hasEmpty }} → TypalExpression
    -- _+̂_ : {{ hasSums }} → TypalExpression → TypalExpression → TypalExpression

  record SignatureOver ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      funsym : Type ℓ'
      dom : funsym → Σ[ n ∈ ℕ ] (Fin n → TypalExpression)
      cod : funsym → TypalExpression

open TypeSyntax

module _ {{whichTypes : hasTypeFormers}} where
  Signature : ∀ ℓ ℓ' → Type _
  Signature ℓ ℓ' = Σ[ base-ty ∈ Type ℓ ] SignatureOver base-ty ℓ'

module _
  (S : SCwF ℓC ℓC' ℓT ℓT')
  {{whichTypes : hasTypeFormers}}
  where

  record SemanticTypeFormers :
    Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ where
    field
      {{⟦1⟧}} : {{hasUnit}} → hasUnitType S
      {{⟦×⟧}} : {{hasProducts}} → hasProductTypes S
      {{⟦⇒⟧}} : {{hasFunctions}} → hasFunctionTypes S
      -- {{⟦0⟧}} : {{hasEmpty}} → hasEmptyType S
      -- {{⟦+⟧}} : {{hasSums}} → hasSumTypes S

  open SemanticTypeFormers {{...}} public

  module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
    record SemanticTypeFormersᴰ :
      Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ ℓCᴰ ,ℓ ℓCᴰ' ,ℓ ℓTᴰ ,ℓ ℓTᴰ' ,ℓ 0ℓ ⌉ℓ where
      field
        {{⟦1⟧ᴰ}} : {{S-unit : hasUnitType S}} →
          hasUnitTypeᴰ S Sᴰ unit-type
        {{⟦×⟧ᴰ}} : {{S-prods : hasProductTypes S}} →
          hasProductTypesᴰ S Sᴰ product-types
        {{⟦⇒⟧ᴰ}} : {{S-funs : hasFunctionTypes S}} →
          hasFunctionTypesᴰ S Sᴰ function-types
        -- {{⟦0⟧ᴰ}} : {{hasEmpty}} → hasEmptyType S
        -- {{⟦+⟧ᴰ}} : {{hasSums}} → hasSumTypes S

module _ {{whichTypes : hasTypeFormers}} where
  module _
    ((base-ty , function-symbols) : Signature ℓ ℓ')
    (S : SCwF ℓC ℓC' ℓT ℓT')
    {{semTypes : SemanticTypeFormers S}}
    where
    open SignatureOver function-symbols
    open SCwFNotation S

    module InterpDefs (↑ty : base-ty → Ty) where
      ↑tm : base-ty → Presheaf C _
      ↑tm A = Tm (↑ty A)

      ⟦_⟧Ty : TypalExpression base-ty → Ty
      ⟦ ↑ A ⟧Ty = ↑ty A
      ⟦ 1̂ ⟧Ty = unit-type .fst
      ⟦ e ×̂ e' ⟧Ty = product-types ⟦ e ⟧Ty ⟦ e' ⟧Ty .fst
      ⟦ e ⇒̂ e' ⟧Ty = function-types ⟦ e ⟧Ty ⟦ e' ⟧Ty .fst
      -- ⟦ 0̂ ⟧Ty = empty-type .fst
      -- ⟦ e +̂ e' ⟧Ty = sum-types ⟦ e ⟧Ty ⟦ e' ⟧Ty .fst

      ↑expr : TypalExpression base-ty → Presheaf C _
      ↑expr e = Tm ⟦ e ⟧Ty

      mkArgs : (f : funsym) → Fin (dom f .fst) → Presheaf C _
      mkArgs f k = ↑expr (dom f .snd k)

      ↑dom :  (f : funsym) → Presheaf C _
      ↑dom f = FinProdPsh $ mkArgs f

      ↑cod :  (f : funsym) → Presheaf C _
      ↑cod f = ↑expr (cod f)

      record Interp : Typeω where
        field
          ↑fun : (f : funsym) → PshHom (↑dom f) (↑cod f)

      module _
        (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
        {{semTypesᴰ : SemanticTypeFormersᴰ S Sᴰ}}
        where
        open SCwFᴰNotation S Sᴰ
        module InterpᴰDefs (↑tyᴰ : (A : base-ty) → Tyᴰ (↑ty A)) where
          ↑tmᴰ : (A : base-ty) → Presheafᴰ (↑tm A) Cᴰ _
          ↑tmᴰ A = Tmᴰ (↑tyᴰ A)

          ⟦_⟧Tyᴰ : (e : TypalExpression base-ty) → Tyᴰ ⟦ e ⟧Ty
          ⟦ ↑ A ⟧Tyᴰ = ↑tyᴰ A
          ⟦ 1̂ ⟧Tyᴰ = unit-typeᴰ .fst
          ⟦ e ×̂ e' ⟧Tyᴰ = product-typesᴰ ⟦ e ⟧Tyᴰ ⟦ e' ⟧Tyᴰ .fst
          ⟦ e ⇒̂ e' ⟧Tyᴰ = function-typesᴰ ⟦ e ⟧Tyᴰ ⟦ e' ⟧Tyᴰ .fst

          ↑exprᴰ : (e : TypalExpression base-ty) → Presheafᴰ (↑expr e) Cᴰ _
          ↑exprᴰ e = Tmᴰ ⟦ e ⟧Tyᴰ

          mkArgsᴰ :
            (f : funsym) → (k : Fin (dom f .fst)) →
            Presheafᴰ (↑expr (dom f .snd k)) Cᴰ _
          mkArgsᴰ f k = ↑exprᴰ (dom f .snd k)

          ↑domᴰ : (f : funsym) → Presheafᴰ (↑dom f) Cᴰ _
          ↑domᴰ f = FinProdPshᴰ (mkArgs f) (mkArgsᴰ f)

          ↑codᴰ :  (f : funsym) → Presheafᴰ (↑cod f) Cᴰ _
          ↑codᴰ f = ↑exprᴰ (cod f)

          record Interpᴰ (ι : Interp) : Typeω where
            open Interp ι
            field
              ↑funᴰ : (f : funsym) → PshHomᴰ (↑fun f) (↑domᴰ f) (↑codᴰ f)

  open InterpDefs
  open InterpᴰDefs
  record SCwFOver (sig : Signature ℓ ℓ') ℓC ℓC' ℓT ℓT' : Typeω where
    field
      S : SCwF ℓC ℓC' ℓT ℓT'
    open SCwFNotation S
    field
      {{semTypes}} : SemanticTypeFormers S
      ↑ty : ⟨ sig ⟩ → Ty
      interp : Interp sig S ↑ty

  record SCwFᴰOver
    (sig : Signature ℓ ℓ')
    (SOver : SCwFOver sig ℓC ℓC' ℓT ℓT')
    ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Typeω where
    open SignatureOver (sig .snd)
    open SCwFOver SOver
    field
      Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
    open SCwFᴰNotation S Sᴰ
    field
      ↑tyᴰ : (A : ⟨ sig ⟩) → Tyᴰ (↑ty A)
      {{semTypesᴰ}} : SemanticTypeFormersᴰ S Sᴰ
      interpᴰ : Interpᴰ sig S ↑ty Sᴰ ↑tyᴰ interp
    open Interp interp public
    open Interpᴰ interpᴰ public

  module _
    (sig : Signature ℓ ℓ')
    (SOver : SCwFOver sig ℓC ℓC' ℓT ℓT')
    (SᴰOver : SCwFᴰOver sig SOver ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
    where
    open SCwFOver SOver
    open SCwFᴰOver SᴰOver

    module _
      ((Fᴰ , F-ty , F-tm
           , presTerm , presLocalRep) : SCwFSection S Sᴰ) where

      record PreservesSemanticTypes :
        Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ ℓCᴰ ,ℓ ℓCᴰ' ,ℓ ℓTᴰ ,ℓ ℓTᴰ' ,ℓ 0ℓ ⌉ℓ where
        field
          pres-⟦1⟧ :
            {{S-1 : hasUnitType S}} →
              preservesUnitType S Sᴰ (unit-type {{S-1}})
                (Fᴰ , F-ty , F-tm , presTerm , presLocalRep)
          pres-⟦×⟧ :
            {{S-× : hasProductTypes S}} →
              preservesProdTypes S Sᴰ (product-types {{S-×}})
                (Fᴰ , F-ty , F-tm , presTerm , presLocalRep)
          pres-⟦⇒⟧ :
            {{S-× : hasFunctionTypes S}} →
              preservesFunTypes S Sᴰ (function-types {{S-×}})
                (Fᴰ , F-ty , F-tm , presTerm , presLocalRep)

      PreservesBaseType : ⟨ sig ⟩ → Type _
      PreservesBaseType A = F-ty (↑ty A) ≡ ↑tyᴰ A

      PreservesBaseTypes : Type _
      PreservesBaseTypes = ∀ (A : ⟨ sig ⟩) → PreservesBaseType A

      -- open PshSection
      -- PreservesFunctionSymbol : (f : funsym) → Type _
      -- PreservesFunctionSymbol f = {!!}

      record PreservesSignature :
        Type ⌈ ℓ ,ℓ ℓ' ,ℓ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ ℓCᴰ ,ℓ ℓCᴰ' ,ℓ ℓTᴰ ,ℓ ℓTᴰ' ,ℓ 0ℓ ⌉ℓ where
        field
          pres-sem-types : PreservesSemanticTypes
          pres-base-types : PreservesBaseTypes

    SignaturePreservingSection : Type _
    SignaturePreservingSection = Σ[ Fᴰ ∈ SCwFSection S Sᴰ ] PreservesSignature Fᴰ

  module _
    (sig : Signature ℓ ℓ')
    (SOver : SCwFOver sig ℓC ℓC' ℓT ℓT')
    where
    isFreeSCwFOver : Typeω
    isFreeSCwFOver =
      ∀ {ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'} →
      (SᴰOver : SCwFᴰOver sig SOver ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') →
      SignaturePreservingSection sig SOver SᴰOver
