{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Displayed.Fibration.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Fibration.Base

open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Data.Unit
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Functor

open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open FiberedFunctor

module _ {C : Category ℓC ℓC'} where
  open CartesianOver

  1/C = Unitᴰ C

  isFib1/C : isFibration 1/C
  isFib1/C _ = CartesianOver→CartesianLift 1/C ue
    where
    ue : CartesianOver 1/C tt _
    ue .f*cᴰ' = tt
    ue .π = tt
    ue .isCartesian _ _ _ =
      uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _)
      λ _ _ → isPropUnit _ _

  -- terminal fibration over C, ie the identity fibration
  TerminalFib : Fibration C _ _
  TerminalFib = (1/C , isFib1/C)

  module _ (p : Fibration C ℓCᴰ ℓCᴰ') where
    open Functorᴰ

    !/C : FiberedFunctor p TerminalFib
    !/C .base = Id
    !/C .over .F-obᴰ _ = tt
    !/C .over .F-homᴰ _ = tt
    !/C .over .F-idᴰ = refl
    !/C .over .F-seqᴰ _ _ = refl
    !/C .preserves-cartesian _ _ _ _ _ _ _ _ =
        uniqueExists tt (isPropUnit tt tt)
        (λ _ p q → isSetUnit tt tt p q) λ _ _ → isPropUnit tt tt

-- This makes sense for any displayed category, but is traditionally used for fibrations
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  -- fibered terminal objects, in terms of UniversalElementᴰ
  hasFibTerminal' : Type _
  hasFibTerminal' = (c : C .ob) → FibTerminalᴰ Cᴰ c

  module _ (term : Terminal' C) where

    open FibTerminalᴰNotation Cᴰ
    open UniversalElementᴰ
    open UniversalElement
    module Cᴰ = Categoryᴰ Cᴰ

    -- if the base has [structure], and Cᴰ has fibered [structure], then Cᴰ has displayed [structure]
    FibTerm→Termᴰ : hasFibTerminal' → Terminalᴰ Cᴰ term
    FibTerm→Termᴰ fibterm .vertexᴰ = 1ᴰ (term .vertex) (fibterm (term .vertex))
    FibTerm→Termᴰ fibterm .elementᴰ = tt
    FibTerm→Termᴰ fibterm .universalᴰ  {xᴰ = xᴰ} {f = f} .equiv-proof _ =
      uniqueExists (!tᴰ (term .vertex) 𝟙ᴰ f xᴰ) refl
      (λ _ p q →
        TerminalᴰSpec Cᴰ .Functorᴰ.F-obᴰ xᴰ
        (TerminalPresheaf {C = C} .Functor.F-hom f (term .element)) .snd tt tt p q)
        λ fᴰ' _ → !tᴰ-unique (term .vertex) 𝟙ᴰ f xᴰ .snd fᴰ'
      where
      𝟙ᴰ : FibTerminalᴰ Cᴰ (term .vertex)
      𝟙ᴰ = (fibterm (term .vertex))

    module _ (isfib : isFibration Cᴰ) where

      open import Cubical.Categories.Displayed.Reasoning Cᴰ
      open CartesianOver
      module C = Category C

      c-o : AllCartesianOvers Cᴰ
      c-o = isFibration→AllCartesianOvers Cᴰ isfib

      -- moreover, if Cᴰ is a fibration, it's an iff
      -- TODO: this is easy on paper but...
      Termᴰ→FibTerm : Terminalᴰ Cᴰ term → hasFibTerminal'
      Termᴰ→FibTerm termᴰ c .vertexᴰ = !cᴰ .f*cᴰ' -- the pullback of Tᴰ over !
        where
        !cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (!t' term c .fst)
        !cᴰ = c-o (termᴰ .vertexᴰ) (!t' term c .fst)
      Termᴰ→FibTerm termᴰ c .elementᴰ = tt -- identity?
      Termᴰ→FibTerm termᴰ c .universalᴰ {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof fᴰ =
        uniqueExists (ccc .fst .fst) refl
        (λ _ p q → isSetUnit tt tt p q)
        λ fᴰ x  → congS (λ x → x .fst) (ccc .snd (fᴰ , eqq fᴰ))
        where
        --abc Cᴰ termᴰ ? .snd ?
        !cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (!t' term c .fst)
        !cᴰ = c-o (termᴰ .vertexᴰ) (!t' term c .fst)
        eqq : ∀ fᴰ →
          fᴰ Cᴰ.⋆ᴰ (!cᴰ .π) ≡
          reind (!t' term x .snd (f C.⋆ !t' term c .fst))
          (!t'ᴰ Cᴰ termᴰ xᴰ .fst)
        --eqq fᴰ = fᴰ Cᴰ.⋆ᴰ (!cᴰ .π) ≡⟨ reind-filler {!!t' term x .snd ?!} (fᴰ Cᴰ.⋆ᴰ (!cᴰ .π)) ⟩ {!!} ≡⟨ {!!} ⟩ {!!}
        eqq fᴰ = sym (≡→≡[] (symP {!!}))
        f⋆!cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (f C.⋆ (!t' term c .fst))
        f⋆!cᴰ = {!c-o (termᴰ .vertexᴰ) (f C.⋆ (!t' term c .fst))!}
        ccc : ∃![ gᴰ ∈ Cᴰ.Hom[ f ][ xᴰ , !cᴰ .f*cᴰ' ] ] gᴰ Cᴰ.⋆ᴰ !cᴰ .π ≡
          reind (!t' term x .snd (f C.⋆ (!t' term c .fst))) (!t'ᴰ Cᴰ termᴰ xᴰ .fst)
        ccc = (!cᴰ .isCartesian xᴰ f (f⋆!cᴰ .π))

module _ {C : Category ℓC ℓC'} (p : Fibration C ℓCᴰ ℓCᴰ') where
  -- Jacobs 1.8.8
  -- Hermida 1.4.1
  -- TODO: no way that's definitionally equivalent to the next thing
  -- well...
  -- Hermida 3.3.3.i: LocalRightAdjointᴰ s are automatically fibered?
  -- Hermida 3.3.6: if C has [structure], a fibration p has fibered [structure] iff ∫p has [structre] and p preserves it
  -- In Jacobs too, TODO: lemma number
  hasFibTerminal : Type _
  hasFibTerminal = LocalRightAdjointᴰ (!/C p .over)
