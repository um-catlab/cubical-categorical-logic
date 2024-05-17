{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Displayed.Fibration.More where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Fibration

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
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open FiberedFunctor

module _ {C : Category ℓC ℓC'} where
  open CartesianOver

module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
  (F : Functor B C)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (fibterm : hasFibTerminal' Cᴰ) where
  open import Cubical.Categories.Displayed.Properties
  open UniversalElementᴰ
  fib-stable-under-reind : hasFibTerminal' (reindex Cᴰ F)
  -- TODO: why do I have to eta expand this?
  fib-stable-under-reind b .vertexᴰ = fibterm (F ⟅ b ⟆) .vertexᴰ
  fib-stable-under-reind b .elementᴰ = fibterm (F ⟅ b ⟆) .elementᴰ
  fib-stable-under-reind b .universalᴰ = fibterm (F ⟅ b ⟆) .universalᴰ

  module _ (term' : Terminal' B) where
    baz : Terminalᴰ (reindex Cᴰ F) term'
    baz = FibTerm→Termᴰ (reindex Cᴰ F) term' fib-stable-under-reind

    --module _ (isfib : isFibration Cᴰ) where

    --  open import Cubical.Categories.Displayed.Reasoning Cᴰ
    --  open CartesianOver
    --  module C = Category C
    --  open import Cubical.Foundations.HLevels

    --  c-o : AllCartesianOvers Cᴰ
    --  c-o = isFibration→AllCartesianOvers Cᴰ isfib

    --  -- moreover, if Cᴰ is a fibration, it's an iff
    --  -- TODO: this is easy on paper but...
    --  Termᴰ→FibTerm : Terminalᴰ Cᴰ term → hasFibTerminal'
    --  Termᴰ→FibTerm termᴰ c .vertexᴰ = !cᴰ .f*cᴰ' -- the pullback of Tᴰ over !
    --    where
    --    !cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (!t' term c .fst)
    --    !cᴰ = c-o (termᴰ .vertexᴰ) (!t' term c .fst)
    --  Termᴰ→FibTerm termᴰ c .elementᴰ = tt -- identity?
    --  Termᴰ→FibTerm termᴰ c .universalᴰ {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof fᴰ =
    --    uniqueExists
    --    (l .fst .fst)
    --    refl
    --    (λ _ _ _ → refl)
    --    λ a' p → cong (λ x → x .fst) (l .snd (a' , ≡→≡[] {!!ᴰ Cᴰ termᴰ ? .snd ?!}))
    --    where
    --    !cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (!t' term c .fst)
    --    !cᴰ = c-o (termᴰ .vertexᴰ) (!t' term c .fst)
    --    goal : !t' term x .fst ≡ f C.⋆ !t' term c .fst
    --    goal = !t' term x .snd (f C.⋆ !t' term c .fst)
    --    l : ∃![ fᴰ' ∈ Cᴰ.Hom[ f ][ xᴰ , !cᴰ .f*cᴰ' ] ] ((!t'ᴰ Cᴰ termᴰ xᴰ .fst) Cᴰ.≡[ goal ] (fᴰ' Cᴰ.⋆ᴰ !cᴰ .π))

    --    l = uniqueExists
    --      (!cᴰ .isCartesian xᴰ f (reind goal (!t'ᴰ Cᴰ termᴰ xᴰ .fst)) .fst .fst)
    --      (≡→≡[] (sym (!cᴰ .isCartesian xᴰ f (reind goal (!t'ᴰ Cᴰ termᴰ xᴰ .fst)) .fst .snd)))
    --      (λ _ pᴰ qᴰ → isSet→SquareP (λ _ _ → Cᴰ.isSetHomᴰ) pᴰ qᴰ _ _)
    --      λ fᴰ' pᴰ → cong (λ x → x .fst)
    --        (isContr→isProp
    --          (!cᴰ .isCartesian xᴰ f (reind goal (!t'ᴰ Cᴰ termᴰ xᴰ .fst)))
    --          ((!cᴰ .isCartesian xᴰ f (reind goal (!t'ᴰ Cᴰ termᴰ xᴰ .fst))) .fst) (fᴰ' , sym (fromPathP pᴰ)))
    --  --Termᴰ→FibTerm termᴰ c .universalᴰ {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof fᴰ =
    --  --  uniqueExists (ccc .fst .fst) refl
    --  --  (λ _ p q → isSetUnit tt tt p q)
    --  --  λ fᴰ x  → congS (λ x → x .fst) (ccc .snd (fᴰ , eqq fᴰ))
    --  --  where
    --  --  --abc Cᴰ termᴰ ? .snd ?
    --  --  !cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (!t' term c .fst)
    --  --  !cᴰ = c-o (termᴰ .vertexᴰ) (!t' term c .fst)
    --  --  eqq : ∀ fᴰ →
    --  --    fᴰ Cᴰ.⋆ᴰ (!cᴰ .π) ≡
    --  --    reind (!t' term x .snd (f C.⋆ !t' term c .fst))
    --  --    (!t'ᴰ Cᴰ termᴰ xᴰ .fst)
    --  --  --eqq fᴰ = fᴰ Cᴰ.⋆ᴰ (!cᴰ .π) ≡⟨ reind-filler {!!t' term x .snd ?!} (fᴰ Cᴰ.⋆ᴰ (!cᴰ .π)) ⟩ {!!} ≡⟨ {!!} ⟩ {!!}
    --  --  eqq fᴰ = sym (≡→≡[] (symP {!!}))
    --  --  f⋆!cᴰ : CartesianOver Cᴰ (termᴰ .vertexᴰ) (f C.⋆ (!t' term c .fst))
    --  --  f⋆!cᴰ = {!c-o (termᴰ .vertexᴰ) (f C.⋆ (!t' term c .fst))!}
    --  --  ccc : ∃![ gᴰ ∈ Cᴰ.Hom[ f ][ xᴰ , !cᴰ .f*cᴰ' ] ] gᴰ Cᴰ.⋆ᴰ !cᴰ .π ≡
    --  --    reind (!t' term x .snd (f C.⋆ (!t' term c .fst))) (!t'ᴰ Cᴰ termᴰ xᴰ .fst)
    --  --  ccc = (!cᴰ .isCartesian xᴰ f (f⋆!cᴰ .π))

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
