{-
Additions to Cubical.Categories.Displayed.Reasoning: `rectifyOut`, a fused
`rectify ∘ ≡out`.

The result type of `≡out` mentions its argument,

  ≡out : (e : (f , fᴰ) ≡ (g , gᴰ)) → fᴰ ≡[ fst (PathPΣ e) ] gᴰ

so writing `rectify (≡out e)` forces `rectify`'s implicit `{p}` to be solved
as `fst (PathPΣ e)`, and the elaborated term contains a second copy of `e`.
Since `e` is typically a long reasoning chain, that roughly doubles its size.
`rectifyOut` leaves the result index free, so `e` is stored once.

This belongs upstream next to `rectify`; see
Notes/displayed-reasoning-rectifyOut.patch.
-}
module Cubical.Categories.Displayed.Reasoning.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
import      Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module ReasoningMore
  {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open Reasoning Cᴰ public
  open Categoryᴰ Cᴰ using (ob[_]; Hom[_][_,_]; _≡[_]_)
  private module C = Category C

  rectifyOut : {a b : C.ob}{f g : C [ a , b ]}{p' : f ≡ g}
      {aᴰ : ob[ a ]}{bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
    → Path _ (f , fᴰ) (g , gᴰ)
    → fᴰ ≡[ p' ] gᴰ
  rectifyOut e = rectify (≡out e)
