module Cubical.Categories.WithFamilies.Simple.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Presheaf

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed

open Category

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

-- It's unclear to me if this is just as bad performance-wise as
-- making SCwF/SCwFᴰ into records
module SCwFNotation (the-scwf : SCwF ℓC ℓC' ℓT ℓT') where
  C = the-scwf .fst
  Ty = the-scwf .snd .fst
  Tm = the-scwf .snd .snd .fst
  module Tm⟨_⟩ (A : Ty) = PresheafNotation (Tm A)
  term = the-scwf .snd .snd .fst
  ext = the-scwf .snd .snd .snd

module SCwFᴰNotation
  {the-scwf : SCwF ℓC ℓC' ℓT ℓT'}
  (the-scwfᴰ : SCwFᴰ the-scwf ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
  where
  open SCwFNotation the-scwf public
  Cᴰ = the-scwfᴰ .fst
  module Cᴰ = Fibers Cᴰ
  Tyᴰ = the-scwfᴰ .snd .fst
  Tmᴰ = the-scwfᴰ .snd .snd .fst
  module Tmᴰ⟨_⟩ {A : Ty} (Aᴰ : Tyᴰ A) = PresheafᴰNotation (Tmᴰ Aᴰ)
  termᴰ = the-scwfᴰ .snd .snd .snd .fst
  module termᴰ = UniversalElementᴰ termᴰ
  extᴰ = the-scwfᴰ .snd .snd .snd .snd
  module extᴰ⟨_,_⟩ {Γ}{A} (Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Tyᴰ A) =
    UniversalElementᴰ (extᴰ Aᴰ Γᴰ)

