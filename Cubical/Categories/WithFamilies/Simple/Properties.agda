module Cubical.Categories.WithFamilies.Simple.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Functor

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
  term = the-scwf .snd .snd .snd .fst
  module TermCtx = TerminalNotation term
  ext = the-scwf .snd .snd .snd .snd

  _,,_ = ExtendContextF._,,_ the-scwf
  _⊢_ : C .Category.ob → Ty → Type _
  Γ ⊢ A = ⟨ Tm A ⟅ Γ ⟆ ⟩

  sole : Ty → C .ob
  sole = TermCtx.𝟙 ,,_

module SCwFᴰNotation
  {the-scwf : SCwF ℓC ℓC' ℓT ℓT'}
  (the-scwfᴰ : SCwFᴰ the-scwf ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
  where
  open SCwFNotation the-scwf public
  Cᴰ = the-scwfᴰ .fst
  module Cᴰ = Fibers Cᴰ
  Tyᴰ = the-scwfᴰ .snd .fst
  Tmᴰ = the-scwfᴰ .snd .snd .fst
  module Tmᴰ {A : Ty}{Aᴰ : Tyᴰ A} = PresheafᴰNotation (Tmᴰ Aᴰ)
  termᴰ = the-scwfᴰ .snd .snd .snd .fst
  module termᴰ = UniversalElementᴰ termᴰ
  extᴰ = the-scwfᴰ .snd .snd .snd .snd
  module extᴰ {Γ}{A}{Γᴰ : Cᴰ.ob[ Γ ]}{Aᴰ : Tyᴰ A} =
    UniversalElementᴰ (extᴰ Aᴰ Γᴰ)
  _[_]⊢ᴰ_ : ∀ {Γ A} → Cᴰ.ob[ Γ ] → Γ ⊢ A → Tyᴰ A → Type _
  Γᴰ [ M ]⊢ᴰ Aᴰ = ⟨ Tmᴰ Aᴰ .Functorᴰ.F-obᴰ Γᴰ M ⟩

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S
  open TermCtx
  open UniversalElement


  module _ (A : Ty) where
    private
      module 1,A = UniversalElementNotation (ext A 𝟙)

    TmUE : UniversalElement C (Tm A)
    TmUE .vertex = sole A
    TmUE .element = 1,A.element .snd
    TmUE .universal Γ =
      isIsoToIsEquiv (
        (λ M → 1,A.intro (!t , M)) ,
        (λ M → cong snd 1,A.β) ,
        (λ γ → 1,A.intro≡ (≡-× 𝟙extensionality refl)))

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  isFreeSCwF : Typeω
  isFreeSCwF =
    ∀ {ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level}
      → (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
      → SCwFSection S Sᴰ

  isStrictFreeSCwF : Typeω
  isStrictFreeSCwF =
    ∀ {ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level}
      → (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
      → StrictSection S Sᴰ

  isStrictFreeSCwF→isFreeSCwF : isStrictFreeSCwF → isFreeSCwF
  isStrictFreeSCwF→isFreeSCwF strict-free Sᴰ =
    StrictSection→SCwFSection S Sᴰ (strict-free Sᴰ)
