module Cubical.Categories.WithFamilies.Simple.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed

open Category
open UniversalElement
open UniversalElementᴰ

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

  _,,_ : C .ob → Ty → C .ob
  Γ ,, A = ext A Γ .vertex

  _⊢_ : C .Category.ob → Ty → Type _
  Γ ⊢ A = ⟨ Tm A ⟅ Γ ⟆ ⟩

  TY : Categoryᴰ C _ _
  TY = PropertyOver C λ _ → Ty

  open Functor

  module _ (A : Ty) where

    ExtendContextProf : Profunctor C C (ℓ-max ℓC' ℓT')
    ExtendContextProf .F-ob Γ = (C [-, Γ ]) ×Psh Tm A
    ExtendContextProf .F-hom f =
      PshHom→NatTrans $ ×PshIntro (π₁ _ _ ⋆PshHom yoRec _ f) (π₂ _ _)
    ExtendContextProf .F-id =
      makeNatTransPath $ funExt₂ $ λ c p → ΣPathP (C .⋆IdR _ , refl)
    ExtendContextProf .F-seq f g =
      makeNatTransPath $ funExt₂ $ λ c p → ΣPathP ((sym $ C .⋆Assoc _ _ _) , refl)

    open Functor
    open UniversalElement
    private
      module ext Γ = UniversalElementNotation (ext A Γ)
      module C = Category C

    ExtendContext : Functor C C
    ExtendContext = FunctorComprehension ExtendContextProf (ext A)

  sole : Ty → C .ob
  sole = TermCtx.𝟙 ,,_

  module _ (A B : Ty) where
    open Functor

    opaque
      Cont : Presheaf C ℓT'
      Cont = Tm B ∘F ((ExtendContext A) ^opF)

module SCwFᴰNotation
  (the-scwf : SCwF ℓC ℓC' ℓT ℓT')
  (the-scwfᴰ : SCwFᴰ the-scwf ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
  where
  open SCwFNotation the-scwf
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

  _,,ᴰ_ : {Γ : C .ob} {A : Ty} → (Γᴰ : Cᴰ.ob[ Γ ]) → (Aᴰ : Tyᴰ A) → Cᴰ.ob[ Γ ,, A ]
  Γᴰ ,,ᴰ Aᴰ = extᴰ Aᴰ Γᴰ .vertexᴰ

  soleᴰ : {A : Ty} → (Aᴰ : Tyᴰ A) → Cᴰ.ob[ sole A ]
  soleᴰ = termᴰ .vertexᴰ ,,ᴰ_

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
