-- Free category with a terminal object, over a Quiver
module Cubical.Categories.Instances.Free.CategoryWithTerminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sum.Base as Sum hiding (elim; rec)
open import Cubical.Data.Unit
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Weaken as Wk
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Limits as Reindex
import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Reasoning.More

private
  variable
    ℓg ℓg' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Section
open Functor
open UniversalElementᴰ

CategoryWithTerminal : (ℓC ℓC' : Level) → Type _
CategoryWithTerminal ℓC ℓC' = Σ[ C ∈ Category ℓC ℓC' ] Terminal' C

-- freely throw in a terminal object
module _ (Ob : Type ℓg) where

  -- adjoin a new terminal object
  Ob' = Ob ⊎ Unit

  𝟙' : Ob'
  𝟙' = inr tt

  module _ (Q : QuiverOver Ob' ℓg') where
    open Category
    open QuiverOver
    open UniversalElement

    data Exp : Ob' → Ob' → Type (ℓ-max ℓg ℓg') where
      ↑_   : ∀ g → Exp (Q .dom g) (Q .cod g)
      idₑ  : ∀ {A} → Exp A A
      _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)
      !ₑ : ∀ {A} → Exp A 𝟙'
      isProp!ₑ : ∀ {A} → isProp (Exp A 𝟙')

    FC : Category _ _
    FC .ob = Ob'
    FC .Hom[_,_] = Exp
    FC .id = idₑ
    FC ._⋆_ = _⋆ₑ_
    FC .⋆IdL = ⋆ₑIdL
    FC .⋆IdR = ⋆ₑIdR
    FC .⋆Assoc = ⋆ₑAssoc
    FC .isSetHom = isSetExp

    FCTerminal : Terminal' FC
    FCTerminal .vertex = inr tt
    FCTerminal .element = tt
    FCTerminal .universal A .equiv-proof y =
      uniqueExists !ₑ refl (λ _ _ _ → refl) (λ _ _ → isProp!ₑ _ _)

    FreeCatw/Terminal : CategoryWithTerminal _ _
    FreeCatw/Terminal = (FC , FCTerminal)

    module _ (Cᴰ : Categoryᴰ (FreeCatw/Terminal .fst) ℓCᴰ ℓCᴰ')
      (term'ᴰ : Terminalᴰ Cᴰ (FreeCatw/Terminal .snd)) where

      open TerminalᴰNotation Cᴰ term'ᴰ

      private
        module FC = Category (FreeCatw/Terminal .fst)
        module Cᴰ = Categoryᴰ Cᴰ
        module R = ReasoningMore Cᴰ

      -- given an interpretation of atomic objects
      module _ (ϕ : (v : Ob) → Cᴰ.ob[ inl v ]) where
        -- extend it to all objects
        private
          ϕ* : (v : Ob') → Cᴰ.ob[ v ]
          ϕ* = Sum.elim (λ a → ϕ a) (λ b → term'ᴰ .vertexᴰ)

        -- and given an interpretation of atomic morphisms
        module _ (ψ : (e : Q .mor) →
          Cᴰ.Hom[ ↑ e ][ ϕ* (Q .dom e) , ϕ* (Q .cod e) ]) where

          elim-F-homᴰ : ∀ {d d'} → (f : FC.Hom[ d , d' ]) →
            Cᴰ.Hom[ f ][ ϕ* d , ϕ* d' ]
          elim-F-homᴰ (↑ g) = ψ g
          elim-F-homᴰ idₑ = Cᴰ.idᴰ
          elim-F-homᴰ (f ⋆ₑ g) = elim-F-homᴰ f Cᴰ.⋆ᴰ elim-F-homᴰ g
          elim-F-homᴰ (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ f) i
          elim-F-homᴰ (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ f) i
          elim-F-homᴰ (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ
            (elim-F-homᴰ f) (elim-F-homᴰ g) (elim-F-homᴰ h) i
          elim-F-homᴰ (isSetExp f g p q i j) =
            isSetHomᴰ' Cᴰ
            (elim-F-homᴰ f) (elim-F-homᴰ g)
            (cong elim-F-homᴰ p) (cong elim-F-homᴰ q)
            i j
          elim-F-homᴰ {d = d} !ₑ = !tᴰ (ϕ* d)
          elim-F-homᴰ {d = d} (isProp!ₑ f g i) =
            (R.rectifyOut {p' = isProp!ₑ f g}
              $ 𝟙extensionalityᴰ
                {f = _ , elim-F-homᴰ f}{g = _ , elim-F-homᴰ g})
            i

          elim : GlobalSection Cᴰ
          elim .F-obᴰ = ϕ*
          elim .F-homᴰ = elim-F-homᴰ
          elim .F-idᴰ = refl
          elim .F-seqᴰ _ _ = refl

    module _
      {D : Category ℓD ℓD'}
      (F : Functor FC D)
      (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
      (term'ᴰ : Terminalⱽ Dᴰ (F ⟅ inr _ ⟆))
      where
      private
        module Dᴰ = Categoryᴰ Dᴰ
        open TerminalⱽNotation _ _ term'ᴰ
      module _ (ϕ : ∀ o → Dᴰ.ob[ F ⟅ inl o ⟆ ]) where
        private
          ϕ* : ∀ v → Dᴰ.ob[ F ⟅ v ⟆ ]
          ϕ* = Sum.elim ϕ λ _ → 𝟙ⱽ
        module _ (ψ : ∀ e → Dᴰ.Hom[ F ⟪ ↑ e ⟫ ][ ϕ* _ , ϕ* _ ]) where
          elimLocal : Section F Dᴰ
          elimLocal = GlobalSectionReindex→Section _ _
            (elim _ (Terminalⱽ→Terminalᴰ _ (TerminalⱽReindex term'ᴰ)) ϕ ψ)

    module _ (D : Category ℓD ℓD')
             (term' : Terminal' D)
             (ϕ : Ob → D .ob)
             where
      private
        open TerminalNotation term'
        ϕ* : Ob' → D .ob
        ϕ* = Sum.elim (λ a → ϕ a) λ _ → 𝟙

      module _ (ψ : ∀ e → D [ ϕ* (Q .dom e) , ϕ* (Q .cod e) ]) where
        rec : Functor FC D
        rec = Wk.introS⁻ (elim (weaken FC D) (termWeaken _ term') ϕ ψ)
