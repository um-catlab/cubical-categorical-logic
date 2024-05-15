-- Free category with a terminal object
-- (The most trivial structure for doing "end-to-end" gluing)
module Cubical.Categories.Constructions.Free.Point where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sum.Base as Sum hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Properties
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓ ℓg ℓg' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

PointCat : (ℓC ℓC' : Level) → Type _
PointCat ℓC ℓC' = Σ[ C ∈ Category ℓC ℓC' ] Terminal' C

-- freely add in a terminal object
module _ (Ob : Type ℓg) where
    Ob' = Ob ⊎ Unit
    module _ (Q : QuiverOver Ob' ℓg') where
        open Category
        open QuiverOver
        open UniversalElement

        -- copied from Categories.Constructions.Quiver
        -- and suitably modified
        data Exp : Ob' → Ob' → Type (ℓ-max ℓg ℓg') where
            ↑_   : ∀ g → Exp (Q .dom g) (Q .cod g)
            idₑ  : ∀ {A} → Exp A A
            _⋆ₑ_ : ∀ {A B C} → (e : Exp A B) → (e' : Exp B C) → Exp A C
            ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
            ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
            ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
                    → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
            isSetExp : ∀ {A B} → isSet (Exp A B)
            !ₑ : ∀ {A} → (Exp A (inr tt))
            isProp!ₑ : ∀ {A} → isProp (Exp A (inr tt))

        BasePointCat : Category _ _
        BasePointCat .ob = Ob'
        BasePointCat .Hom[_,_] = Exp
        BasePointCat .id = idₑ
        BasePointCat ._⋆_ = _⋆ₑ_
        BasePointCat .⋆IdL = ⋆ₑIdL
        BasePointCat .⋆IdR = ⋆ₑIdR
        BasePointCat .⋆Assoc = ⋆ₑAssoc
        BasePointCat .isSetHom = isSetExp

        Point : Terminal' BasePointCat
        Point .vertex = inr tt
        Point .element = tt
        Point .universal A .equiv-proof y =
            uniqueExists !ₑ refl (λ _ _ _ → refl) (λ _ _ → isProp!ₑ _ _)

        FreePointCat : PointCat _ _
        FreePointCat = (BasePointCat , Point)

        module _ (Cᴰ : Categoryᴰ (FreePointCat .fst) ℓCᴰ ℓCᴰ')
            (term'ᴰ : Terminalᴰ Cᴰ (FreePointCat .snd)) where

            private
                open import Cubical.Foundations.HLevels
                open Section
                open UniversalElementᴰ
                module FPC = Category (FreePointCat .fst)
                module Cᴰ = Categoryᴰ Cᴰ
                open import Cubical.Categories.Displayed.Reasoning
                open TerminalᴰNotation Cᴰ term'ᴰ

            -- interpretation of atomic objects
            module _ (ϕ : (v : Ob) → Cᴰ.ob[ inl v ]) where
                ϕ* : (v : Ob') → Cᴰ.ob[ v ]
                ϕ* = Sum.elim (λ a → ϕ a) (λ b → term'ᴰ .vertexᴰ)

                module _ (ψ : (e : Q .mor) → Cᴰ.Hom[ ↑ e ][ ϕ* (Q .dom e) , ϕ* (Q .cod e) ]) where

                    -- copied from Quiver.agda
                    elim-F-homᴰ : ∀ {d d'} → (f : FPC.Hom[ d , d' ]) →
                        Cᴰ.Hom[ f ][ ϕ* d , ϕ* d' ]
                    elim-F-homᴰ (↑ g) = ψ g
                    elim-F-homᴰ idₑ = Cᴰ.idᴰ
                    elim-F-homᴰ (f ⋆ₑ g) = elim-F-homᴰ f Cᴰ.⋆ᴰ elim-F-homᴰ g
                    elim-F-homᴰ (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ f) i
                    elim-F-homᴰ (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ f) i
                    elim-F-homᴰ (⋆ₑAssoc f g h i) =
                        Cᴰ.⋆Assocᴰ (elim-F-homᴰ f) (elim-F-homᴰ g) (elim-F-homᴰ h) i
                    elim-F-homᴰ (isSetExp f g p q i j) = isOfHLevel→isOfHLevelDep 2
                        ((λ x → Cᴰ.isSetHomᴰ))
                        ((elim-F-homᴰ f)) ((elim-F-homᴰ g))
                        ((cong elim-F-homᴰ p)) ((cong elim-F-homᴰ q))
                        ((isSetExp f g p q))
                        i j
                    elim-F-homᴰ {d = d} !ₑ = !tᴰ (ϕ* d)
                    elim-F-homᴰ {d = d} (isProp!ₑ f g i) = goal i
                        where
                        goal : elim-F-homᴰ f Cᴰ.≡[ isProp!ₑ f g ] elim-F-homᴰ g
                        goal = ≡[]-rectify Cᴰ
                            (≡[]∙ Cᴰ _ _
                            (𝟙ηᴰ {f = f} (elim-F-homᴰ f))
                            (symP (𝟙ηᴰ {f = g} (elim-F-homᴰ g))))

                    elim' : GlobalSection Cᴰ
                    elim' .F-obᴰ = ϕ*
                    elim' .F-homᴰ = elim-F-homᴰ
                    elim' .F-idᴰ = refl
                    elim' .F-seqᴰ _ _ = refl
