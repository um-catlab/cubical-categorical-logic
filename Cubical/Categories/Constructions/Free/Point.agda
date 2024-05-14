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

        --open import Cubical.Categories.Constructions.Free.Category.Quiver
        --
        -- I don't want to introduce a path or just say
        -- that the terminal object needs to be mapped to something terminal'
        -- which has a similar issue
        --PointInterp : (C : Category ℓC ℓC')(term' : Terminal' C) → Type _
        --PointInterp C term' = Σ[ ı ∈ Interp (Ob' , Q) C ] {!!}

        record Interp (C : Category ℓC ℓC')(term' : Terminal' C)
            : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓC ℓC')) where
            module C = Category C
            field
                interp-v : Ob → C .ob
            ϕ : Ob' → C .ob
            ϕ = rec interp-v (λ _ → term' .vertex) -- preserve chosen terminal objects
            field
                interp-e : (g : Q .mor) → C.Hom[ ϕ (Q .dom g) , ϕ (Q .cod g) ]

        -- try to avoid transport issues
        record Interp' (C : Category ℓC ℓC')(term' : Terminal' C) : Type ((ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓC ℓC'))) where
            module C = Category C
            field
                interp-v' : Σ[ ϕ ∈ (Ob' → C .ob) ] ϕ (inr tt) ≡ term' .vertex
                interp-e' : (g : Q .mor) → C.Hom[ interp-v' .fst (Q .dom g) , interp-v' .fst (Q .cod g) ]

        open Interp
        open Interp'

        module FPC = Category (FreePointCat .fst)

        lem : ∀ A → A ≡ rec {C = Ob'} inl (λ _ → inr tt) A
        lem (inl _) = refl
        lem (inr _) = refl

        η : Interp (FreePointCat .fst) (FreePointCat .snd)
        η .interp-v = inl
        -- NOTE: this transport is necessary because we don't have
        -- (even a weak) eta for sum types?
        η .interp-e g =
            transport (cong₂ (λ p q → FPC.Hom[ p , q ]) (lem (Q .dom g)) (lem (Q .cod g))) (↑ g)

        η' : Interp' (FreePointCat .fst)(FreePointCat .snd)
        η' .interp-v' = (λ x → x) , refl
        η' .interp-e' g = ↑ g

        module _ {C : Category ℓC ℓC'}{term' : Terminal' C}
            (ı : Interp C term')
            (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')(term'ᴰ : Terminalᴰ Cᴰ term')
            where
            private module Cᴰ = Categoryᴰ Cᴰ
            open UniversalElementᴰ
            record Interpᴰ : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓCᴰ ℓCᴰ')) where
                field
                    interp-vᴰ : (v : Ob) → Cᴰ.ob[ ı .interp-v v ]
                ψ : (v : Ob') → Cᴰ.ob[ ϕ ı v  ]
                ψ = Sum.elim interp-vᴰ (λ _ → term'ᴰ .vertexᴰ)
                field
                    interp-eᴰ : (e : Q .mor) → Cᴰ.Hom[ ı .interp-e e ][ ψ (Q .dom e) , ψ (Q .cod e) ]
        module _ {C : Category ℓC ℓC'}{term' : Terminal' C}
            (ı : Interp' C term')
            (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')(term'ᴰ : Terminalᴰ Cᴰ term')
            where
            private module Cᴰ = Categoryᴰ Cᴰ
            open UniversalElementᴰ
            record Interpᴰ' : Type ((ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓCᴰ ℓCᴰ'))) where
                field
                    interp-vᴰ' : Σ[ ϕ ∈ ((v : Ob') → Cᴰ.ob[ ı .interp-v' .fst v ]) ]
                        ϕ (inr tt) ≡ transport (cong (λ x → Cᴰ.ob[ x ]) (sym (ı .interp-v' .snd))) (term'ᴰ .vertexᴰ)
                    interp-eᴰ' : (e : Q .mor) →
                        Cᴰ.Hom[ ı .interp-e' e ][ interp-vᴰ' .fst (Q .dom e) , interp-vᴰ' .fst (Q .cod e) ]

        --module _ (Cᴰ : Categoryᴰ (FreePointCat .fst) ℓCᴰ ℓCᴰ')
        --    (term'ᴰ : Terminalᴰ Cᴰ (FreePointCat .snd))
        --    (ıᴰ : Interpᴰ η Cᴰ term'ᴰ) where

        --    private module Cᴰ = Categoryᴰ Cᴰ
        --    open Section
        --    open Interpᴰ

        --    elim-F-homᴰ : ∀ {d d'} → (f : FPC.Hom[ d , d' ]) →
        --        Cᴰ.Hom[ f ][ transport (sym (congS (λ x → Cᴰ.ob[ x ]) (lem d))) (ψ ıᴰ d) , transport (sym (congS (λ x → Cᴰ.ob[ x ]) (lem d'))) (ψ ıᴰ d') ]
        --    elim-F-homᴰ (↑ g) = {!ıᴰ .interp-eᴰ g!}

        --    elim : GlobalSection Cᴰ
        --    elim .F-obᴰ v = transport (congS (λ x → Cᴰ.ob[ x ]) (sym (lem v))) (ψ ıᴰ v)
        --    elim .F-homᴰ = elim-F-homᴰ
        --    elim .F-idᴰ = {!!}
        --    elim .F-seqᴰ = {!!}

        module _ (Cᴰ : Categoryᴰ (FreePointCat .fst) ℓCᴰ ℓCᴰ')
            (term'ᴰ : Terminalᴰ Cᴰ (FreePointCat .snd))
            (ıᴰ : Interpᴰ' η' Cᴰ term'ᴰ) where

            private module Cᴰ = Categoryᴰ Cᴰ
            open Section
            open Interpᴰ'
            open import Cubical.Foundations.HLevels
            open UniversalElementᴰ

            -- copied from Quiver.agda
            elim-F-homᴰ' : ∀ {d d'} → (f : FPC.Hom[ d , d' ]) →
                Cᴰ.Hom[ f ][ ıᴰ .interp-vᴰ' .fst d , ıᴰ .interp-vᴰ' .fst d' ]
            elim-F-homᴰ' (↑ g) = ıᴰ .interp-eᴰ' g
            elim-F-homᴰ' idₑ = Cᴰ.idᴰ
            elim-F-homᴰ' (f ⋆ₑ g) = elim-F-homᴰ' f Cᴰ.⋆ᴰ elim-F-homᴰ' g
            elim-F-homᴰ' (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ' f) i
            elim-F-homᴰ' (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ' f) i
            elim-F-homᴰ' (⋆ₑAssoc f g h i) =
                Cᴰ.⋆Assocᴰ (elim-F-homᴰ' f) (elim-F-homᴰ' g) (elim-F-homᴰ' h) i
            elim-F-homᴰ' (isSetExp f g p q i j) = isOfHLevel→isOfHLevelDep 2
                ((λ x → Cᴰ.isSetHomᴰ))
                ((elim-F-homᴰ' f)) ((elim-F-homᴰ' g))
                ((cong elim-F-homᴰ' p)) ((cong elim-F-homᴰ' q))
                ((isSetExp f g p q))
                i j
            elim-F-homᴰ' {d = d} !ₑ =
                transport
                (cong (λ x → Cᴰ.Hom[ !ₑ ][ ıᴰ .interp-vᴰ' .fst d , x ]) (sym (transportRefl {!ıᴰ .interp-vᴰ' .fst (inr tt)!}) ∙ sym (ıᴰ .interp-vᴰ' .snd) ))
                (!t'ᴰ Cᴰ term'ᴰ (ıᴰ .interp-vᴰ' .fst d) .fst)
            elim-F-homᴰ' (isProp!ₑ f g i) = {!!}

            open import Cubical.Categories.Displayed.Reasoning

            elim' : GlobalSection Cᴰ
            elim' .F-obᴰ v = ıᴰ .interp-vᴰ' .fst v
            elim' .F-homᴰ = elim-F-homᴰ'
            elim' .F-idᴰ = refl
            elim' .F-seqᴰ _ _ = refl
