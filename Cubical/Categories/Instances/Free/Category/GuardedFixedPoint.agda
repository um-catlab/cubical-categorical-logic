module Cubical.Categories.Instances.Free.Category.GuardedFixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)
import Cubical.HITs.SetTruncation as Trunc

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open UniversalElement

data Ob : Type where
  [RetBool] [1] : Ob

data Exp : Ob → Ob → Type where
  idₑ : ∀ {A} → Exp A A
  _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
  ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
  ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
  ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
          → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
  isSetExp : ∀ {A B} → isSet (Exp A B)

  -- [1] is terminal
  []ₑ : ∀ {A} → Exp A [1]
  1ηₑ : ∀ {A}{M : Exp A [1]} → M ≡ []ₑ

  -- [RetBool] contains constants
  [tru] [fls] : Exp [1] [RetBool]
  [ifthen_else_] : ∀ {B}
    → Exp [1] B
    → Exp [1] B
    → Exp [RetBool] B

  -- delay/step/pay/fuel
  [δ] : ∀ {B} → Exp B B
  [ite-δ] : ∀ {B} {M1 M2 : Exp [1] B}
    → [δ] ⋆ₑ [ifthen M1 else M2 ] ≡ [ifthen M1 else M2 ] ⋆ₑ [δ]

  -- guarded fixed points
  [fix] : ∀ {B} → Exp B B → Exp [1] B
  [fix]-gfix : ∀ {B} (M : Exp B B)
    → [fix] M ≡ ([fix] M ⋆ₑ ([δ] ⋆ₑ M))

quoteBool : Bool → Exp [1] [RetBool]
quoteBool false = [fls]
quoteBool true = [tru]

EXP : Category ℓ-zero ℓ-zero
EXP .ob = Ob
EXP .Hom[_,_] = Exp
EXP .id = idₑ
EXP ._⋆_ = _⋆ₑ_
EXP .⋆IdL = ⋆ₑIdL
EXP .⋆IdR = ⋆ₑIdR
EXP .⋆Assoc = ⋆ₑAssoc
EXP .isSetHom = isSetExp



[1]-TERMINAL : Terminal' EXP
[1]-TERMINAL .vertex = [1]
[1]-TERMINAL .element = tt
[1]-TERMINAL .universal Γ = isIsoToIsEquiv
  ( (λ z → []ₑ)
  , (λ _ → refl)
  , (λ _ → sym 1ηₑ))

module _ (Cᴰ : Categoryᴰ EXP ℓCᴰ ℓCᴰ') (1ᴰ : Terminalᴰ Cᴰ [1]-TERMINAL)
  where
  private
    module Cᴰ = Fibers Cᴰ
    module 1ᴰ = TerminalᴰNotation Cᴰ {term = [1]-TERMINAL} 1ᴰ

  -- this is all just a bunch of one-off compatibility lemmas for now
  module _
    (⟦RetBool⟧ : Cᴰ.ob[ [RetBool] ])
    ([truᴰ] : Cᴰ.Hom[ [tru] ][ 1ᴰ .fst , ⟦RetBool⟧ ])
    ([flsᴰ] : Cᴰ.Hom[ [fls] ][ 1ᴰ .fst , ⟦RetBool⟧ ])
    ([ifᴰthen_else_] : ∀ {B} {Bᴰ : Cᴰ.ob[ B ]}
      {M1 M2 : Exp [1] B}
      → Cᴰ.Hom[ M1 ][ 1ᴰ .fst , Bᴰ ]
      → Cᴰ.Hom[ M2 ][ 1ᴰ .fst , Bᴰ ]
      → Cᴰ.Hom[ [ifthen M1 else M2 ] ][ ⟦RetBool⟧ , Bᴰ ]
      )
    (δᴰ : ∀ {B}{Bᴰ : Cᴰ.ob[ B ]} → Cᴰ.Hom[ [δ] ][ Bᴰ , Bᴰ ])
    (δᴰ-ifᴰ : ∀ {B} {Bᴰ : Cᴰ.ob[ B ]}
      {M1 M2 : Exp [1] B}
      → (M1ᴰ : Cᴰ.Hom[ M1 ][ 1ᴰ .fst , Bᴰ ])
      → (M2ᴰ : Cᴰ.Hom[ M2 ][ 1ᴰ .fst , Bᴰ ])
      → (δᴰ Cᴰ.⋆ᴰ [ifᴰthen M1ᴰ else M2ᴰ ]) Cᴰ.≡[ [ite-δ] ] [ifᴰthen M1ᴰ else M2ᴰ ] Cᴰ.⋆ᴰ δᴰ
      )
    (fixᴰ : ∀ {B}{Bᴰ : Cᴰ.ob[ B ]}{M : Exp B B}
      → (Mᴰ : Cᴰ.Hom[ M ][ Bᴰ , Bᴰ ])
      → Cᴰ.Hom[ [fix] M ][ 1ᴰ .fst , Bᴰ ])
    ([fix]-gfixᴰ : ∀ {B}{Bᴰ : Cᴰ.ob[ B ]}{M : Exp B B}
      → (Mᴰ : Cᴰ.Hom[ M ][ Bᴰ , Bᴰ ])
      → fixᴰ Mᴰ Cᴰ.≡[ [fix]-gfix M ] fixᴰ Mᴰ Cᴰ.⋆ᴰ δᴰ Cᴰ.⋆ᴰ Mᴰ)
    where
    elimOb : ∀ B → Cᴰ.ob[ B ]
    elimOb [RetBool] = ⟦RetBool⟧
    elimOb [1] = 1ᴰ .fst

    elimHom : ∀ {B1 B2} → (M : Exp B1 B2) → Cᴰ.Hom[ M ][ elimOb B1 , elimOb B2 ]
    elimHom idₑ = Cᴰ.idᴰ
    elimHom (M ⋆ₑ M₁) = elimHom M Cᴰ.⋆ᴰ elimHom M₁
    elimHom (⋆ₑIdL M i) = Cᴰ.⋆IdLᴰ (elimHom M) i
    elimHom (⋆ₑIdR M i) = Cᴰ.⋆IdRᴰ (elimHom M) i
    elimHom (⋆ₑAssoc M M₁ M₂ i) = Cᴰ.⋆Assocᴰ (elimHom M) (elimHom M₁) (elimHom M₂) i
    elimHom (isSetExp M M₁ x y i i₁) = isSetHomᴰ' Cᴰ (elimHom M) (elimHom M₁) (λ i → elimHom (x i)) ((λ i → elimHom (y i))) i i₁
    elimHom []ₑ = 1ᴰ.introᴰ _
    elimHom (1ηₑ {M = M} i) = Cᴰ.rectify {e' = 1ηₑ} (1ᴰ.ηᴰ (elimHom M)) i
    elimHom [tru] = [truᴰ]
    elimHom [fls] = [flsᴰ]
    elimHom [ifthen M else M₁ ] = [ifᴰthen elimHom M else elimHom M₁ ]
    elimHom [δ] = δᴰ
    elimHom ([ite-δ] {M1 = M1}{M2 = M2} i) = δᴰ-ifᴰ (elimHom M1) (elimHom M2) i
    elimHom ([fix] M) = fixᴰ (elimHom M)
    elimHom ([fix]-gfix M i) = [fix]-gfixᴰ (elimHom M) i

    elim : GlobalSection Cᴰ
    elim .Section.F-obᴰ = elimOb
    elim .Section.F-homᴰ = elimHom
    elim .Section.F-idᴰ = refl
    elim .Section.F-seqᴰ _ _ = refl

open import Cubical.Data.Nat as Nat hiding (elim)
import Cubical.Data.Equality as Eq
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory as TotalCat hiding (elim)
open import Cubical.Categories.Displayed.Instances.PropertyOver as PropertyOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.HLevels

ℕType ωType ωSet : (ℓ : Level) → Type _
ℕType ℓ = ℕ → Type ℓ
ωType ℓ = Σ[ Xi ∈ (ℕ → Type ℓ) ] (∀ i → Xi (suc i) → Xi i)
ωSet ℓ = Σ[ X ∈ ωType ℓ ] ∀ i → isSet (X .fst i)

ℕHom : (X : ℕType ℓ)(Y : ℕType ℓ') → Type _
ℕHom X Y = ∀ n → X n → Y n

ωHom : (X : ωType ℓ)(Y : ωType ℓ') → Type (ℓ-max ℓ ℓ')
ωHom X Y = Σ[ f ∈ (∀ n → X .fst n → Y .fst n) ]
  ∀ n x x'
    → X .snd n x ≡ x'
    → Y .snd n (f (suc n) x) ≡ f n x'

ωId : (X : ωType ℓ) → ωHom X X
ωId X .fst = λ n z → z
ωId X .snd = λ n x y z → z

_ω⋆_ : {X : ωType ℓ}{Y : ωType ℓ'}{Z : ωType ℓ''}
  → ωHom X Y
  → ωHom Y Z
  → ωHom X Z
(f ω⋆ g) .fst = λ n z → g .fst n (f .fst n z)
_ω⋆_ {X = X}{Y = Y}{Z = Z} f g .snd n x z Zπgf≡z = g .snd n (f .fst (suc n) x) (f .fst n z) (f .snd n x z Zπgf≡z)

-- TODO: generalize this to an arbitrary Family displayed category/fibration
ωSETᴰ : ∀ ℓ ℓ' → Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
ωSETᴰ ℓ ℓ' .ob[_] X = ⟨ X ⟩ → ωSet ℓ'
ωSETᴰ ℓ ℓ' .Hom[_][_,_] f Xᴰ Yᴰ = ∀ x → ωHom (Xᴰ x .fst) (Yᴰ (f x) .fst)
ωSETᴰ ℓ ℓ' .idᴰ = λ x → ωId _
ωSETᴰ ℓ ℓ' ._⋆ᴰ_ {f = f}{g}{xᴰ = xᴰ}{yᴰ}{zᴰ} fᴰ gᴰ x =
  _ω⋆_ {X = xᴰ x .fst}{Y = yᴰ (f x) .fst}{Z = zᴰ (g (f x)) .fst}
    (fᴰ x)
    (gᴰ (f x))
ωSETᴰ ℓ ℓ' .⋆IdLᴰ = λ _ → refl
ωSETᴰ ℓ ℓ' .⋆IdRᴰ = λ _ → refl
ωSETᴰ ℓ ℓ' .⋆Assocᴰ = λ _ _ _ → refl
ωSETᴰ ℓ ℓ' .isSetHomᴰ {yᴰ = yᴰ} = isSetΠ λ x → isSetΣ (isSetΠ λ n → isSet→ (yᴰ _ .snd n))
  λ _ → isSetΠ3 (λ _ _ _ → isSet→ (isProp→isSet (yᴰ _ .snd _ _ _)))

module ωSETᴰ {ℓ}{ℓ'} = Fibers (ωSETᴰ ℓ ℓ')

▷ : ωType ℓ → ωType ℓ
▷ X .fst zero = Unit*
▷ X .fst (suc n) = X .fst n
▷ X .snd zero x = tt*
▷ X .snd (suc i) x = X .snd i x

ω1 : ωType _
ω1 .fst _ = Unit
ω1 .snd _ _ = tt

-- Delay X ≅ X ⊎ (▷ Delay X)
data |Delay| (X : ωType ℓ) : ℕ → Type ℓ where
  -- terminated, "inl"
  done : ∀ {n} → X .fst n → |Delay| X n
  -- still running, but ran out of fuel
  Ω0 : |Delay| X 0
  -- still running, more fuel in the tank
  |Θ|  : ∀ {n} → |Delay| X n → |Delay| X (suc n)

Delay : ωType ℓ → ωType ℓ
Delay X .fst = |Delay| X
Delay X .snd n (done x) = done (X .snd n x)
Delay X .snd n (|Θ| d) = d

Δ : Type ℓ → ωType ℓ
Δ X .fst = λ z → X
Δ X .snd = λ i z → z

module _ {X : ωType ℓ} where
  retDelay : ωHom X (Delay X)
  retDelay .fst n = done
  retDelay .snd n x x' pf i = done (pf i)

  next : ωHom X (▷ X)
  next .fst = (▷ X) .snd
  next .snd zero _ _ _ i = tt*
  next .snd (suc n) x x' pf i = X .snd n (pf i)

  module _ (f : ωHom (▷ X) X) where
    |gfix| : ∀ n → X .fst n
    |gfix| zero = f .fst zero tt*
    |gfix| (suc n) = f .fst (suc n) (|gfix| n)

    |gfix|-nat : ∀ n → X .snd n (f .fst (suc n) (|gfix| n)) ≡ |gfix| n
    |gfix|-nat zero = f .snd zero (|gfix| zero) tt* refl
    |gfix|-nat (suc n) = f .snd (suc n) (|gfix| (suc n)) (|gfix| n) (|gfix|-nat n)

    gfix : ωHom ω1 X
    gfix .fst = λ { n tt → |gfix| n }
    gfix .snd n _ _ _ = |gfix|-nat n

    gfix-fixed-fst : ∀ n → |gfix| n ≡ f .fst n (next .fst n (|gfix| n))
    gfix-fixed-fst zero = refl
    gfix-fixed-fst (suc n) = cong (f .fst (suc n))
      (gfix-fixed-fst n ∙ sym (f .snd n (|gfix| n) (next .fst n (|gfix| n)) refl))

module _ (X : ωSet ℓ) (f : ωHom (▷ (X .fst)) (X .fst)) where
  gfix-fixed : gfix f ≡ _ω⋆_ {Z = X .fst} (gfix f) (_ω⋆_ {Z = X .fst} next f)
  gfix-fixed = ΣPathPProp (λ _ → isPropΠ4 λ _ _ _ _ → X .snd _ _ _)
    (funExt (λ n → funExt λ { tt → gfix-fixed-fst f n }))

δSET : Category _ _
δSET = ∫C (PropertyOver (SET ℓ-zero) (λ X → ⟨ X ⟩ → ⟨ X ⟩))

θωSetᴰ : Categoryᴰ δSET _ (ℓ-max (ℓ-max ℓ-zero ℓ-zero) ℓ-zero)
θωSetᴰ = ∫Cᴰ (EqReindex.reindex (ωSETᴰ _ ℓ-zero) Fst Eq.refl λ _ _ → Eq.refl)
  (PropertyOver _ λ ((X , δ) , Xᴰ) → ∀ x → ωHom (▷ (Xᴰ x .fst)) (Xᴰ (δ x) .fst))

-- Free θωSetᴰ
-- pushforward
module _ {V : Type ℓ}{X : Type ℓ'} (ret : V → X) (δ : X → X) (Vᴰ : V → ωType ℓᴰ) where
  -- TODO: prove |Delayᴰ| is a set, assuming V and X are sets
  data |Delayᴰ| : (x : X) → ℕ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ)) where
    terminates : ∀ {v n} → Vᴰ v .fst n → |Delayᴰ| (ret v) n
    timeout : ∀ {x}                → |Delayᴰ| (δ x) 0
    steps : ∀ {x n} → |Delayᴰ| x n → |Delayᴰ| (δ x) (suc n)

  π-Delayᴰ : ∀ {x} n → |Delayᴰ| x (suc n) → |Delayᴰ| x n
  π-Delayᴰ n (terminates x) = terminates (Vᴰ _ .snd n x)
  π-Delayᴰ zero (steps d) = timeout
  π-Delayᴰ (suc n) (steps d) = steps (π-Delayᴰ n d)

  Delayᴰ : X → ωType _
  Delayᴰ x .fst n = |Delayᴰ| x n
  Delayᴰ x .snd = π-Delayᴰ

  θᴰ : ∀ x → ωHom (▷ (Delayᴰ x)) (Delayᴰ (δ x))
  θᴰ x .fst zero (lift tt) = timeout
  θᴰ x .fst (suc n)        = steps
  θᴰ x .snd zero _ _ _ = refl
  θᴰ x .snd (suc n) d⟨sn⟩ d⟨n⟩ πd⟨sn⟩≡d⟨n⟩ i = steps (πd⟨sn⟩≡d⟨n⟩ i)

Γ : Functor EXP δSET
Γ = TotalCat.intro
  (EXP [ [1] ,-])
  (mkContrHomsSection (λ _ _ _ → isContrUnit)
  λ A → _⋆ₑ [δ])

GL : Categoryᴰ EXP _ _
GL = reindex θωSetᴰ Γ

GuardedCanonicitySection : GlobalSection GL
GuardedCanonicitySection = elim GL
  {!!} -- TODO: reindex a terminalᴰ
  ((λ x → (Delayᴰ {V = Bool} quoteBool (_⋆ₑ [δ]) (λ _ → ω1) x) , {!!}) , θᴰ quoteBool (_⋆ₑ [δ]) (λ _ → ω1))
  ((λ e → {!!}) , _)
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
  {!!}
