module Cubical.CoData.Delay where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding(str)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sum renaming (rec to ⊎rec; map to ⊎map)
open import Cubical.Data.Sum.More
open import Cubical.Data.Unit renaming (Unit to ⊤ )

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Monad.ExtensionSystem

open Algebra
open AlgebraHom
open Category
open ExtensionSystemFor
open Functor

private
  variable
    ℓ : Level

mutual
  State : Type ℓ → Type ℓ
  State A = A ⊎ (Delay A)

  record Delay (A : Type ℓ) : Type ℓ where
    constructor delay_
    coinductive
    field view : State A

open Delay public

Delay-rec : {A B : Type ℓ} → (A → B) → (Delay A → B) → Delay A → B
Delay-rec f g d = ⊎rec f g (d .view)

-- Given a Delay d, return a function on nats that,
-- when d ≡ running ^ n (inl x),
-- maps n to inl x and every other number to inr tt.
fromDelay : {X : Type ℓ} → Delay X → (ℕ → X ⊎ Unit)
fromDelay d n with d .view
fromDelay d zero    | inl x = inl x
fromDelay d (suc n) | inl x = inr tt
fromDelay d zero    | inr _ = inr tt
fromDelay d (suc n) | inr d' = fromDelay d' n

-- Given a function f on nats,
-- return a delay that runs for n0 inrs and returns x,
-- where n0 is the smallest nat such that f n0 = inl x.
toDelay : {X : Type ℓ} → (ℕ → X ⊎ Unit) → Delay X
toDelay f .view with f zero
... | inl x  = inl x
... | inr tt = inr (toDelay λ n → f (suc n))

retr : {X : Type ℓ} → (d : Delay X) → toDelay (fromDelay d) ≡ d
retr d i .view with d .view
... | inl x  = inl x
... | inr d' = inr (retr d' i)

isSetDelay : ∀ {ℓ : Level} → {X : Type ℓ} → isSet X → isSet (Delay X)
isSetDelay {X = X} p =
  isSetRetract
    fromDelay
    toDelay
    retr
    (isSetΠ λ n → isSet⊎ p isSetUnit)

isSetState : ∀ {ℓ : Level} → {X : Type ℓ} → isSet X → isSet (State X)
isSetState {X = X} p = isSet⊎ p (isSetDelay p)

mutual
  -- this is just ⊎map f (Delay-map f)
  -- but we can't use this definition
  -- without the termination checker throwing a fit
  State-map : {A B : Type ℓ} → (A → B) → State A → State B
  State-map f (inl x) = inl (f x)
  State-map f (inr x) = inr (Delay-map f x)

  Delay-map : {A B : Type ℓ} → (A → B) → Delay A → Delay B
  view (Delay-map f d) = State-map f (d .view)

mutual
  State-map-id : {A : Type ℓ}{s : State A} →
    State-map (λ x → x) s ≡ s
  State-map-id {s = inl x} = refl
  State-map-id {s = inr x} = cong inr Delay-map-id

  Delay-map-id : {A : Type ℓ}{d : Delay A} →
    Delay-map (λ x → x) d ≡ d
  view (Delay-map-id {A = A}{d} i) = State-map-id {A = A}{d .view} i

mutual
  State-map-seq :  {A B C : Type ℓ}{f : A → B}{g : B → C}{s : State A} →
    State-map (λ x → g (f x)) s ≡ State-map g (State-map f s)
  State-map-seq {s = inl x} = refl
  State-map-seq {s = inr x} = cong inr Delay-map-seq

  Delay-map-seq : {A B C : Type ℓ}{f : A → B}{g : B → C}{d : Delay A} →
    Delay-map (λ x → g (f x)) d ≡ Delay-map g (Delay-map f d)
  view (Delay-map-seq {ℓ}{A}{B}{C}{f}{g}{d} i) =
    State-map-seq {ℓ}{A}{B}{C}{f}{g}{d .view} i

DelayF : Functor (SET ℓ) (SET ℓ)
DelayF .F-ob X = Delay ⟨ X ⟩ , isSetDelay (X .snd)
DelayF .F-hom = Delay-map
DelayF .F-id = funExt λ _ → Delay-map-id
DelayF .F-seq _ _ = funExt λ _ → Delay-map-seq

StateFun : ob (SET ℓ) → Functor (SET ℓ) (SET ℓ)
StateFun X .F-ob Y = (⟨ X ⟩ ⊎ ⟨ Y ⟩) , isSet⊎ (X .snd) (Y .snd)
StateFun X .F-hom = map-r
StateFun X .F-id = map-id
StateFun X .F-seq _ _ = map-seq

CoAlg : ob (SET ℓ) → Category (ℓ-suc ℓ) ℓ
CoAlg R = AlgebrasCategory (StateFun R ^opF) ^op

unfold : {X : Type ℓ} → Delay X → X ⊎ (Delay X)
unfold d = ⊎rec inl inr (d .view)

fold : {X : Type ℓ} → X ⊎ (Delay X) → Delay X
fold = ⊎rec (delay_ ∘S inl) (delay_ ∘S inr)

d-iso : {X : Type ℓ} → Iso (Delay X) (X ⊎ (Delay X))
d-iso .Iso.fun = unfold
d-iso .Iso.inv = fold
d-iso .Iso.rightInv (inl x) = refl
d-iso .Iso.rightInv (inr x) = refl
d-iso .Iso.leftInv d i .view with d .view
... | inl x = inl x
... | inr x = inr x

unfold-inj : {X : Type ℓ} → (d1 d2 : Delay X) →
  unfold d1 ≡ unfold d2 → d1 ≡ d2
unfold-inj d1 d2 eq = isoFunInjective d-iso d1 d2 eq

unfold-inv2 : {X : Type ℓ} →(d : Delay X) →  (d' : Delay X) →
  unfold d ≡ inr d' →  d .view ≡ inr d'
unfold-inv2 d d' H =
  cong view (isoFunInjective d-iso d (delay (inr d')) H)

DelayCoAlg : (R : ob (SET ℓ)) → ob (CoAlg R)
DelayCoAlg R .carrier = Delay ⟨ R ⟩ , isSetDelay (R .snd)
DelayCoAlg R .str = unfold

-- Proof thanks to Eric Giovannini
-- https://github.com/ericgiovannini/gradual-typing-semantics-in-sgdt
-- /blob/74e6c189239c0f0726ad5bbf20b40e87935117a4/formalizations/
-- guarded-cubical/Semantics/Adequacy/Coinductive/DelayCoalgebra.agda
FinalCoAlg : (R : ob (SET ℓ)) → Terminal (CoAlg R)
FinalCoAlg R = DelayCoAlg R , λ c → goal c where

  module _ (c : ob (CoAlg R)) where

    D = DelayCoAlg R

    fun : ⟨ c .carrier ⟩ → Delay ⟨ R ⟩
    view (fun x) with (c .str x)
    ... | inl r = inl r
    ... | inr y = inr (fun y)

    commute : (v : ⟨ c .carrier ⟩ ) →
      (D .str ∘S fun) v ≡ (map-r fun ∘S c .str) v
    commute v with c .str v
    ... | inl x = refl
    ... | inr v' = refl

    hom : CoAlg R [ c , D ]
    hom .carrierHom = fun
    hom .strHom = funExt commute

    unique' : (s s' : Σ[ h ∈ (⟨ c .carrier  ⟩ → Delay ⟨ R ⟩ ) ]
      (D .str ∘S (h) ≡ map-r h ∘S (c .str))) →
      s ≡ s'
    unique' (h , com) (h' , com') =
      Σ≡Prop (λ g →
        isSetΠ (λ v → isSet⊎ (R .snd) (D .carrier .snd)) _ _)
      (funExt eq-fun) where

      eq-fun : (x : ⟨ c .carrier ⟩) → PathP (λ v → Delay ⟨ R ⟩) (h x) (h' x)
      view (eq-fun v i) with c .str v in eq
      ... | inl x  =
        view (unfold-inj (h v) (h' v) (com-v ∙ sym com'-v) i) where
        com-v : unfold (h v) ≡ inl x
        com-v = funExtS⁻ com v ∙ (λ j → map-r h (Eq.eqToPath eq j))

        com'-v : unfold (h' v) ≡ inl x
        com'-v = funExtS⁻ com' v ∙ (λ j → map-r h' (Eq.eqToPath eq j))

      ... | inr v'  =
        (goal
          (h v .view)
          (h' v .view)
          (Eq.pathToEq eq-hv)
          (Eq.pathToEq eq-h'v)) i where
        com-v : unfold (h v) ≡ inr (h v')
        com-v = funExtS⁻ com v ∙ (λ j → map-r h (Eq.eqToPath eq j))

        com'-v : unfold (h' v) ≡ inr (h' v')
        com'-v = funExtS⁻ com' v ∙ (λ j → map-r h' (Eq.eqToPath eq j))

        eq-hv : h v .view ≡ inr (h v')
        eq-hv = unfold-inv2 (h v) (h v') com-v

        eq-h'v : h' v .view ≡ inr (h' v')
        eq-h'v = unfold-inv2 (h' v) (h' v') com'-v

        goal : ∀ s1 s2 →
          s1 Eq.≡ inr (h v') →
          s2 Eq.≡ inr (h' v') →
          s1 ≡ s2
        goal _ _ Eq.refl Eq.refl = cong inr (eq-fun v')

    uniq : (f : CoAlg R [ c , D ]) → hom ≡ f
    uniq f = AlgebraHom≡ (StateFun R ^opF) (cong fst have) where
      have : (fun , funExt commute) ≡ (f .carrierHom , f .strHom)
      have = unique' (fun , funExt commute) ( f .carrierHom , f .strHom)

    goal : isContr ((CoAlg R) [ c , D ])
    goal = hom , uniq

D : ob (SET ℓ) → ob (SET ℓ)
D X = (Delay ⟨ X ⟩) , (isSetDelay (X .snd))

ret-s : {A : Type ℓ} → A → State A
ret-s a = inl a

ret-d : {A : Type ℓ} → A → Delay A
ret-d a = delay (ret-s a)

mutual
  bind-s : {A B : Type ℓ} → State A → (A → State B) → State B
  bind-s (inl x) f = f x
  bind-s (inr x) f = inr (bind-d x λ a → delay (f a))

  bind-d : {A B : Type ℓ} → Delay A → (A → Delay B) → Delay B
  view (bind-d d f) = bind-s (d .view) λ a → f a .view

eq-d : {A : Type ℓ}{d d' : Delay A} → d .view ≡ d' .view → d ≡ d'
eq-d p i .view = p i

bind-ret-l : {A B : Type ℓ} → (f : A → Delay B)(a : A) →
  bind-d (ret-d a) f ≡ f a
bind-ret-l f a = eq-d refl

mutual
  bind-s-ret : {A : Type ℓ}{s : State A} → bind-s s ret-s ≡ s
  bind-s-ret {s = inl x} = refl
  bind-s-ret {s = inr x} = cong inr (bind-ret-r {d = x})

  bind-ret-r : {A : Type ℓ}{d : Delay A} → bind-d d ret-d ≡ d
  view (bind-ret-r {A = A}{d} i) = bind-s-ret {A = A}{d .view} i

DFun→SFun : {X Y : Type ℓ} → (X → Delay Y) → (X → State Y)
DFun→SFun f x = view (f x)

SFun→DFun : {X Y : Type ℓ} → (X → State Y) → (X → Delay Y)
SFun→DFun f x = delay (f x)

mutual
  comp-s : {X Y Z : Type ℓ} → (f : Y → State Z) → (g : X → State Y) →
      (s : State X) →
    bind-s (bind-s s g) f ≡
    bind-s s (λ x' → bind-s (g x') f)
  comp-s f g (inl x₁) = refl
  comp-s {X = X}{Y}{Z} f g (inr d) i =
    inr (
      goal
        (λ x' → delay bind-s (g x') f)
        (Eq.pathToEq (funExt lem)) i) where

    lem : ∀ x' ->
      delay (bind-s (g x')f ) ≡
      bind-d  (SFun→DFun g x')(SFun→DFun f)
    lem x' i .view = bind-s (g x') f

    goal : ∀ (f' : X -> Delay Z) ->
      f' Eq.≡ (λ x' -> bind-d (SFun→DFun g x')(SFun→DFun f) ) ->
      bind-d (bind-d d (λ  x' -> delay (g  x')))  (λ  x' -> delay (f  x'))
        ≡
      bind-d d f'
    goal _ Eq.refl = comp-d (SFun→DFun f) (SFun→DFun g) d

  comp-d : {X Y Z : Type ℓ} → (f : Y → Delay Z) → (g : X → Delay Y) →
    (d : Delay X) →
    bind-d (bind-d d g) f ≡
    bind-d d (λ x' → bind-d (g  x')f)
  comp-d f g d i .view = comp-s (DFun→SFun f)(DFun→SFun g) (view d) i

DExt' : ExtensionSystemFor (SET ℓ) D
DExt' .η = ret-d
DExt' .bind f m = bind-d m f
DExt' .bind-r = funExt λ d → bind-ret-r
DExt' .bind-l = funExt λ d → bind-ret-l _ _
DExt' .bind-comp {X}{Y}{f}{Z}{g}= funExt λ d → comp-d _ _ _

DExt : ExtensionSystem (SET ℓ)
DExt = D , DExt'
