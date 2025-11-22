module Cubical.CoData.Delay where
  open import Cubical.Foundations.Prelude
  open import Cubical.Categories.Category
  open import Cubical.Categories.Functor
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure hiding(str)
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Limits.Terminal
  open import Cubical.Categories.Instances.FunctorAlgebras
  open import Cubical.Categories.Monad.ExtensionSystem
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Function
  open import Cubical.Data.Sigma.Properties
  open import Cubical.Data.Nat
  import Cubical.Data.Equality as Eq
  open import Cubical.Data.Sum renaming (rec to ⊎rec)
  open import Cubical.Data.Unit renaming (Unit to ⊤ )
  open Category
  open Functor
  open Algebra
  open AlgebraHom
  open ExtensionSystemFor

  private
    variable
      ℓ : Level

  module Basics where

    data StateF (Res Rec : Type ℓ) : Type ℓ where
      doneF : Res → StateF Res Rec
      stepF : Rec → StateF Res Rec

    record Delay (Res : Type ℓ) : Type ℓ

    data State (Res : Type ℓ) : Type ℓ where
      done : Res → State Res
      step : Delay Res → State Res

    record Delay Res where
      constructor delay_
      coinductive
      field view : State Res

    open Delay public

    StateF-rec : {A B C : Type ℓ} → (A → C) → (B → C) →  StateF A B → C
    StateF-rec f g (doneF x) = f x
    StateF-rec f g (stepF x) = g x

    State-rec : {A B : Type ℓ} → (A → B) → (Delay A → B) → State A → B
    State-rec f g (done x) = f x
    State-rec f g (step x) = g x

    Delay-rec : {A B : Type ℓ} → (A → B) → (Delay A → B) → Delay A → B
    Delay-rec f g d = State-rec f g (d .view)

    -- Given a Delay d, return a function on nats that,
    -- when d ≡ running ^ n (done x),
    -- maps n to inl x and every other number to inr tt.
    fromDelay : {X : Type ℓ} → Delay X → (ℕ → X ⊎ Unit)
    fromDelay d n with d .view
    fromDelay d zero    | done x = inl x
    fromDelay d (suc n) | done x = inr tt
    fromDelay d zero    | step _ = inr tt
    fromDelay d (suc n) | step d' = fromDelay d' n

    -- Given a function f on nats,
    -- return a delay that runs for n0 steps and returns x,
    -- where n0 is the smallest nat such that f n0 = inl x.
    toDelay : {X : Type ℓ} → (ℕ → X ⊎ Unit) → Delay X
    toDelay f .view with f zero
    ... | inl x  = done x
    ... | inr tt = step (toDelay λ n → f (suc n))

    retr : {X : Type ℓ} → (d : Delay X) → toDelay (fromDelay d) ≡ d
    retr d i .view with d .view
    ... | done x  = done x
    ... | step d' = step (retr d' i)

    isSetDelay : ∀ {ℓ : Level} → {X : Type ℓ} → isSet X → isSet (Delay X)
    isSetDelay {X = X} p =
      isSetRetract
        fromDelay
        toDelay
        retr
        (isSetΠ λ n → isSet⊎ p isSetUnit)

    isSetState : ∀ {ℓ : Level} → {X : Type ℓ} → isSet X → isSet (State X)
    isSetState {X = X} p =
      isSetRetract
        (State-rec inl inr)
        (⊎rec done step)
        (λ {(done x) → refl
          ; (step x) → refl})
        (isSet⊎ p (isSetDelay p))

    isSetStateF : ∀ {ℓ : Level} → {X Y : Type ℓ} →
      isSet X → isSet Y → isSet (StateF X Y)
    isSetStateF {X = X}{Y} p q =
      isSetRetract
        (StateF-rec inl inr)
        (⊎rec doneF stepF)
        (λ {(doneF x) → refl
          ; (stepF x) → refl})
        ((isSet⊎ p q))

  module Dynamics where
    open Basics

    StateF-map : {A B C : Type ℓ} → (B → C) → StateF A B → StateF A C
    StateF-map f (doneF x) = doneF x
    StateF-map f (stepF x) = stepF (f x)

    StateF-map-id : {A B : Type ℓ}{s : StateF A B} →
      StateF-map (λ x → x) s ≡ s
    StateF-map-id {s = doneF x} = refl
    StateF-map-id {s = stepF x} = refl

    StateF-map-seq :  {R A B C : Type ℓ}{f : A → B}{g : B → C}{s : StateF R A} →
        StateF-map (λ x → g (f x)) s ≡ StateF-map g (StateF-map f s)
    StateF-map-seq {s = doneF x} = refl
    StateF-map-seq {s = stepF x} = refl

    mutual
      State-map : {A B : Type ℓ} → (A → B) → State A → State B
      State-map f (done x) = done (f x)
      State-map f (step x) = step (Delay-map f x)

      Delay-map : {A B : Type ℓ} → (A → B) → Delay A → Delay B
      view (Delay-map f d) = State-map f (d .view)

    mutual
      State-map-id : {A : Type ℓ}{s : State A} →
        State-map (λ x → x) s ≡ s
      State-map-id {s = done x} = refl
      State-map-id {s = step x} = cong step Delay-map-id

      Delay-map-id : {A : Type ℓ}{d : Delay A} →
        Delay-map (λ x → x) d ≡ d
      view (Delay-map-id {A = A}{d} i) = State-map-id {A = A}{d .view} i

    mutual

      State-map-seq :  {A B C : Type ℓ}{f : A → B}{g : B → C}{s : State A} →
        State-map (λ x → g (f x)) s ≡ State-map g (State-map f s)
      State-map-seq {s = done x} = refl
      State-map-seq {s = step x} = cong step Delay-map-seq

      Delay-map-seq : {A B C : Type ℓ}{f : A → B}{g : B → C}{d : Delay A} →
        Delay-map (λ x → g (f x)) d ≡ Delay-map g (Delay-map f d)
      view (Delay-map-seq {ℓ}{A}{B}{C}{f}{g}{d} i) =
        State-map-seq {ℓ}{A}{B}{C}{f}{g}{d .view} i


    DelayF : Functor (SET ℓ) (SET ℓ)
    DelayF .F-ob X = Delay ⟨ X ⟩ , isSetDelay (X .snd)
    DelayF .F-hom = Delay-map
    DelayF .F-id = funExt λ _ → Delay-map-id
    DelayF .F-seq _ _ = funExt λ _ → Delay-map-seq

    StateFun' : Functor (SET ℓ) (SET ℓ)
    StateFun' .F-ob X = State ⟨ X ⟩ , isSetState (X .snd)
    StateFun' .F-hom = State-map
    StateFun' .F-id = funExt λ _ → State-map-id
    StateFun' .F-seq _ _ = funExt λ _ → State-map-seq

    StateFun : ob (SET ℓ) → Functor (SET ℓ) (SET ℓ)
    StateFun X .F-ob Y = (StateF ⟨ X ⟩  ⟨ Y ⟩) , isSetStateF (X .snd) (Y .snd)
    StateFun X .F-hom = StateF-map
    StateFun X .F-id = funExt λ _ → StateF-map-id
    StateFun X .F-seq _ _ = funExt λ _ → StateF-map-seq

    CoAlg : ob (SET ℓ) → Category (ℓ-suc ℓ) ℓ
    CoAlg R = AlgebrasCategory (StateFun R ^opF) ^op

    unfold : {X : Type ℓ} →  Delay X → StateF X (Delay X)
    unfold d = State-rec doneF stepF (d .view)

    fold : {X : Type ℓ} → StateF X (Delay X) → Delay X
    fold = StateF-rec (delay_ ∘S done) (delay_ ∘S step)

    d-iso : {X : Type ℓ} → Iso (Delay X) (StateF X (Delay X))
    d-iso .Iso.fun = unfold
    d-iso .Iso.inv = fold
    d-iso .Iso.rightInv (doneF x) = refl
    d-iso .Iso.rightInv (stepF x) = refl
    d-iso .Iso.leftInv d i .view with d .view
    ... | done x = done x
    ... | step x = step x

    unfold-inj : {X : Type ℓ} → (d1 d2 : Delay X) →
      unfold d1 ≡ unfold d2 → d1 ≡ d2
    unfold-inj d1 d2 eq = isoFunInjective d-iso d1 d2 eq

    unfold-inv2 : {X : Type ℓ} →(d : Delay X) →  (d' : Delay X) →
      unfold d ≡ stepF d' →  d .view ≡ step d'
    unfold-inv2 d d' H =
      cong view (isoFunInjective d-iso d (delay (step d')) H)

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
        ... | doneF r = done r
        ... | stepF y = step (fun y)

        commute : (v : ⟨ c .carrier ⟩ ) →
          (D .str ∘S fun) v ≡ (StateF-map fun ∘S c .str) v
        commute v with c .str v
        ... | doneF x = refl
        ... | stepF v' = refl

        hom : CoAlg R [ c , D ]
        hom .carrierHom = fun
        hom .strHom = funExt commute

        unique' : (s s' : Σ[ h ∈ (⟨ c .carrier  ⟩ → Delay ⟨ R ⟩ ) ]
          (D .str ∘S (h) ≡ StateF-map h ∘S (c .str))) →
          s ≡ s'
        unique' (h , com) (h' , com') =
          Σ≡Prop (λ g →
            isSetΠ (λ v → isSetStateF (R .snd) (D .carrier .snd)) _ _)
          (funExt eq-fun) where

          eq-fun : (x : ⟨ c .carrier ⟩) → PathP (λ v → Delay ⟨ R ⟩) (h x) (h' x)
          view (eq-fun v i) with c .str v in eq
          ... | doneF x  =
            view (unfold-inj (h v) (h' v) (com-v ∙ sym com'-v) i) where
            com-v : unfold (h v) ≡ doneF x
            com-v = funExtS⁻ com v ∙ (λ j → StateF-map h (Eq.eqToPath eq j))

            com'-v : unfold (h' v) ≡ doneF x
            com'-v = funExtS⁻ com' v ∙ (λ j → StateF-map h' (Eq.eqToPath eq j))

          ... | stepF v'  =
            (goal
              (h v .view)
              (h' v .view)
              (Eq.pathToEq eq-hv)
              (Eq.pathToEq eq-h'v)) i where
            com-v : unfold (h v) ≡ stepF (h v')
            com-v = funExtS⁻ com v ∙ (λ j → StateF-map h (Eq.eqToPath eq j))

            com'-v : unfold (h' v) ≡ stepF (h' v')
            com'-v = funExtS⁻ com' v ∙ (λ j → StateF-map h' (Eq.eqToPath eq j))

            eq-hv : h v .view ≡ step (h v')
            eq-hv = unfold-inv2 (h v) (h v') com-v

            eq-h'v : h' v .view ≡ step (h' v')
            eq-h'v = unfold-inv2 (h' v) (h' v') com'-v

            goal : ∀ s1 s2 →
              s1 Eq.≡ step (h v') →
              s2 Eq.≡ step (h' v') →
              s1 ≡ s2
            goal _ _ Eq.refl Eq.refl = cong step (eq-fun v')

        uniq : (f : CoAlg R [ c , D ]) → hom ≡ f
        uniq f = AlgebraHom≡ (StateFun R ^opF) (cong fst have) where
          have : (fun , funExt commute) ≡ (f .carrierHom , f .strHom)
          have = unique' (fun , funExt commute) ( f .carrierHom , f .strHom)

        goal : isContr ((CoAlg R) [ c , D ])
        goal = hom , uniq

  module Monad {ℓ : Level} where
    open Basics

    D : ob (SET ℓ) → ob (SET ℓ)
    D X = (Delay ⟨ X ⟩) , (isSetDelay (X .snd))

    ret-s : {A : Type ℓ} → A → State A
    ret-s a = done a

    ret-d : {A : Type ℓ} → A → Delay A
    ret-d a = delay (ret-s a)

    mutual
      bind-s : {A B : Type ℓ} → State A → (A → State B) → State B
      bind-s (done x) f = f x
      bind-s (step x) f = step (bind-d x λ a → delay (f a))

      bind-d : {A B : Type ℓ} → Delay A → (A → Delay B) → Delay B
      view (bind-d d f) = bind-s (d .view) λ a → f a .view

    eq-d : {A : Type ℓ}{d d' : Delay A} → d .view ≡ d' .view → d ≡ d'
    eq-d p i .view = p i

    bind-ret-l : {A B : Type ℓ} → (f : A → Delay B)(a : A) →
      bind-d (ret-d a) f ≡ f a
    bind-ret-l f a = eq-d refl

    mutual
      bind-s-ret : {A : Type ℓ}{s : State A} → bind-s s ret-s ≡ s
      bind-s-ret {s = done x} = refl
      bind-s-ret {s = step x} = cong step (bind-ret-r {d = x})

      bind-ret-r : {A : Type ℓ}{d : Delay A} → bind-d d ret-d ≡ d
      view (bind-ret-r {A}{d} i) = bind-s-ret {A}{d .view} i


    DFun→SFun : {X Y : Type ℓ} → (X → Delay Y) → (X → State Y)
    DFun→SFun f x = view (f x)

    -- SFun→DFun
    SFun→DFun : {X Y : Type ℓ} → (X → State Y) → (X → Delay Y)
    SFun→DFun f x = delay (f x)

    mutual
      comp-s : {X Y Z : Type ℓ} → (f : Y → State Z) → (g : X → State Y) →
          (s : State X) →
        bind-s (bind-s s g) f ≡
        bind-s s (λ x' → bind-s (g x') f)
      comp-s f g (done x₁) = refl
      comp-s {X}{Y}{Z} f g (step d) i =
        step (
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
