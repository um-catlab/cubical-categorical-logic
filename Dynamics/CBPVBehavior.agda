{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --type-in-type #-}
-- working on level polymorphism
-- i need to generalize `enrich : cat -> enriched cat` to be more level polymorphic
module Dynamics.CBPVBehavior where

  open import Cubical.Foundations.Prelude
  open import Cubical.Categories.Functor
  open import Cubical.Categories.Category
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Categories.Monad.Base
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Data.Sum renaming (rec to rec⊎)
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Sigma
  open import Cubical.Data.Nat
  open import Cubical.Categories.Monoidal.Base
  open import Cubical.Categories.Monoidal.Enriched
  open import Cubical.Categories.Monoidal.Enriched.More
  open import Cubical.Categories.Monoidal.Enriched.Presheaf
  open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
  open import Cubical.Data.Empty renaming (elim to ⊥elim)
  open import Cubical.Data.Maybe renaming (rec to mrec)
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure
  open import Cubical.Categories.Monad.ExtensionSystem
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Relation.Binary.Preorder
  open import Gluing.CBPV.Model
  open import Dynamics.CBPVSmallStep
  open import Dynamics.TransitionSystem
  open import Gluing.CBPV.Kleisli
  --open import src.delay

  module _ {ℓ : Level} where
    private
      set = SET ℓ

    open Functor
    open TSys {ℓ}
    open CBPVModel
    open Category
    open EnrichedFunctor
    open EnrichedCategory
    open NatTrans
    open TSystem
    open CBPVModelHom
    open EnrichedNatTrans
    open Concrete {ℓ} hiding (T)
    open Model {ℓ} TExt
    open mod {ℓ}
    open MonFun renaming (f to fun ; isMon to mono)
    open TSystem[_,_]
    open ExtensionSystemFor TE


    private
      open model set {ℓ}
      K = Kleisli set TExt
      E = enrich K

      𝓟[_,_] : ob 𝓟 → ob 𝓟 → Type (ℓ-suc ℓ)
      𝓟[_,_] = 𝓟 .Hom[_,_]

      E[_,_] : ob E → ob E → ob 𝓟
      E[_,_] = E .Hom[_,_]

      self[_,_] : ob self → ob self → ob 𝓟
      self[_,_] = self .Hom[_,_]

    exec : (S : TSystem) → ℕ → ⟨ state S ⟩ → ⟨ state S ⟩
    exec S zero s = s
    exec S (suc n) s = mrec s (exec S n) (S .trans s)

    exec-term : {S : TSystem} → (n : ℕ) → (t : term S) → exec S n (t .fst) ≡ t .fst
    exec-term {S} zero t = refl
    exec-term {S} (suc n) t with (canStep? S (t .fst))
    ... | inr x = ⊥elim {A = λ _ →  mrec (t .fst) (exec S n) (S .Test.TSystem.trans (t .fst)) ≡ t .fst}(¬nothing≡just (sym (t .snd) ∙ x .snd))
    ... | inl x with (trans S (t .fst))
    ... | nothing = refl
    ... | just x₁ = ⊥elim {A = λ _ →  mrec (t .fst) (exec S n) (just x₁) ≡ t .fst} (¬nothing≡just (sym x))

    exec-step : {S : TSystem} → (n : ℕ) → ((t , (t' , prf)) : steps S) → exec S (suc n) t ≡ exec S n t'
    exec-step {S} zero t = cong (λ h → mrec (t .fst) (λ s → s) h) (t .snd .snd)
    exec-step {S} (suc n) t with (canStep? S (t .fst))
    ... | inr x = cong (λ h → mrec (t .fst) (λ s → mrec s (exec S n) (S .Test.TSystem.trans s)) h) (t .snd .snd)
    ... | inl x = ⊥elim {A = λ _ → thing} (¬nothing≡just (sym x ∙ t .snd .snd)) where
      thing = mrec (t .fst) (λ s → mrec s (exec S n) (S .Test.TSystem.trans s)) (S .Test.TSystem.trans (t .fst))
            ≡ mrec (t .snd .fst) (exec S n) (S .Test.TSystem.trans (t .snd .fst))

    run : (S : TSystem) → ℕ → ⟨ state S ⟩ → Maybe (term S)
    run S n s = finish S (exec S n s)

    open import  Cubical.Data.Nat.Order hiding (eq)
    _≤n_ : Lift ℕ → Lift ℕ → Type _
    _≤n_ x y = Lift (x .lower ≤ y .lower)
    -- ≤m-trans

    -- The three cases of run
    -- runing a terminal
    -- taking a step with fuel
    -- taking a step with no fuel
    run-term : {B : TSystem}{n : ℕ}{t : term B} → run B n (t .fst) ≡ just t
    run-term {B}{n}{t} = cong₂ finish refl (exec-term n t) ∙ finish-term B t

    run-step : {S : TSystem}{n : ℕ}{(t , (t' , _)) : steps S} → run S (suc n) t ≡ run S n t'
    run-step {S}{n}{t}= cong₂ finish refl (exec-step {S} n t)

    run-timeout : {S : TSystem}{(t , (t' , _)) : steps S} → run S 0 t ≡ nothing
    run-timeout {S}{t}= finish-step S t

    run-mon-s : (S : TSystem)(s : ⟨ state S ⟩)(n : ℕ) → _≤m_ {hterm S} (run S n s)(run S (suc n) s)
    run-mon-s S s zero with canStep? S s
    ... | inl x = goal where
      -- both s can't step so it is terminal and run just returns
      prf : (run S 1 s) ≡ just (s , x)
      prf = run-term {S}{1}{s , x}

      goal : _≤m_ {hterm S} (just (s , x))(run S 1 s)
      goal = ≡-to-≤m refl prf refl

    ... | inr x = tt*
    run-mon-s S s (suc n) with canStep? S s
    ... | inl x = goal where
      prf : (run S (suc n) s) ≡ just (s , x)
      prf = run-term {S}{suc n}{s , x}

      prf' : (run S (suc (suc n)) s) ≡ just (s , x)
      prf' = run-term {S}{suc (suc n)}{s , x}

      goal : _≤m_ {hterm S} (run S (suc n) s)(run S (suc (suc n)) s)
      goal = ≡-to-≤m prf prf' refl

    ... | inr x = goal where
      have : run S (suc n) s ≡ run S n (x .fst)
      have = run-step {S}{n}{s , x}

      have' : run S (suc (suc n)) s ≡ run S (suc n) (x .fst)
      have' = run-step {S}{suc n}{s , x}

      ih : run S n (x .fst) ≤m run S (suc n) (x .fst)
      ih = run-mon-s S (x .fst) n

      goal :  _≤m_ {hterm S} (run S (suc n) s)(run S (suc (suc n)) s)
      goal = subst2 (λ h1 h2 → _≤m_ {hterm S} h1 h2) (sym have) (sym have') ih

    run-mono-plus : (S : TSystem)(s : ⟨ state S ⟩)(n p : ℕ) →
      _≤m_ {hterm S} (run S n s)(run S (p + n) s)
    run-mono-plus S s n zero = eq refl
    run-mono-plus S s n (suc p) = ≤m-trans (run-mono-plus S s n p) ((run-mon-s S s (p + n)))

    run-mono : (S : TSystem)(s : ⟨ state S ⟩)(n m : Lift ℕ) →
      n ≤n m → _≤m_ {hterm S} (run S (n . lower) s)(run S (m .lower) s)
    run-mono S s n m (lift (p , p+n=m)) = ≤m-trans (run-mono-plus S s (n .lower) p) coerce where
      coerce : run S (p + n .lower) s ≤m run S (m .lower) s
      coerce = subst (λ h → _≤m_ {hterm S} (run S h s) (run S (m .lower) s)) (sym p+n=m) (eq refl)

    run-mon : (S : TSystem)(s : ⟨ state S ⟩) → MonFun preℕ (maybePreorder (hterm S) .fst)
    run-mon S s .fun (lift n) = run S n s
    run-mon S s .mono = run-mono S s _ _

    runE : {B B' : TSystem} → TSysCat [ B , B' ] → K [ hterm B , hterm B' ]
    runE {B}{B'} f s .fun (lift n) = run B' n (f .tmap (s .fst))
    runE {B}{B'} f s .mono = run-mono B' (f .tmap (s .fst)) _ _

    runE-seq-zero : {S T : TSystem}{s : ⟨ state S ⟩ }{f : TSystem[ S , T ]}→
      run T 0 (f .tmap s) ≡ ((run S 0 s) >>=m (λ t → run T 0 (tmap f (t .fst))))
    runE-seq-zero {S} {T}{s} {f} with canStep? S s
    ... | inl x = refl
    ... | inr x = goal where

      have : trans T (tmap f s) ≡ just (tmap f (fst x))
      have = commutes f (s , x)

      goal : run T 0 (tmap f s) ≡ nothing
      goal = run-timeout {T} {(tmap f s) , ((tmap f (fst x))) , have}


    {-
      run T n (f s) ≡ (run S n s) >>=m (λ t → run T n (f t))

      The issue here is that
        run T n (f s)
        and
        run S n s
      are in sync until system S stops stepping
        this is due to the laxness condition of f
      if S timesout with n steps, then both sides return nothing
      if S finished with k steps left
        then we are demanding equality of
        run T k t
        and
        run T n t
      we only have that run T k t ≤m run T n t, not equality
    -}
    runE-seq' : {S T  : TSystem}{n : ℕ}{s : ⟨ state S ⟩}{f : TSystem[ S , T ]} →
      run T n (f .tmap s) ≡ (run S n s) >>=m (λ t → run T n (tmap f (t .fst)))
    runE-seq' {S} {T} {zero} {s} {f} = runE-seq-zero {S}{T}{s}{f}
    runE-seq' {S} {T} {suc n} {s} {f} with canStep? S s
    ... | inl x = cong₃ mrec refl refl (sym (run-term {S}{suc n}{s , x}))
    ... | inr x = goal where
        -- we have that s steps
      t-step : run S (suc n) s ≡ run S n (x .fst)
      t-step = run-step {S}{n}{s , x}

      -- we have that f s steps
      ft-step : run T (suc n) (tmap f s) ≡ run T n (tmap f (x .fst))
      ft-step = run-step {T}{n}{(tmap f s) , (tmap f (x .fst)) , commutes f (s , x)}

      ih : run T n (tmap f (x .fst)) ≡ (run S n (x .fst)) >>=m ((λ t → run T n (tmap f (t .fst))))
      ih = runE-seq' {S}{T}{n}{x .fst}{f}

      -- equality does not hold..
      -- lhs ≤m rhs does ...
      -- run is monotonic though
      {-
        If I was using a delay monad I'd hit the same issue
        so what we really want is weak bisim
        The answer might be to use the partiality monad encoded as a QIT from
        Partiality, Revisited
      -}
      sus : (t : term S) → run T n (tmap f (t .fst)) ≡ run T (suc n) (tmap f (t .fst))
      sus t with canStep? T (tmap f (t .fst))
      ... | inl x = run-term {T}{n}{(tmap f (t .fst)) , x} ∙ sym (run-term {T}{suc n}{(tmap f (t .fst)) , x})
      ... | inr x = {!   !}

      goal : run T (suc n) (f .tmap s) ≡ (run S (suc n) s)  >>=m (λ t → run T (suc n) (tmap f (t .fst)))
      goal = ft-step ∙ ih ∙ cong₃ mrec refl (funExt sus) (sym t-step)

    runE-seq : {S T R : TSystem}{n : ℕ}{s : term S}{f : TSystem[ S , T ]}{g : TSystem[ T , R ]} →
      run R n (g .tmap (f .tmap (s .fst))) ≡ (run T n (tmap f (s .fst))) >>=m (λ t → run R n (tmap g (t .fst)))
    runE-seq {S} {T} {R} {n} {s} {f} {g} = runE-seq'{T}{R}{n}{tmap f (s .fst)}{g}

    runF : Functor TSysCat K
    runF .F-ob = hterm
    runF .F-hom = runE
    runF .F-id = funExt λ t → eqMon _ _ (funExt λ n → run-term)
    runF .F-seq {S}{T}{R} f g =
      funExt λ t → eqMon _ _ (funExt λ n → runE-seq{S}{T}{R}{n .lower}{t}{f}{g})

    𝓜 = (model.𝓟Mon set)

    dumb : EnrichedFunctor 𝓜 E (BaseChange Id E)
    dumb .F₀ X = X
    dumb .F₁ = natTrans (λ x x₁ → x₁) λ _  → refl
    dumb .Fid = refl
    dumb .Fseq = makeNatTransPath refl

    {-}
    -- Current Level issues
    -- I need to generalize `enrich : Cat → Enriched Cat` to be more level polymorphic

    _ : CBPVModel {ℓ-suc ℓ}{ℓ}{ℓ}{ℓ-suc ℓ}
    _ = sem

    _ : CBPVModel {ℓ-suc ℓ}{ℓ}{ℓ}{ℓ-suc ℓ}
    _ = kleisli

    -- need CBPVModel {ℓ-suc ℓ} {ℓ} {ℓ} {ℓ-suc (ℓ-suc ℓ)}

    bigstep : CBPVModelHom {ℓ-suc ℓ}{ℓ} {!   !} {!   !}
    bigstep = {!   !} -}

    bigstep : CBPVModelHom sem kleisli
    bigstep = record {
      ctx = Id ;
      ty = λ A → A ;
      tm = λ A → natTrans (λ Γ f Γ∙ → f Γ∙) λ _ → refl ;
      stk = ecomp _ (enrichF TSysCat K runF) dumb ;
      cmp = final } where

        target : EnrichedFunctor 𝓜 (𝓔 sem) self
        target =
          ecomp 𝓜 (
            ecomp 𝓜
              (enrichF TSysCat K runF)
              dumb)
            (ecomp 𝓜
              (BaseChangeF Id  (TmB kleisli))
              (BaseChangeSelf Id))

        final' : (S : TSystem) → 𝓟[ 𝟙 , self[ semcmp S , target .F₀ S ] ]
        final' S .N-ob Γ tt* =
          pshhom
            (λ Δ (γ , m) → lift λ Δ∙ → run-mon S (m .lower Δ∙))
            λ _ _ _ _  → cong lift refl
        final' S .N-hom γ =
          funExt λ tt* →
            makePshHomPath (
              funExt λ Δ → funExt λ γ,m → cong lift (funExt λ Δ∙ → refl))

        final : EnrichedNatTrans (TmB sem) target
        final .E-N-ob = final'
        final .E-N-hom S T =
          makeNatTransPath (funExt λ Γ → funExt λ Γ◂B⊢kB' →
          makePshHomPath (funExt λ Δ → funExt λ { (γ , Δ⊢cB) →
            cong lift (funExt λ Δ∙ → eqMon _ _ (funExt λ n →
            runE-seq'{S}{T}{n .lower}{Δ⊢cB .lower Δ∙}{lower Γ◂B⊢kB' (γ Δ∙) }))}))
            {-
            run-mon T
              (lower Γ◂B⊢kB' (γ Δ∙) .tmap (Δ⊢cB .lower Δ∙))
            ≡
            (run-mon S (Δ⊢cB .lower Δ∙) >>= runE (Γ◂B⊢kB' .lower (γ Δ∙)))
            -}
