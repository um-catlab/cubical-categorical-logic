
module Cubical.Categories.CBPV.Instances.TransitionSystem where

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Category
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Data.Maybe renaming (rec to mrec)
open import Cubical.Data.Maybe.More
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Preorder
open import Cubical.Reflection.RecordEquiv.More
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Foundations.Equiv.Base
open Category
open Functor
open OrderedFunctor

module TSys {ℓ : Level} where

  MaybeF : Functor (SET ℓ) (SET ℓ)
  MaybeF .F-ob X = (Maybe ⟨ X ⟩) , isSetMaybe {A = X}
  MaybeF .F-hom = map-Maybe
  MaybeF .F-id = funExt map-Maybe-id
  MaybeF .F-seq f g = funExt map-Maybe-seq

  _≤m_ : {A : hSet ℓ } → Maybe ⟨ A ⟩ → Maybe ⟨ A ⟩ → Set ℓ
  nothing ≤m n = Unit*
  just x ≤m nothing = ⊥*
  _≤m_ {A} (just x) (just y) = (x ≡ y)

  ≡-to-≤m  : {A : hSet ℓ}{x y : ⟨ A ⟩}{m n : Maybe ⟨ A ⟩ } →
    m ≡ just x → n ≡ just y → x ≡ y → _≤m_ {A} m n
  ≡-to-≤m {A} p q r = subst2 (λ h1 h2 → _≤m_ {A} h1 h2) (sym p) (sym q) r

  eq : {A : hSet ℓ }{m n : Maybe ⟨ A ⟩} → m ≡ n → _≤m_ {A} m n
  eq {A} {nothing} {n} _ = tt*
  eq {A} {just x} {nothing} p =
    ⊥elim {A = λ _ → _≤m_{A} (just x) nothing}(¬nothing≡just (sym p))
  eq {A} {just x} {just x₁} p = just-inj _ _ p

  inversion : {A : hSet ℓ}{a : ⟨ A ⟩ }{n : Maybe ⟨ A ⟩ } →
    _≤m_ {A} (just a) n → Σ ⟨ A ⟩ λ a' → (n ≡ just a') × (a ≡ a' )
  inversion {A} {a} {just x} p = x , refl , p

  ≤m-isProp : {A : hSet ℓ}{m n : Maybe ⟨ A ⟩ } → isProp (_≤m_ {A} m n )
  ≤m-isProp {A} {nothing} {nothing} = isPropUnit*
  ≤m-isProp {A} {nothing} {just x} = isPropUnit*
  ≤m-isProp {A} {just x} {nothing} ()
  ≤m-isProp {A} {just x} {just y} p q = A .snd x y p q

  ≤m-refl : {A : hSet ℓ}{m : Maybe ⟨ A ⟩ } → _≤m_ {A} m m
  ≤m-refl {A} {nothing} = tt*
  ≤m-refl {A} {just x} = refl

  ≤m-trans : {A : hSet ℓ}{m n p : Maybe ⟨ A ⟩ } →
    _≤m_{A} m n → _≤m_ {A} n p → _≤m_ {A} m p
  ≤m-trans {A} {nothing} {n} {p} _ _ = tt*
  ≤m-trans {A} {just x} {nothing} {p} ()
  ≤m-trans {A} {just x} {just y} {nothing} _ ()
  ≤m-trans {A} {just x} {just y} {just z} p q = p ∙ q

  monoF : {A B : hSet ℓ}{x y : Maybe ⟨ A ⟩ }{f : ⟨ A ⟩  → ⟨ B ⟩ } →
      _≤m_ {A} x y → _≤m_ {B} (map-Maybe f x) (map-Maybe f y)
  monoF {A} {B} {nothing} {y} p = tt*
  monoF {A} {B} {just x} {just y}{f} p = cong f p

  monoF' : {A B : hSet ℓ}{x y : Maybe ⟨ A ⟩ }{f g : ⟨ A ⟩  → ⟨ B ⟩ } →
    f ≡ g →  _≤m_ {B} (map-Maybe f x) (map-Maybe g x)
  monoF' {A} {B} {nothing} {y} {f} {g} p = tt*
  monoF' {A} {B} {just x} {y} {f} {g} p = funExt⁻ p _

  monoBind : {A B C : hSet ℓ}{x : Maybe ⟨ A ⟩ }
    {f : ⟨ A ⟩  → ⟨ B ⟩ }{g : ⟨ B ⟩ → ⟨ C ⟩ }→
    _≤m_ {C} (map-Maybe (g ∘S f) x) (map-Maybe g (map-Maybe f x))
  monoBind {x = nothing} = tt*
  monoBind {x = just x} = refl

  maybePreorder : ob (SET ℓ) → ob (PREORDER ℓ ℓ)
  maybePreorder X = (Maybe ⟨ X ⟩  ,
    preorderstr (_≤m_{X})
      (ispreorder
        (λ a b → ≤m-isProp)
        (λ a → ≤m-refl)
        λ a b c → ≤m-trans)) ,
      isSetMaybe {A = X}

  ord : Functor (SET ℓ) (PREORDER ℓ ℓ)
  ord .F-ob = maybePreorder
  ord .F-hom {A}{B}f = record { f = map-Maybe f ; isMon = monoF }
  ord .F-id = eqMon _ _ (funExt map-Maybe-id)
  ord .F-seq _ _ = eqMon _ _ (funExt map-Maybe-seq)

  MaybeOrdered : OrderedFunctor
  MaybeOrdered .F = MaybeF
  MaybeOrdered .≤ = ord
  MaybeOrdered .commute = Functor≡ (λ _ → refl) (λ _ → refl)

  record TSystem : Set(ℓ-suc ℓ) where
    field
      state : hSet ℓ
      trans : ⟨ state ⟩ → Maybe ⟨ state ⟩

    isterm : ⟨ state ⟩ → Type _
    isterm s = trans s ≡ nothing

    canStep : ⟨ state ⟩ → Type _
    canStep s = Σ ⟨ state ⟩ λ s' → trans s ≡ just s'

    steps : Type _
    steps = Σ ⟨ state ⟩ canStep

    term : Type _
    term = Σ ⟨ state ⟩ isterm

    eq-term : {t1 t2 : term} → fst t1 ≡ fst t2 → t1 ≡ t2
    eq-term p = ΣPathP (p , toPathP (isSetMaybe {A = state} _ _ _ _))

    hterm : hSet _
    hterm = term , isSetΣ (state .snd)
      λ _ → isOfHLevelSuc 1 ((isSetMaybe{A = state} _ _))

    dec-canStep : (s : ⟨ state ⟩) → Dec (canStep s)
    dec-canStep s with trans s
    ... | nothing = no λ x → ¬nothing≡just (x .snd)
    ... | just x = yes (x , refl)

    ¬-fiber→nothing : (s : ⟨ state ⟩ ) →
      ¬ (Σ ⟨ state ⟩ λ s' → trans s ≡ just s') → trans s ≡ nothing
    ¬-fiber→nothing s neg with trans s
    ... | nothing = refl
    ... | just x = ⊥elim (neg (x , refl))

    canStep? : (s : ⟨ state ⟩ ) → isterm s ⊎ canStep s
    canStep? s with dec-canStep s
    ... | yes p = inr p
    ... | no ¬p = inl (¬-fiber→nothing s ¬p)

    finish : ⟨ state ⟩ → Maybe term
    finish s = rec⊎ (λ prf → just (s , prf)) (λ _ → nothing) (canStep? s)

    -- terminals never step
    nostep : ((s , prf) : term) → canStep? s ≡ inl prf
    nostep (s , prf)  with canStep? s
    ... | inl x = cong inl (isSetMaybe {A = state} _ _ _ _)
    ... | inr (s' , prf') =
      ⊥elim {ℓ}{λ _ → inr (s' , prf') ≡ inl prf}
            ((¬nothing≡just (sym prf ∙ prf')))

    -- things that can step, always step
    willStep : ((s , (s' , prf)) : steps) → canStep? s ≡ inr (s' , prf)
    willStep (s , s' , prf) with canStep? s
    ... | inl x =
      ⊥elim {ℓ} {λ _ → inl x ≡ inr (s' , prf)} (¬nothing≡just  (sym x ∙ prf))
    ... | inr (s'' , prf') =
      cong inr (ΣPathP (goal , toPathP (isSetMaybe {A = state} _ _ _ _))) where
      goal : s''  ≡ s'
      goal = just-inj _ _ (sym prf' ∙ prf)

    finish-step : (t : steps) → finish (t .fst) ≡ nothing
    finish-step t = cong (λ h → rec⊎ _ _ h) (willStep t)

    finish-term : (t : term) → finish (t .fst) ≡ just t
    finish-term t = cong (λ h → rec⊎ _ _ h) (nostep t)

    partition : ⟨ state ⟩ → term ⊎ steps
    partition s with canStep? s
    ... | inl x = inl (s , x)
    ... | inr x = inr (s , x)

  open TSystem

  module _ (S T : TSystem) where
    record TSystem[_,_] : Set ℓ where
      field
        tmap : ⟨ S .state ⟩  → ⟨ T .state ⟩
        comm : {s : ⟨ S .state ⟩ } →
          _≤m_{T .state} (map-Maybe tmap (S .trans s))  (T .trans (tmap s))

    TSystemHomSigma : Type ℓ
    TSystemHomSigma =
      Σ (⟨ S .state ⟩  → ⟨ T .state ⟩)
        λ f → {s : ⟨ S .state ⟩ } →
          _≤m_ {T .state}(map-Maybe f (S .trans s) ) (T .trans (f s))

    TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
    unquoteDef TSysHomIsoΣ =
      defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))

  open TSystem[_,_]


  module _
    {S T : TSystem}
    (f  : TSystem[ S , T ])
    ((s , (s' , s↦s')) : steps S) where
    {-
        s --tmap f --> f(s)
        | S trans      | trans T
        |              |
        s'  ---------> f(s')
    -}

    step-T : Σ ⟨ T .state ⟩ (λ a' →
      (T .trans (tmap f s) ≡ just a') × (f .tmap s' ≡ a'))
    step-T =
      inversion
        (subst ( λ h → h ≤m T .trans (tmap f s))
        (cong₂ map-Maybe refl s↦s') (f .comm))

    commutes : T .trans (tmap f s) ≡ just (tmap f s')
    commutes = step-T  .snd .fst ∙ cong just (sym (step-T .snd .snd))

  TSysMap≡ : {S T : TSystem}{f g : TSystem[ S , T ]} →
    f .tmap ≡ g .tmap → f ≡ g
  TSysMap≡ {S}{T}{f}{g} p =
    isoFunInjective
      (TSysHomIsoΣ S T)
      f
      g
      (Σ≡Prop (λ f → isPropImplicitΠ λ _ → ≤m-isProp) p)

  open Iso
  TSysMapisSet : {S T : TSystem} → isSet (TSystem[ S , T ])
  TSysMapisSet {S} {T} =
    isSetRetract
      (fun (TSysHomIsoΣ S T))
      (inv (TSysHomIsoΣ S T))
      (leftInv (TSysHomIsoΣ S T))
    (isSetΣ (isSet→ (T .state .snd))
    λ _ → isProp→isSet (isPropImplicitΠ λ _ → ≤m-isProp))

  idSysHom : {S : TSystem} → TSystem[ S , S ]
  idSysHom .tmap s = s
  idSysHom {S} .comm {s} =
    subst (λ x → x ≤m S .trans s) (sym (map-Maybe-id _)) ≤m-refl

  _∘TS_ : {S T R : TSystem} →
    TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]
  _∘TS_ {S}{T}{R} f g .tmap = g .tmap ∘S f .tmap
  _∘TS_ {S}{T}{R} f g .comm {s} =
    ≤m-trans
      (≤m-trans
        (monoBind{S .state}{T .state})
        (monoF (f .comm)))
      (g .comm)

  TSysCat : Category _ _
  TSysCat .ob = TSystem
  TSysCat .Hom[_,_] = TSystem[_,_]
  TSysCat .id = idSysHom
  TSysCat ._⋆_ = _∘TS_
  TSysCat .⋆IdL _ =  TSysMap≡ refl
  TSysCat .⋆IdR _ =  TSysMap≡ refl
  TSysCat .⋆Assoc _ _ _ = TSysMap≡ refl
  TSysCat .isSetHom = TSysMapisSet

{-}
  module mod {ℓ : Level} where
  private
    set = SET ℓ
    𝓜 = model.𝓟Mon set
    self = model.self  set

    self[_,_] = self {ℓ} .Hom[_,_]

    E : EnrichedCategory 𝓜 _
    E = enrich TSysCat

    E[_,_] = E .Hom[_,_]

  semcmp : ob E → ob (self {ℓ})
  semcmp S .F-ob Γ =
    (Lift (set [ Γ , S .state ])) ,
    isOfHLevelLift 2 (set .isSetHom {Γ}{S .state})
  semcmp S .F-hom γ m = lift (m .lower ∘S γ)
  semcmp S .F-id = refl
  semcmp S .F-seq _ _ = refl

  stacktrans : {S T : TSystem {ℓ}} →
    NatTrans E[ S , T ] self[ semcmp S , semcmp T ]
  stacktrans {S}{T} .N-ob Γ (lift k) =
    pshhom
      (λ Δ (γ , m) → lift λ Δ∙ → k (γ Δ∙) .tmap (m .lower Δ∙))
      λ _ _ _ _  → cong lift refl
  stacktrans {S}{T} .N-hom f = funExt λ x → makePshHomPath refl

  EF : EnrichedFunctor 𝓜 E self
  EF .F₀ = semcmp
  EF .F₁ {S}{T} = stacktrans
  EF .Fid = makeNatTransPath
    (funExt λ Γ → funExt λ tt* → makePshHomPath refl)
  EF .Fseq = makeNatTransPath
    (funExt λ Γ → funExt λ tt* → makePshHomPath refl)

  sem : CBPVModel
  sem .𝓒 = set
  sem .𝓔 = E
  sem .vTy = hSet ℓ
  sem .vTm A = set [-, A ]
  sem .cTm = EF
  sem .emp =
    (Unit*  {ℓ}, isSetUnit*) ,
    λ X → (λ _ → tt*) , λ f → funExt λ _ → refl
  sem ._×c_ = λ A B → ⟨ A ⟩ × ⟨ B ⟩ , isSetΣ (A .snd) λ _ → B .snd
  sem .up×c Γ A =
    record {
      trans =
        natTrans
          (λ X f → (λ x → fst (f x)) , (λ x → snd (f x)))
          λ _ → refl ;
      nIso = λ X →
        isiso
          (λ {(f , g) x → (f x) , (g x)})
          (funExt (λ _ → refl))
          (funExt (λ _ → refl)) }
-- TODO define instance for syntax with defined substitution

-}