module HyperDoc.Operational.TransitionSystemAlt where

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Data.Maybe renaming (rec to mrec)
open import Cubical.Data.Maybe.More
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets

open Category
open Functor
open Iso

private
  variable
    ℓ : Level

ord : Functor (SET ℓ) (PREORDER ℓ ℓ)
ord .F-ob X = maybePreorder X , isSetMaybe {A = X}
ord .F-hom {A}{B}f = record { f = map-Maybe f ; isMon = mono-map }
ord .F-id = eqMon _ _ (funExt map-Maybe-id)
ord .F-seq _ _ = eqMon _ _ (funExt map-Maybe-seq)

-- an ordered functor for lax coalgebra homomorphisms
MaybeF : Functor (SET ℓ) (SET ℓ)
MaybeF = U ∘F ord

record TSystem (ℓ : Level) : Type(ℓ-suc ℓ) where
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

module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      tmap : ⟨ S .state ⟩  → ⟨ T .state ⟩
      comm : {s : ⟨ S .state ⟩ } →
        (map-Maybe tmap (S .trans s)) ≤ (T .trans (tmap s))

  TSystemHomSigma : Type ℓ
  TSystemHomSigma =
    Σ (⟨ S .state ⟩  → ⟨ T .state ⟩)
      λ f → {s : ⟨ S .state ⟩ } →
        (map-Maybe f (S .trans s) ) ≤ (T .trans (f s))

  TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
  unquoteDef TSysHomIsoΣ =
    defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))

open TSystem[_,_]

module _
  {S T : TSystem ℓ}
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
      (subst ( λ h → h ≤ T .trans (tmap f s))
      (cong₂ map-Maybe refl s↦s') (f .comm))

  commutes : T .trans (tmap f s) ≡ just (tmap f s')
  commutes = step-T  .snd .fst ∙ cong just (sym (step-T .snd .snd))

TSysMap≡ : {S T : TSystem ℓ}{f g : TSystem[ S , T ]} →
  f .tmap ≡ g .tmap → f ≡ g
TSysMap≡ {S = S}{T}{f}{g} p =
  isoFunInjective
    (TSysHomIsoΣ S T)
    f
    g
    (Σ≡Prop (λ f → isPropImplicitΠ λ _ → ≤-isProp{A = T .state}) p)

TSysMapisSet : {S T : TSystem ℓ} → isSet (TSystem[ S , T ])
TSysMapisSet {S = S} {T} = {!   !} 
{-}
  isSetRetract
    (fun (TSysHomIsoΣ S T))
    (inv (TSysHomIsoΣ S T))
    (leftInv (TSysHomIsoΣ S T))
  (isSetΣ (isSet→ (T .state .snd))
  λ _ → isProp→isSet (isPropImplicitΠ λ _ → ≤-isProp {A = T .state}))
 -}
idSysHom : {S : TSystem ℓ} → TSystem[ S , S ]
idSysHom .tmap s = s
idSysHom {S = S} .comm {s} =
  subst (λ x → x ≤ S .trans s) (sym (map-Maybe-id _)) ≤-refl

_∘TS_ : {S T R : TSystem ℓ} →
  TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]
_∘TS_ {S}{T}{R} f g .tmap = g .tmap ∘S f .tmap
_∘TS_ {S}{T}{R} f g .comm {s} =
  ≤-trans
    (≤-trans
      (mono-map-comp {f = f .tmap}{g .tmap})
      (mono-map (f .comm)))
    (g .comm)

TSysCat : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ
TSysCat {ℓ} .ob = TSystem ℓ
TSysCat .Hom[_,_] = TSystem[_,_]
TSysCat .id = idSysHom
TSysCat ._⋆_ = _∘TS_
TSysCat .⋆IdL _ =  TSysMap≡ refl
TSysCat .⋆IdR _ =  TSysMap≡ refl
TSysCat .⋆Assoc _ _ _ = TSysMap≡ refl
TSysCat .isSetHom = TSysMapisSet