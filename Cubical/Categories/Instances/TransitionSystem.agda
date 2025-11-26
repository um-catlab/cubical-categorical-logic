module Cubical.Categories.Instances.TransitionSystem where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎ ; map to map⊎)
open import Cubical.Data.Sum.More

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category

open Category
open Iso

private
  variable
    ℓ : Level

record TSystem (ℓ : Level) : Type(ℓ-suc ℓ) where
  field
    state : hSet ℓ
    term : hSet ℓ
    trans : ⟨ state ⟩ → ⟨ term ⟩ ⊎ ⟨ state ⟩ 

open TSystem

module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      smap : ⟨ S .state ⟩  → ⟨ T .state ⟩
      tmap : ⟨ S .term ⟩ → ⟨ T . term ⟩ ⊎ ⟨ T . state ⟩
      comm : {s : ⟨ S . state ⟩} → 
        T .trans (smap s) ≡ rec⊎ tmap (λ s' → inr (smap s')) (S .trans s) 
    {-
      If s steps to a terminal
      then tmap must behave the same as smap
        
        s -- S .trans --> ■ 
        |                 |
      f .smap           f .tmap
        |                 |
        t -- T .trans --> t'

      If s steps to a non-terminal
      then we just have a graph homomorphism

        s -- S .trans --> s'
        |                 |
      f .smap           f .smap 
        |                 |
        t -- T .trans --> t'
    -}


  TSystemHomSigma : Type ℓ
  TSystemHomSigma =
    Σ[ smap ∈ (⟨ S .state ⟩ → ⟨ T .state ⟩) ]
    Σ[ tmap ∈ (⟨ S .term ⟩ → ⟨ T .term ⟩ ⊎ ⟨ T .state ⟩ ) ] 
    ({s : ⟨ S .state ⟩} → 
      T .trans (smap s) ≡ rec⊎ tmap (λ s' → inr (smap s')) (S .trans s))

  TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
  unquoteDef TSysHomIsoΣ =
    defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))
    
open TSystem[_,_]

TSysMap≡ : {S T : TSystem ℓ}{f g : TSystem[ S , T ]} →
  f .smap ≡ g .smap → 
  f .tmap ≡ g .tmap → f ≡ g
TSysMap≡ {S = S}{T}{f}{g} p q = 
  isoFunInjective 
    (TSysHomIsoΣ S T) 
    f 
    g 
    (ΣPathP (p , ΣPathP (q , implicitFunExt λ {_} → 
    toPathP (isSet⊎ (T .term .snd) (T .state .snd) _ _  _ _))))

TSysMapisSet : {S T : TSystem ℓ} → isSet (TSystem[ S , T ])
TSysMapisSet {S = S} {T} =
  isSetRetract
    (fun (TSysHomIsoΣ S T))
    (inv (TSysHomIsoΣ S T))
    (leftInv (TSysHomIsoΣ S T))
    (isSetΣ (isSet→ (T .state .snd)) λ _ → 
    isSetΣ (isSet→ (isSet⊎ (T .term .snd) (T .state .snd))) 
    λ _ → isProp→isSet (isPropImplicitΠ  λ _ → 
    isSet⊎ (T .term .snd) (T .state .snd) _ _))

idSysHom : {S : TSystem ℓ} → TSystem[ S , S ]
idSysHom {S} .smap x = x
idSysHom {S} .tmap x = inl x
idSysHom {S = S} .comm {s = s} with S .trans s 
... | inl x = refl
... | inr x = refl

match : {S : TSystem ℓ} → (s : ⟨ S .state ⟩) → 
  (Σ[ t ∈ ⟨ S .term ⟩ ] (S .trans s ≡ inl t)) 
  ⊎ (Σ[ s' ∈ ⟨ S .state ⟩ ] S .trans s ≡ inr s')
match {S = S} s with S .trans s 
... | inl x = inl (x , refl)
... | inr x = inr (x , refl)

_∘TS_ : {S T R : TSystem ℓ} →
  TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]
(f ∘TS g) .smap = g .smap ∘S f .smap
(f ∘TS g) .tmap = rec⊎ (g .tmap) (inr ∘S g .smap) ∘S f .tmap
(_∘TS_){S = S}{T}{R}f g .comm {s} with match {S = S} s 
... | inl (t , p) = goal  
    ∙ cong₃ rec⊎ refl refl (sym p) where 

    have : T .trans (f .smap s) ≡ f .tmap t
    have = f .comm {s} ∙ cong₃  rec⊎ refl refl p 

    goal : R .trans (g .smap (f .smap s)) 
      ≡ rec⊎ (g .tmap) (λ s' → inr (g .smap s')) (f .tmap t) 
    goal  = g .comm {f .smap s} ∙ cong₃ rec⊎ refl refl have
    
... | inr (s' , p) = goal 
    ∙ cong₃ rec⊎ refl refl (sym p) where 

    have : T .trans (f .smap s) ≡ inr (f .smap s') 
    have = f .comm {s} ∙ cong₃ rec⊎ refl refl p

    goal : R .trans (g .smap (f .smap s)) ≡ inr (g .smap (f .smap s')) 
    goal = g .comm {f .smap s} ∙ cong₃ rec⊎ refl refl have

TSysCat : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ
TSysCat .ob = TSystem _
TSysCat .Hom[_,_] = TSystem[_,_]
TSysCat .id = idSysHom
TSysCat ._⋆_ = _∘TS_
TSysCat .⋆IdL _ = TSysMap≡ refl refl
TSysCat .⋆IdR _ = TSysMap≡ refl (funExt λ _ → rec-eta)
TSysCat .⋆Assoc {x = S} f g h = TSysMap≡ refl (funExt goal) where 
  goal : (t : ⟨ S .term ⟩)  → rec⊎ (h .tmap) (λ x → inr (h .smap x))
      (rec⊎ (g .tmap) (λ x → inr (g .smap x)) (f .tmap t))
      ≡
      rec⊎ (λ x → rec⊎ (h .tmap) (λ x₁ → inr (h .smap x₁)) (g .tmap x))
      (λ x → inr (h .smap (g .smap x))) (f .tmap t)
  goal t with f .tmap t 
  ... | inl x = refl
  ... | inr x = refl
TSysCat .isSetHom = TSysMapisSet
