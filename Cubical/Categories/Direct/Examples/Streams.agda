{-# OPTIONS --lossy-unification #-}
-- Streams internal to the topos of trees
module Cubical.Categories.Direct.Examples.Streams where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Nat.Order.Recursive as R
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Functors.Constant using (Constant)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat
  using (ℕCat ; ℕWFOrder ; ℕDirect)
import Cubical.Categories.Direct.StrictDownset as SD
open import Cubical.Categories.Direct.LocallyContractive

open Functor
open PshHomStrict

private
  dir = ℕDirect

  wfToR : ∀ {m n} → WFOrder._≤_ ℕWFOrder m n → m R.≤ n
  wfToR (inl lt)    = R.<-weaken lt
  wfToR {m} (inr e) = subst (m R.≤_) (Eq.eqToPath e) (R.≤-refl m)

  rToWf : ∀ {m n} → m R.≤ n → WFOrder._≤_ ℕWFOrder m n
  rToWf le with R.≤-split le
  ... | inl m<n = inl m<n
  ... | inr m≡n = inr (Eq.pathToEq m≡n)

  isProp↡ : ∀ n y → isProp ⟨ SD.↡Psh dir n .F-ob y ⟩
  isProp↡ n y = isPropΣ (WFOrder.isProp≤ ℕWFOrder) (λ _ → R.isProp≤)

  ▷ : Functor (PRESHEAF ℕCat ℓ-zero) (PRESHEAF ℕCat ℓ-zero)
  ▷ = SD.▷ dir

ConstP : hSet ℓ-zero → Presheaf ℕCat ℓ-zero
ConstP S = Constant _ _ S

constHom : ∀ {S T : hSet ℓ-zero} → (⟨ S ⟩ → ⟨ T ⟩)
         → PshHomStrict (ConstP S) (ConstP T)
constHom f .N-ob n = f
constHom f .N-hom n n' g s' s e = cong f e

constElt : ∀ {S : hSet ℓ-zero} → ⟨ S ⟩ → PshHomStrict UnitPsh (ConstP S)
constElt s .N-ob n _ = s
constElt s .N-hom n n' g _ _ e = refl

module Streams (𝔸 : hSet ℓ-zero) where

  𝔸P : Presheaf ℕCat ℓ-zero
  𝔸P = ConstP 𝔸

  F₀ : Presheaf ℕCat ℓ-zero → Presheaf ℕCat ℓ-zero
  F₀ X = 𝔸P ×Psh (▷ .F-ob X)

  F : Functor (PRESHEAF ℕCat ℓ-zero) (PRESHEAF ℕCat ℓ-zero)
  F .F-ob = F₀
  F .F-hom φ = idPshHomStrict ×PshHomStrict (▷ .F-hom φ)
  F .F-id =
    makePshHomStrictPath (funExt λ c → funExt λ p →
      ΣPathP (refl , makePshHomStrictPath refl))
  F .F-seq φ ψ =
    makePshHomStrictPath (funExt λ c → funExt λ p →
      ΣPathP (refl , makePshHomStrictPath refl))

  ▷appl : ∀ {X Y : Presheaf ℕCat ℓ-zero}
        → PshHomStrict (▷ .F-ob (X ⇒PshLargeStrict Y) ×Psh ▷ .F-ob X)
                       (▷ .F-ob Y)
  ▷appl {X} {Y} = ▷× dir ⋆PshHomStrict ▷ .F-hom (appPshHomStrict X Y)

  Fδ : ▷HomActionPsh dir F₀
  Fδ {X} {Y} = λPshHomStrict (F₀ X) (F₀ Y) body
    where
      P⇒ = ▷ .F-ob (X ⇒PshLargeStrict Y)
      hd : PshHomStrict (P⇒ ×Psh F₀ X) 𝔸P
      hd = π₂ _ _ ⋆PshHomStrict π₁ 𝔸P (▷ .F-ob X)
      tl : PshHomStrict (P⇒ ×Psh F₀ X) (▷ .F-ob Y)
      tl = ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict π₂ 𝔸P (▷ .F-ob X))
           ⋆PshHomStrict ▷appl
      body : PshHomStrict (P⇒ ×Psh F₀ X) (F₀ Y)
      body = ×PshIntroStrict hd tl

  Flaw : isContractiveHomAction dir F Fδ
  Flaw {X} {Y} h = makePshHomStrictPath (funExt λ n → funExt λ (a₀ , β) →
    ΣPathP (refl ,
      sym ( cong (λ z → ▷appl {X} {Y} .N-ob n (z , β))
              (funExt⁻ (▷ .F-ob (X ⇒PshLargeStrict Y) .F-id)
                 (▷transpose dir h .N-ob n tt))
          ∙ makePshHomStrictPath refl )))

  Fstream : LocallyContractive dir
  Fstream = F , Fδ , Flaw

  Str : Presheaf ℕCat ℓ-zero
  Str .F-ob n =
    ((k : ℕ) → k R.≤ n → ⟨ 𝔸 ⟩) , isSetΠ λ _ → isSetΠ λ _ → 𝔸 .snd
  Str .F-hom f s k k≤ = s k (R.≤-trans k≤ (wfToR f))
  Str .F-id =
    funExt λ s → funExt λ k → funExt λ k≤ → cong (s k) (R.isProp≤ _ _)
  Str .F-seq f g =
    funExt λ s → funExt λ k → funExt λ k≤ → cong (s k) (R.isProp≤ _ _)

  unroll : PshHomStrict Str (F₀ Str)
  unroll .N-ob n s = (s 0 tt) , tailα
    where
      tailα : PshHomStrict (SD.↡Psh dir n) Str
      tailα .N-ob y (f , q) k k≤y =
        s (suc k) (R.≤-trans {suc k} {suc y} {n} k≤y q)
      tailα .N-hom y y' g (f' , q') (f , q) e =
        funExt λ k → funExt λ k≤y → cong (s (suc k)) (R.isProp≤ _ _)
  unroll .N-hom n n' f s' s e =
    ΣPathP ( cong (s' 0) (R.isProp≤ _ _) ∙ (λ i → e i 0 tt)
           , makePshHomStrictPath (funExt λ y → funExt λ (g , r) →
               funExt λ k → funExt λ k≤y →
                 cong (s' (suc k)) (R.isProp≤ _ _)
                 ∙ (λ i → e i (suc k) (R.≤-trans {suc k} {suc y} {n} k≤y r)) ) )

  roll : PshHomStrict (F₀ Str) Str
  roll .N-ob n (a , α) zero     k≤n = a
  roll .N-ob n (a , α) (suc k') k≤n =
    α .N-ob k' (inl k≤n , k≤n) k' (R.≤-refl k')
  roll .N-hom n n' f (a' , α') (a , α) e =
    funExt λ { zero    → funExt λ k≤n → cong fst e
             ; (suc k') → funExt λ k≤n →
                 cong (λ z → α' .N-ob k' z k' (R.≤-refl k')) (isProp↡ n' k' _ _)
                 ∙ (λ i → (cong snd e i) .N-ob k' (inl k≤n , k≤n) k'
                            (R.≤-refl k')) }

  unroll-roll : unroll ⋆PshHomStrict roll ≡ idPshHomStrict
  unroll-roll = makePshHomStrictPath (funExt λ n → funExt λ s →
    funExt λ { zero     → funExt λ k≤n → cong (s zero)     (R.isProp≤ _ _)
             ; (suc k') → funExt λ k≤n → cong (s (suc k')) (R.isProp≤ _ _) })

  roll-unroll : roll ⋆PshHomStrict unroll ≡ idPshHomStrict
  roll-unroll = makePshHomStrictPath (funExt λ n → funExt λ (a , α) →
    ΣPathP ( refl
           , makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
               funExt λ k → funExt λ k≤y →
                 let wf  = rToWf k≤y
                     nat = α .N-hom k y wf (g , q)
                             (SD.↡Psh dir n .F-hom wf (g , q)) refl
                 in cong (λ z → α .N-ob k z k (R.≤-refl k)) (isProp↡ n k _ _)
                    ∙ sym (λ i → nat i k (R.≤-refl k))
                    ∙ cong (α .N-ob y (g , q) k) (R.isProp≤ _ _) ) ) )

  unfoldˢ : (X : Presheaf ℕCat ℓ-zero)
          → PshHomStrict X (F₀ X) → PshHomStrict X Str
  unfoldˢ X c = HyloPsh.hylo dir Fstream X Str c roll .fst

  foldˢ : (B : Presheaf ℕCat ℓ-zero)
        → PshHomStrict (F₀ B) B → PshHomStrict Str B
  foldˢ B a = HyloPsh.hylo dir Fstream Str B unroll a .fst

  headˢ : PshHomStrict Str 𝔸P
  headˢ = unroll ⋆PshHomStrict π₁ 𝔸P (▷ .F-ob Str)

  tailˢ : PshHomStrict Str (▷ .F-ob Str)
  tailˢ = unroll ⋆PshHomStrict π₂ 𝔸P (▷ .F-ob Str)

  elt : PshHomStrict UnitPsh Str → ℕ → ⟨ 𝔸 ⟩
  elt g k = g .N-ob k tt k (R.≤-refl k)

  takeˢ : ℕ → PshHomStrict UnitPsh Str → List (⟨ 𝔸 ⟩)
  takeˢ zero s = [ elt s zero ]
  takeˢ (suc n) s = takeˢ n s ∷ʳ elt s (suc n)

  consˢ : PshHomStrict (F₀ Str) Str
  consˢ = roll

  repeatˢ : PshHomStrict 𝔸P Str
  repeatˢ = unfoldˢ 𝔸P (×PshIntroStrict idPshHomStrict (SD.next dir 𝔸P))

  mapˢ : PshHomStrict 𝔸P 𝔸P → PshHomStrict Str Str
  mapˢ g = unfoldˢ Str (unroll ⋆PshHomStrict (g ×PshHomStrict idPshHomStrict))

  module _ (X : Presheaf ℕCat ℓ-zero) (c : PshHomStrict X (F₀ X)) where
    private
      module H = HyloPsh dir Fstream X Str c roll

    unfoldˢ-coalg :
      unfoldˢ X c ⋆PshHomStrict unroll ≡ c ⋆PshHomStrict F .F-hom (unfoldˢ X c)
    unfoldˢ-coalg =
      cong (_⋆PshHomStrict unroll) (H.hylo .snd)
      ∙ cong (λ z → c ⋆PshHomStrict (F .F-hom (unfoldˢ X c) ⋆PshHomStrict z))
          roll-unroll

    unfoldˢ-head : unfoldˢ X c ⋆PshHomStrict headˢ
                 ≡ c ⋆PshHomStrict π₁ 𝔸P (▷ .F-ob X)
    unfoldˢ-head =
      makePshHomStrictPath refl
      ∙ cong (_⋆PshHomStrict π₁ 𝔸P (▷ .F-ob Str)) unfoldˢ-coalg
      ∙ makePshHomStrictPath refl

    unfoldˢ-tail :
      unfoldˢ X c ⋆PshHomStrict tailˢ
      ≡ (c ⋆PshHomStrict π₂ 𝔸P (▷ .F-ob X)) ⋆PshHomStrict ▷ .F-hom (unfoldˢ X c)
    unfoldˢ-tail =
      makePshHomStrictPath refl
      ∙ cong (_⋆PshHomStrict π₂ 𝔸P (▷ .F-ob Str)) unfoldˢ-coalg
      ∙ makePshHomStrictPath refl

  mooreCoalg : (S : hSet ℓ-zero) (out : ⟨ S ⟩ → ⟨ 𝔸 ⟩) (nxt : ⟨ S ⟩ → ⟨ S ⟩)
             → PshHomStrict (ConstP S) (F₀ (ConstP S))
  mooreCoalg S out nxt =
    ×PshIntroStrict (constHom out)
      (constHom nxt ⋆PshHomStrict SD.next dir (ConstP S))

  moore : (S : hSet ℓ-zero) (out : ⟨ S ⟩ → ⟨ 𝔸 ⟩) (nxt : ⟨ S ⟩ → ⟨ S ⟩)
        → PshHomStrict (ConstP S) Str
  moore S out nxt = unfoldˢ (ConstP S) (mooreCoalg S out nxt)

  moore-head : (S : hSet ℓ-zero) (out : ⟨ S ⟩ → ⟨ 𝔸 ⟩) (nxt : ⟨ S ⟩ → ⟨ S ⟩)
             → moore S out nxt ⋆PshHomStrict headˢ ≡ constHom out
  moore-head S out nxt = unfoldˢ-head (ConstP S) (mooreCoalg S out nxt)

  moore-tail : (S : hSet ℓ-zero) (out : ⟨ S ⟩ → ⟨ 𝔸 ⟩) (nxt : ⟨ S ⟩ → ⟨ S ⟩)
             → moore S out nxt ⋆PshHomStrict tailˢ
               ≡ (constHom nxt ⋆PshHomStrict SD.next dir (ConstP S))
                 ⋆PshHomStrict ▷ .F-hom (moore S out nxt)
  moore-tail S out nxt = unfoldˢ-tail (ConstP S) (mooreCoalg S out nxt)

-- Fibonacci as a Moore machine on state ℕ × ℕ
module Fibonacci where
  open import Cubical.Data.Nat using (_+_)
  open Streams (ℕ , isSetℕ)

  ℕ×ℕ : hSet ℓ-zero
  ℕ×ℕ = (ℕ × ℕ) , isSet× isSetℕ isSetℕ

  fibNext : ℕ × ℕ → ℕ × ℕ
  fibNext (a , b) = (b , a + b)

  fibStr : PshHomStrict (ConstP ℕ×ℕ) Str
  fibStr = moore ℕ×ℕ fst fibNext

  fib-head : fibStr ⋆PshHomStrict headˢ ≡ constHom fst
  fib-head = moore-head ℕ×ℕ fst fibNext

  fib-tail : fibStr ⋆PshHomStrict tailˢ
           ≡ (constHom fibNext ⋆PshHomStrict SD.next dir (ConstP ℕ×ℕ))
             ⋆PshHomStrict ▷ .F-hom fibStr
  fib-tail = moore-tail ℕ×ℕ fst fibNext

  fib : PshHomStrict UnitPsh Str
  fib = constElt (0 , 1) ⋆PshHomStrict fibStr

  _ : takeˢ 7 fib ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ 13 ∷ []
  _ = refl

-- primality, decided by Löb induction
-- n is prime iff it is indivisible by every smaller prime
-- this is overkill, as we could actually stop at primes bound by sqrt
module Primality where
  open import Cubical.Data.Bool using (Bool ; true ; false ; Dec→Bool)
  open import Cubical.Data.Empty as ⊥ using ()
  open import Cubical.Data.Nat.Mod using (_mod_)
  open import Cubical.Data.Nat.Properties using (discreteℕ)
  open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; isProp¬)
  open import Cubical.Relation.Nullary.Properties using (isPropDec)
  open import Cubical.Relation.Nullary.More using (Dec× ; Dec¬ ; Dec→)

  decAllBelow : (n : ℕ) (Q : ∀ p → p R.< n → Type)
                (dQ : ∀ p (q : p R.< n) → Dec (Q p q))
              → Dec (∀ p (q : p R.< n) → Q p q)
  decAllBelow zero    Q dQ = yes λ p q → ⊥.rec q
  decAllBelow (suc m) Q dQ =
    combine
      (decAllBelow m (λ p q → Q p (R.<-weaken q)) (λ p q → dQ p (R.<-weaken q)))
      (dQ m (R.≤-refl m))
    where
      combine : Dec (∀ p (q : p R.< m) → Q p (R.<-weaken q))
              → Dec (Q m (R.≤-refl m))
              → Dec (∀ p (q : p R.< suc m) → Q p q)
      combine (no ¬rec) _        = no λ f → ¬rec λ p q → f p (R.<-weaken q)
      combine (yes _)   (no ¬pm) = no λ f → ¬pm (f m (R.≤-refl m))
      combine (yes rec) (yes pm) = yes λ p q → resolve p q (R.≤-split q)
        where
          resolve : ∀ p (q : p R.< suc m) → (p R.< m) ⊎ (p ≡ m) → Q p q
          resolve p q (inl p<m) = subst (Q p) (R.isProp≤ _ _) (rec p p<m)
          resolve p q (inr p≡m) = transport (λ i → Q (p≡m (~ i)) (qPath i)) pm
            where
              qPath : PathP (λ i → (p≡m (~ i)) R.< suc m) (R.≤-refl m) q
              qPath = isProp→PathP (λ _ → R.isProp≤) (R.≤-refl m) q

  A : ℕ → hSet (ℓ-suc ℓ-zero)
  A n = (Σ[ P ∈ hProp ℓ-zero ] Dec ⟨ P ⟩)
      , isSetΣ isSetHProp (λ P → isProp→isSet (isPropDec (P .snd)))

  step : ∀ n → ⟨ SD.▷Fam dir {ℓF = ℓ-suc ℓ-zero} A n ⟩ → ⟨ A n ⟩
  step n β = IsPrime , decIsPrime
    where
      primeBelow : ∀ p → p R.< n → ⟨ A p ⟩
      primeBelow p q = SD.▷FamApp dir {ℓF = ℓ-suc ℓ-zero} A β (inl q) q

      PassesTrial : ∀ p → p R.< n → Type
      PassesTrial p q = ⟨ primeBelow p q .fst ⟩ → ¬ (n mod p ≡ 0)

      IsPrime : hProp ℓ-zero
      IsPrime = ((2 R.≤ n) × (∀ p (q : p R.< n) → PassesTrial p q))
        , isProp× R.isProp≤ (isPropΠ2 λ p q → isPropΠ λ _ → isProp¬ _)

      decIsPrime : Dec ⟨ IsPrime ⟩
      decIsPrime = Dec× (2 R.≤? n)
        (decAllBelow n PassesTrial λ p q →
          Dec→ (primeBelow p q .snd) (Dec¬ (discreteℕ (n mod p) 0)))

  fixP : ∀ n → ⟨ A n ⟩
  fixP = SD.löbFam dir {ℓF = ℓ-suc ℓ-zero} A step

  Prime : ℕ → Type
  Prime n = ⟨ fst (fixP n) ⟩

  decPrime : ∀ n → Dec (Prime n)
  decPrime n = snd (fixP n)

  isPropPrime : ∀ n → isProp (Prime n)
  isPropPrime n = fst (fixP n) .snd

  -- Description of primality using Löb unfolding
  Prime-characterization : ∀ n
    → Prime n
    ≡ ((2 R.≤ n) × (∀ p (q : p R.< n) → Prime p → ¬ (n mod p ≡ 0)))
  Prime-characterization n =
    cong (λ d → ⟨ d .fst ⟩)
      (SD.löbFam-unfold dir {ℓF = ℓ-suc ℓ-zero} A step n)

  PrimeDec : hSet ℓ-zero
  PrimeDec = (Σ[ n ∈ ℕ ] Dec (Prime n))
           , isSetΣ isSetℕ (λ n → isProp→isSet (isPropDec (isPropPrime n)))

  prime? : ⟨ PrimeDec ⟩ → Maybe ℕ
  prime? (n , yes p) = just n
  prime? (n , no ¬p) = nothing

  open Streams PrimeDec

  primesStr : PshHomStrict (ConstP (ℕ , isSetℕ)) Str
  primesStr = moore (ℕ , isSetℕ) (λ n → n , decPrime n) suc

  primes : PshHomStrict UnitPsh Str
  primes = constElt 0 ⋆PshHomStrict primesStr

  primesUpTo : ℕ → List ℕ
  primesUpTo n = filterMap prime? (takeˢ n primes)

  _ : primesUpTo 20 ≡ 2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ []
  _ = refl
