{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
module Cubical.Categories.Monad.Instances.LocalState.PlotkinPower.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.Coend
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Tensor

open Category
open Bifunctor
open Functor
open UniversalElement
open NatTrans

module _ {ℓV : Level}(V : hSet ℓV) where

  Store : Functor (Inj ^op) (SET ℓV)
  Store .F-ob n = (Fin n → ⟨ V ⟩) , isSet→ (V .snd)
  Store .F-hom f s i = s (f .fst i)
  Store .F-id = refl
  Store .F-seq f g = refl

  Store+Iso : (n m : ℕ) →
    Iso (Fin (n + m) → ⟨ V ⟩)
        ((Fin n → ⟨ V ⟩) × (Fin m → ⟨ V ⟩))
  Store+Iso n m = equivToIso
    (compEquiv
      (preCompEquiv (FinSumChar.Equiv n m))
      Π⊎≃)

  splitStoreAlong : {n m : ℕ} (f : Injection n m) →
    (Fin m → ⟨ V ⟩) →
    (Fin n → ⟨ V ⟩) × (Fin (complementSize f) → ⟨ V ⟩)
  splitStoreAlong f Sm =
    Iso.fun Π⊎Iso
      (λ x → Sm (Iso.fun (finiteImageComplementIso f) x))

  splitStoreAlong-complement : {n m : ℕ} (f : Injection n m)
    (Sm : Fin m → ⟨ V ⟩) (c : Complement f) →
    splitStoreAlong f Sm .snd (complementIndex f c) ≡ Sm (c .fst)
  splitStoreAlong-complement f Sm c = cong
    (λ c' → Sm (Iso.fun (imageComplementIso f) (inr c')))
    (Iso.ret (complementEnumerationIso f) c)

  extendRight-Store : {p q : ℕ} (h : Injection p q) (ext : ℕ)
    (Sq : Fin q → ⟨ V ⟩) (Sext : Fin ext → ⟨ V ⟩) →
    Store .F-hom (extendRight h ext) (Sq ++Fin Sext)
    ≡ Store .F-hom h Sq ++Fin Sext
  extendRight-Store {p} {q} h ext Sq Sext = funExt point
    where
    lhs rhs : Fin (p + ext) → ⟨ V ⟩
    lhs = Store .F-hom (extendRight h ext) (Sq ++Fin Sext)
    rhs = Store .F-hom h Sq ++Fin Sext

    core : (z : Fin p ⊎ Fin ext) →
      lhs (FinSumChar.fun p ext z) ≡ rhs (FinSumChar.fun p ext z)
    core (inl i) =
      cong (Sq ++Fin Sext) (extendRight-map h ext (inl i))
      ∙ sym (FinSumChar.++FinInl q ext Sq Sext (h .fst i))
      ∙ FinSumChar.++FinInl p ext (Store .F-hom h Sq) Sext i
    core (inr i) =
      cong (Sq ++Fin Sext) (extendRight-map h ext (inr i))
      ∙ sym (FinSumChar.++FinInr q ext Sq Sext i)
      ∙ FinSumChar.++FinInr p ext (Store .F-hom h Sq) Sext i

    point : (x : Fin (p + ext)) → lhs x ≡ rhs x
    point x =
      cong lhs (sym (FinSumChar.sec p ext x))
      ∙ core (FinSumChar.inv p ext x)
      ∙ cong rhs (FinSumChar.sec p ext x)

  extendInjection-Store : {p ext : ℕ}
    (Sp : Fin p → ⟨ V ⟩) (Sext : Fin ext → ⟨ V ⟩) →
    Store .F-hom extendInjection (Sp ++Fin Sext) ≡ Sp
  extendInjection-Store {p} {ext} Sp Sext = funExt λ i →
    sym (FinSumChar.++FinInl p ext Sp Sext i)

  module _ {ℓA} (A : Functor Inj (SET ℓA)) where

    Cov : (n : ℕ) → Functor Inj (SET ℓA)
    Cov n = ×Sets ∘F (A ,F (Inj [ n ,-]))

    Diagram : (n : ℕ) →
      Bifunctor (Inj ^op) Inj (SET (ℓ-max ℓV ℓA))
    Diagram n = ×SetsBif ∘Fl Store ∘Fr Cov n

    LocalStateAt : (n : ℕ) → hSet (ℓ-max ℓA ℓV)
    LocalStateAt n = ⊗-Bif ⟅ Cov n , Store ⟆b

    localStateCowedge : (n : ℕ) → Cowedge (Diagram n) (LocalStateAt n)
    localStateCowedge n .Cowedge.ψ p (s , a , f) =
      (a , f) ,⊗ s
      where open Tensor (Cov n) Store
    localStateCowedge n .Cowedge.extranatural h =
      funExt λ (s , a , f) → sym (swap (a , f) h s)
      where open Tensor (Cov n) Store

    localStateCoend : (n : ℕ) → Coend (Diagram n)
    localStateCoend n .vertex = LocalStateAt n
    localStateCoend n .element = localStateCowedge n
    localStateCoend n .universal X = isoToIsEquiv
      (iso to from
        (λ w → Cowedge≡ (Diagram n) (funExt λ p → funExt λ x → refl))
        (λ g →
          funExt (R.ind (λ x → (X .snd) _ _) λ (a , f) s → refl)))
      where
      module R = Tensor (Cov n) Store

      to : (LocalStateAt n .fst → X .fst) → Cowedge (Diagram n) X
      to g = (CoendPsh (Diagram n) .F-hom g) (localStateCowedge n)

      from : Cowedge (Diagram n) X → LocalStateAt n .fst → X .fst
      from w = R.rec (X .snd)
        (λ (a , f) s → w .Cowedge.ψ _ (s , a , f))
        (λ (a , f) h s →
          sym (funExt⁻ (w .Cowedge.extranatural h) (s , a , f)))

  CovHom : {ℓ : Level} {A B : Functor Inj (SET ℓ)} →
    NatTrans A B → (n : ℕ) → NatTrans (Cov A n) (Cov B n)
  CovHom nt n .N-ob p (a , f) = nt .N-ob p a , f
  CovHom nt n .N-hom h = funExt λ (a , f) →
    ΣPathP (funExt⁻ (nt .N-hom h) a , refl)

  LocalStateHom : {ℓ : Level} {A B : Functor Inj (SET ℓ)} →
    NatTrans A B → (n : ℕ) →
    LocalStateAt A n .fst → LocalStateAt B n .fst
  LocalStateHom nt n = CovHom nt n ⊗NT idTrans Store

  LocalStateHom-id : {ℓ : Level} (A : Functor Inj (SET ℓ)) (n : ℕ)
    (x : LocalStateAt A n .fst) →
    LocalStateHom (idTrans A) n x ≡ x
  LocalStateHom-id A n = R.ind
    (λ x → LocalStateAt A n .snd _ _)
    (λ _ _ → refl)
    where module R = Tensor (Cov A n) Store

  LocalStateHom-seq : {ℓ : Level} {A B C : Functor Inj (SET ℓ)}
    (α : NatTrans A B) (β : NatTrans B C) (n : ℕ)
    (x : LocalStateAt A n .fst) →
    LocalStateHom (seqTrans α β) n x
    ≡ LocalStateHom β n (LocalStateHom α n x)
  LocalStateHom-seq α β n = R.ind
    (λ x → LocalStateAt _ n .snd _ _)
    (λ _ _ → refl)
    where module R = Tensor (Cov _ n) Store

  LocalStateReindex : {ℓ : Level} (A : Functor Inj (SET ℓ))
    {n m : ℕ} → Injection n m → (Fin m → ⟨ V ⟩) →
    LocalStateAt A n .fst → LocalStateAt A m .fst
  LocalStateReindex A {n} {m} f Sm = Rₙ.rec
    (LocalStateAt A m .snd)
    (λ { {p} (Ap , g) Sp →
      (A .F-hom extendInjection Ap , E.along g) Rₘ.,⊗
      (Sp ++Fin splitStoreAlong f Sm .snd) })
    (λ { {p} {q} (Ap , g) h Sq →
      let pair = (A .F-hom extendInjection Ap , E.along g)
          Sₑ = splitStoreAlong f Sm .snd
          Sq+ = Sq ++Fin Sₑ
      in
      cong (pair Rₘ.,⊗_) (sym (extendRight-Store h ext Sq Sₑ))
      ∙ Rₘ.swap pair (E.right h) Sq+
      ∙ cong (Rₘ._,⊗ Sq+) (pair-coherence Ap g h) })
    where
    module Rₙ = Tensor (Cov A n) Store
    module Rₘ = Tensor (Cov A m) Store
    module E = Extension f

    ext = E.size

    pair-coherence : ∀ {p q} (Ap : ⟨ A ⟅ p ⟆ ⟩)
      (g : Injection n p) (h : Injection p q) →
      Cov A m .F-hom (E.right h)
        (A .F-hom extendInjection Ap , E.along g)
      ≡
      ( A .F-hom extendInjection (A .F-hom h Ap)
      , E.along (composeInjection g h))
    pair-coherence {p} {q} Ap g h = ΣPathP
      ( (sym (funExt⁻ (A .F-seq
            (extendInjection {p} {ext}) (E.right h)) Ap)
        ∙ cong (λ k → A .F-hom k Ap)
            (E.right-extend h)
        ∙ funExt⁻ (A .F-seq h (extendInjection {q} {ext})) Ap)
      , E.along-natural g h)

  LocalStateReindex-id : {ℓ : Level} (A : Functor Inj (SET ℓ))
    {n : ℕ} (Sn : Fin n → ⟨ V ⟩) (x : LocalStateAt A n .fst) →
    LocalStateReindex A idInjection Sn x ≡ x
  LocalStateReindex-id A {n} Sn = R.ind
    (λ x → LocalStateAt A n .snd _ _)
    (λ { {p} (Ap , g) Sp →
      let ext = E.size
          Sₑ = splitStoreAlong (idInjection {n}) Sn .snd
          Sp+ = Sp ++Fin Sₑ
          along = E.along g
          along≡g+ =
            sym (Inj .⋆IdL along)
            ∙ E.square g
      in
      cong (λ j → (A .F-hom extendInjection Ap , j) R.,⊗ Sp+)
        along≡g+
      ∙ sym (R.swap (Ap , g) (extendInjection {p} {ext}) Sp+)
      ∙ cong ((Ap , g) R.,⊗_)
          (extendInjection-Store Sp Sₑ) })
    where
    module R = Tensor (Cov A n) Store
    module E = Extension (idInjection {n})

  [Inj,Set] : Category (ℓ-suc ℓV) ℓV
  [Inj,Set] = FUNCTOR Inj (SET ℓV)

  T : Functor [Inj,Set] [Inj,Set]
  T .F-ob A .F-ob n .fst =
    (Fin n → V .fst) → LocalStateAt A n .fst
  T .F-ob A .F-ob n .snd = isSet→ (LocalStateAt A n .snd)
  T .F-ob A .F-hom f t Sm =
    LocalStateReindex A f Sm (t (Store .F-hom f Sm))
  T .F-ob A .F-id {n} = funExt λ k → funExt λ Sn →
    LocalStateReindex-id A Sn (k Sn)
  T .F-ob A .F-seq f g = {! !}
  T .F-hom {A} {B} nt .N-ob n k Sn = LocalStateHom nt n (k Sn)
  T .F-hom {A} {B} nt .N-hom {n}{m} f =
    funExt λ k → funExt λ Sm →
      Rₙ.ind
        (λ x → LocalStateAt B m .snd
          (LocalStateHom nt m (LocalStateReindex A f Sm x))
          (LocalStateReindex B f Sm (LocalStateHom nt n x)))
        (λ { {p} (Ap , g) Sp →
          cong
            (λ b →
              (b , extendAlong f g) Rᴮₘ.,⊗
              (Sp ++Fin splitStoreAlong f Sm .snd))
            (funExt⁻ (nt .N-hom
              (extendInjection {p} {complementSize f})) Ap) })
        (k (Store .F-hom f Sm))
    where
    module Rₙ = Tensor (Cov A n) Store
    module Rᴮₘ = Tensor (Cov B m) Store
  T .F-id {x = A} = makeNatTransPath λ i n k Sn →
    LocalStateHom-id A n (k Sn) i
  T .F-seq α β = makeNatTransPath λ i n k Sn →
    LocalStateHom-seq α β n (k Sn) i
