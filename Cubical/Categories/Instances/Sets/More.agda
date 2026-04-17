module Cubical.Categories.Instances.Sets.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Base

private
  variable
    ℓ ℓ' : Level

open Functor
×SetsBif : Bifunctor (SET ℓ) (SET ℓ') (SET (ℓ-max ℓ ℓ'))
×SetsBif = mkBifunctorParAx F where
  open BifunctorParAx
  F : BifunctorParAx (SET _) (SET _) (SET _)
  F .Bif-ob A B .fst = ⟨ A ⟩ × ⟨ B ⟩
  F .Bif-ob A B .snd = isSet× (A .snd) (B .snd)
  F .Bif-homL = λ f d z → f (z .fst) , z .snd
  F .Bif-homR = λ c g z → z .fst , g (z .snd)
  F .Bif-hom× = λ f g z → f (z .fst) , g (z .snd)
  F .Bif-×-id = refl
  F .Bif-×-seq f f' g g' = refl
  F .Bif-L×-agree f = refl
  F .Bif-R×-agree g = refl

×Sets : Functor (SET ℓ ×C SET ℓ') (SET (ℓ-max ℓ ℓ'))
×Sets = BifunctorToParFunctor ×SetsBif

opaque
  open isUnivalent

  ~univSetβ : ∀ {A}{B} (f : CatIso (SET ℓ) A B)
    → ∀ b
    → transport (λ i → ⟨ CatIsoToPath isUnivalentSET f (~ i) ⟩) b ≡ f .snd .isIso.inv b
  ~univSetβ f b =
    transportRefl _ ∙ transportRefl _
    ∙ cong (f .snd .isIso.inv)
      (transportRefl _ ∙ transportRefl _ ∙ transportRefl _)

open isHAEquiv
module _ (A B : hSet ℓ) (f : CatIso (SET ℓ) A B) where
  private
    isSetA = A .snd
    isSetB = B .snd
  CatIso→HAE : HAEquiv ⟨ A ⟩ ⟨ B ⟩
  CatIso→HAE .fst = f .fst
  CatIso→HAE .snd .g = f .snd .isIso.inv
  CatIso→HAE .snd .linv = funExt⁻ (f .snd .isIso.ret)
  CatIso→HAE .snd .rinv = funExt⁻ (f .snd .isIso.sec)
  CatIso→HAE .snd .com a =
    isSet→SquareP (λ _ _ → isSetB) _ _ _ _

  CatIso→Iso' : Iso ⟨ A ⟩ ⟨ B ⟩
  CatIso→Iso' = isHAEquiv→Iso (CatIso→HAE .snd)

  CatIso→⟨A⟩≡⟨B⟩ : ⟨ A ⟩ ≡ ⟨ B ⟩
  CatIso→⟨A⟩≡⟨B⟩ = ua (_ , (isHAEquiv→isEquiv (CatIso→HAE .snd)))

  CatIso→A≡B : A ≡ B
  CatIso→A≡B = Σ≡Prop (λ _ → isPropIsSet) CatIso→⟨A⟩≡⟨B⟩

-- TODO: this should be upstreamed as it has better definitional
-- behavior than the upstream proof. The upstream proof has two more
-- transportRefls in it.
isUnivalentSET' : isUnivalent (SET ℓ)
isUnivalentSET' .univ (A , isSetA) (B , isSetB) = isIsoToIsEquiv
  ( CatIso→A≡B _ _
  , (λ f → CatIso≡ _ _ (funExt (λ x → transportRefl _ ∙ cong (f .fst) (transportRefl _))))
  , (λ p →
    cong (Σ≡Prop (λ C → isPropIsSet)) (isInjectiveTransport
      (funExt (λ x → transportRefl _ ∙ cong (transport (cong fst p)) (transportRefl _))))
    ∙ section-Σ≡Prop (λ C → isPropIsSet) p))

opaque
  open isUnivalent
  univSet'β : ∀ {A}{B} (f : CatIso (SET ℓ) A B)
    → ∀ a
    → transport (λ i → ⟨ CatIsoToPath isUnivalentSET' f i ⟩) a ≡ f .fst a
  univSet'β f a = transportRefl _

  private
    -- definitional behavior test
    univSet'-ua :
      ∀ {A}{B} (f : CatIso (SET ℓ) A B)
      → cong fst (CatIsoToPath isUnivalentSET' f)
        ≡ ua (_ , (isHAEquiv→isEquiv (CatIso→HAE _ _ f .snd)))
    univSet'-ua f = refl

  ~univSet'β : ∀ {A}{B} (f : CatIso (SET ℓ) A B)
    → ∀ b
    → transport (λ i → ⟨ CatIsoToPath isUnivalentSET' f (~ i) ⟩) b ≡ f .snd .isIso.inv b
  ~univSet'β f b = cong (f .snd .isIso.inv) (transportRefl _)

open import Cubical.Categories.Instances.ExtraId
_[-,_]Thick : ∀ {ℓC}{ℓC'} (C : Category ℓC ℓC') (x : C .Category.ob) → Presheaf C (ℓ-max ℓC ℓC')
C [-, x ]Thick = (ExtraId C [-, x ]) ∘F (σ C ^opF)
