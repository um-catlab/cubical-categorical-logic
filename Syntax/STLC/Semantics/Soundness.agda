module Syntax.STLC.Semantics.Soundness where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Data.Unit
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import NamedContext
open import UMP
open import NaturalModels.Cartesian
open import Syntax.STLC renaming (Tm to STm; Ty to STy)
open import Syntax.STLC.Semantics.Interpretation
open import Syntax.STLC.Semantics.Lindenbaum
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓ ℓ' ℓb ℓb' ℓc ℓc' ℓt ℓt' : Level
module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'}
         (S : SimplyTypedCategory ℓb ℓb' ℓt ℓt')
         (i₀ : Interp₀ Σ₀ S) (i₁ : Interp₁ {S = S} i₀ Σ₁)
         where
  open Category
  open Functor
  open STC-Functor
  open CartesianFunctor
  open UnivElt
  open isUniversal
  open Ctx
  open Sig₁

  open SimplyTypedCategory(S)
  open CartesianCategory(B)
  -- some abbreviations
  private
    Term = STm {Σ₀ = Σ₀} Σ₁
    Subst = STT-subst Σ₁

  ctx-sem : Ctx (STy Σ₀) → cat .ob
  ctx-sem = interpCtx {Σ₀ = Σ₀} {S = S} i₀

  term-sem : ∀ {Γ A} → Term Γ A → (Tm (i₀ A) ⟅ ctx-sem Γ ⟆) .fst
  term-sem (ivar x) =
    the-var ⟨ π _ _ x ⟩S
  term-sem {Γ} (fun-app f γ) = i₁ f ⟨ γ~ ⟩S where
    γ~ : cat [ ctx-sem Γ , ctx-sem (Σ₁ .src f) ]
    γ~ = prod-I (varFinSet (Σ₁ .src f))
                (λ x → sole (i₀ (Σ₁ .src f .el x)))
                λ x → term-sem (γ x) /the-var

  subst-sem : ∀ {Δ Γ} → Subst Δ Γ → cat [ (ctx-sem Δ) , (ctx-sem Γ) ]
  subst-sem {Δ = Δ}{Γ} γ =
    prod-I (varFinSet Γ)
           (λ x → sole (i₀ (Γ .el x)))
           λ x → term-sem (γ x) /the-var

  private
    subst-sem-comp-ind : ∀ {Ξ Δ Γ} → (γ : Subst Δ Γ) (δ : Subst Ξ Δ)
                       → (∀ x → term-sem (γ x ⟨ δ ⟩) ≡
                         term-sem (γ x) ⟨ subst-sem δ ⟩S)
                       → subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ) ≡
                         (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
    subst-sem-comp-ind {Γ = Γ} γ δ IH =
      determined-by-elt
        (finite-products (varFinSet Γ) (λ x → sole (i₀ (Γ .el x))) .universal)
        (funExt (λ x →
          π _ _ x ∘⟨ cat ⟩ subst-sem ( λ x → γ x ⟨ δ ⟩)
            ≡⟨ π∘prod-I _ _ (λ x → term-sem (γ x ⟨ δ ⟩) /the-var) x ⟩
          term-sem (γ x ⟨ δ ⟩) /the-var
            ≡[ i ]⟨ IH x i /the-var ⟩
          (term-sem (γ x) ⟨ subst-sem δ ⟩S) /the-var -- M/x o γ = M ⟨ γ ⟩ / x
            ≡⟨ sym (/the-var⟨⟩S _ _) ⟩
          (term-sem (γ x) /the-var) ∘⟨ cat ⟩ subst-sem δ
            ≡[ i ]⟨ π∘prod-I (varFinSet Γ) _
                  (λ x → term-sem (γ x) /the-var) x (~ i) ∘⟨ cat ⟩ subst-sem δ ⟩
          ((π _ _ x) ∘⟨ cat ⟩ subst-sem γ) ∘⟨ cat ⟩ subst-sem δ
            ≡[ i ]⟨ cat .⋆Assoc (subst-sem δ)
                    (subst-sem {Γ = Γ} γ) (π _ _ x) (~ i) ⟩
          (π _ _ x) ∘⟨ cat ⟩ (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
          ∎))

  term-sem-comp : ∀ {Δ Γ A} → (M : Term Γ A) → (γ : Subst Δ Γ)
                → term-sem (M ⟨ γ ⟩) ≡ term-sem M ⟨ subst-sem γ ⟩S
  term-sem-comp {Γ = Γ}{A} (ivar x) γ =
    term-sem (γ x)
      ≡⟨ sym (⟨/the-var⟩ (term-sem (γ x))) ⟩
    the-var ⟨ term-sem (γ x) /the-var ⟩S
      ≡[ i ]⟨ the-var ⟨ π∘prod-I (varFinSet Γ) (λ x → sole (i₀ (Γ .el x)))
              (λ x → term-sem (γ x) /the-var) x (~ i) ⟩S ⟩
    the-var ⟨ π (varFinSet Γ) _ x ∘⟨ cat ⟩ subst-sem γ ⟩S
      ≡⟨ ∘ᴾAssoc cat (Tm _) _ _ _ ⟩
    the-var ⟨ π _ _ x ⟩S ⟨ subst-sem γ ⟩S
    ∎
  term-sem-comp (fun-app f δ) γ =
    (i₁ f ⟨ subst-sem ( λ x → δ x ⟨ γ ⟩) ⟩S)
      ≡[ i ]⟨ i₁ f ⟨ subst-sem-comp-ind δ γ (λ x → term-sem-comp (δ x) γ) i ⟩S ⟩
    (i₁ f ⟨ subst-sem δ ∘⟨ cat ⟩ subst-sem γ ⟩S)
      ≡⟨ ∘ᴾAssoc cat (Tm _) _ _ _ ⟩
    i₁ f ⟨ subst-sem δ ⟩S ⟨ subst-sem γ ⟩S
    ∎

  subst-sem-comp : ∀ {Ξ Δ Γ} → (γ : Subst Δ Γ) (δ : Subst Ξ Δ)
                 → subst-sem {Γ = Γ} (comp-subst {Γ = Γ} γ δ) ≡
                  (subst-sem γ ∘⟨ cat ⟩ subst-sem δ)
  subst-sem-comp {Γ = Γ} γ δ =
    subst-sem-comp-ind γ δ (λ x → term-sem-comp (γ x) δ)

  subst-sem-id : ∀ Γ → subst-sem (id-subst Γ) ≡ cat .id
  subst-sem-id Γ =
    determined-by-elt
      (finite-products (varFinSet Γ) ((λ x → sole (i₀ (Γ .el x)))) .universal)
      (funExt (λ x →
        π _ _ x ∘⟨ cat ⟩ prod-I (varFinSet Γ)
                                (λ x → sole (i₀ (Γ .el x)))
                                (λ x → (the-var ⟨ π _ _ x ⟩S) /the-var)
          ≡[ i ]⟨ π∘prod-I (varFinSet Γ) (λ x → sole (i₀ (Γ .el x)))
                  ((λ x → (the-var ⟨ π _ _ x ⟩S) /the-var)) x i ⟩
        (the-var ⟨ π _ _ x ⟩S) /the-var
          ≡⟨ sym (η-expansion (Tm-repr (i₀ (Γ .el x)) .universal) (π _ _ x)) ⟩
        π _ _ x
          ≡⟨ sym (cat .⋆IdL _) ⟩
        π _ _ x ∘⟨ cat ⟩ cat .id ∎
        ))

  F-fin-prod-coinduction :
    ∀ {b} (J : FinSet ℓ-zero) (ctxts : J .fst → Ctx (STy Σ₀))
    → (Πᴾ cat (J .fst) (λ j → cat [-, ctx-sem (ctxts j) ]) ⟅ b ⟆) .fst
    → cat [ b , prod-ob (varFinSet (finProd J ctxts))
            ((λ (j , x) → sole (i₀ (ctxts j .el x)))) ]
  F-fin-prod-coinduction J ctxts γs =
    prod-I (varFinSet (finProd J ctxts)) (λ (j , x) → sole (i₀ (ctxts j .el x)))
      (λ (j , x) → π _ _ x ∘⟨ cat ⟩ γs j)

  F-Tm-repr-coinduction : ∀ {A b} (M : (Tm (i₀ A) ⟅ b ⟆) .fst) →
    cat [ b , prod-ob (Unit , isFinSetUnit) (λ tt → sole (i₀ A)) ]
  F-Tm-repr-coinduction M = prod-I _ _ (λ tt → M /the-var)

  -- for some reason Agda can't figure out termination unless I do this
  ctx-functor : Functor (STTCtx {Σ₀ = Σ₀}{Σ₁ = Σ₁}) cat
  ctx-functor .F-ob = ctx-sem
  ctx-functor .F-hom = subst-sem
  ctx-functor .F-id = subst-sem-id _
  ctx-functor .F-seq δ γ = subst-sem-comp γ δ

  -- Soundness says that we can translate any structure in the
  -- Lindenbaum algebra homomorphically into any CT structure.
  soundness : STC-Functor (Lindenbaum {Σ₀ = Σ₀}{Σ₁ = Σ₁}) S
  soundness .F-B .func = ctx-functor
  soundness .F-B .preserves-fin-products J ctxts .coinduction γs =
    F-fin-prod-coinduction J ctxts γs
  soundness .F-B .preserves-fin-products J ctxts .commutes γs =
    funExt (λ j →
      prod-I _ _
        (λ x → the-var ⟨ π _ _ (j , x) ⟩S /the-var) ∘⟨ cat ⟩
          (F-fin-prod-coinduction J ctxts γs)
        ≡[ i ]⟨ prod-I _ _
                (λ x → η-expansion
                  (Tm-repr (i₀ (ctxts j .el x)) .universal)
                  (π _ _ (j , x)) (~ i) )
                ∘⟨ cat ⟩ (F-fin-prod-coinduction J ctxts γs) ⟩
      prod-I _ _ (λ x → π _ _ (j , x)) ∘⟨ cat ⟩
          (F-fin-prod-coinduction J ctxts γs)
        ≡[ i ]⟨ coinduction-natural
          (finite-products
            (varFinSet (ctxts j))
            (λ x → sole (i₀ (ctxts j .el x))) .universal)
          (λ x → π _ _ (j , x)) ((F-fin-prod-coinduction J ctxts γs)) i ⟩
      prod-I _ _ (λ x → π _ _ (j , x) ∘⟨ cat ⟩
                    F-fin-prod-coinduction J ctxts γs)
        ≡[ i ]⟨ prod-I _ _
                (λ x → π∘prod-I
                       (varFinSet (finProd J ctxts)) _
                       ((λ (j , x) → π _ _ x ∘⟨ cat ⟩ γs j)) (j , x) i) ⟩
      prod-I _ _ (λ x → π _ _ x ∘⟨ cat ⟩ γs j)
        ≡[ i ]⟨ η-expansion (finite-products _ _ .universal) (γs j) (~ i) ⟩
      γs j ∎)
  soundness .F-B .preserves-fin-products J ctxts
    .is-uniq {b = b} γs δ γs-commutes =
    finite-products (varFinSet (finProd J ctxts)) ((λ (j , x) →
    sole (i₀ (ctxts j .el x)))) .universal .is-uniq _ _ (funExt (λ (j , x) →
      π _ _ (j , x) ∘⟨ cat ⟩ δ
        ≡[ i ]⟨ π∘prod-I
                (varFinSet (ctxts j))
                _ (λ x → π _ _ (j , x)) x (~ i) ∘⟨ cat ⟩ δ ⟩
      ((π _ _ x) ∘⟨ cat ⟩ prod-I _ _ (λ x → π _ _ (j , x))) ∘⟨ cat ⟩ δ
        ≡[ i ]⟨ cat .⋆Assoc δ
                    (prod-I (varFinSet (ctxts j)) _ (λ x → π _ _ (j , x)))
                    (π _ _ x) (~ i) ⟩
      (π _ _ x) ∘⟨ cat ⟩ (prod-I _ _ (λ x → π _ _ (j , x)) ∘⟨ cat ⟩ δ)
        ≡[ i ]⟨ π (varFinSet (ctxts j)) _ x ∘⟨ cat ⟩
                (prod-I _ _
                  (λ x → η-expansion
                         (Tm-repr (i₀ (ctxts j .el x)) .universal)
                         (π _ _ (j , x)) i) ∘⟨ cat ⟩ δ) ⟩
      (π _ _ x) ∘⟨ cat ⟩ ((prod-I _ _
          (λ x → the-var ⟨ π _ _ (j , x) ⟩S /the-var)) ∘⟨ cat ⟩ δ)
        ≡[ i ]⟨ (π _ _ x) ∘⟨ cat ⟩ γs-commutes i j ⟩
      (π _ _ x) ∘⟨ cat ⟩ γs j
      ∎
      ))
  soundness .F-Ty = i₀
  soundness .F-Tm A .NatTrans.N-ob Γ (lift M) = lift (term-sem M)
  soundness .F-Tm A .NatTrans.N-hom γ =
    funExt λ (lift M) → cong lift (term-sem-comp M γ)
  soundness .F-Tm-repr A .coinduction M = F-Tm-repr-coinduction M
  soundness .F-Tm-repr A .commutes M =
    (the-var ⟨ π _ _ tt ⟩S ⟨ F-Tm-repr-coinduction M ⟩S)
      ≡[ i ]⟨ ∘ᴾAssoc cat (Tm (i₀ A)) the-var (π _ _ tt)
              (F-Tm-repr-coinduction M) (~ i) ⟩
    (the-var ⟨ π _ _ tt ∘⟨ cat ⟩ F-Tm-repr-coinduction M ⟩S)
      ≡[ i ]⟨ the-var ⟨ π∘prod-I
                        (_ , isFinSetUnit) _ (λ tt → M /the-var) tt i ⟩S ⟩
    (the-var ⟨ M /the-var ⟩S)
      ≡⟨ Tm-repr (i₀ A) .universal .commutes M ⟩
    M ∎
  soundness .F-Tm-repr A .is-uniq M γ~ M-commutes =
    finite-products ((_ , isFinSetUnit)) _ .universal .is-uniq _ _
      (funExt (λ tt → Tm-repr _ .universal .is-uniq _ _
        ((the-var ⟨ π _ _ tt ∘⟨ cat ⟩ γ~ ⟩S
          ≡[ i ]⟨ ∘ᴾAssoc cat (Tm (i₀ A)) the-var (π _ _ tt) γ~ i ⟩
         the-var ⟨ π _ _ tt ⟩S ⟨ γ~ ⟩S
          ≡⟨ M-commutes ⟩
         M
         ∎))))
