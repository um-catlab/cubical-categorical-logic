module Cubical.Algebra.Theory.Theories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category

private
  variable
    ℓ ℓ' ℓ'' ℓE ℓv ℓX : Level
    ℓ1 ℓ2 ℓ3 ℓ4 : Level

open AlgTheorySig

record SigMap {ℓ1 ℓ2} (σ : AlgTheorySig ℓ1 ℓ') (τ : AlgTheorySig ℓ2 ℓ')
  : Type (ℓ-max (ℓ-max ℓ1 ℓ2) ℓ') where
  field
    onOps : σ .ops → τ .ops
    unArity : ∀ op → τ .arities (onOps op) → σ .arities op

open SigMap

module _ {σ : AlgTheorySig ℓ ℓ'} where
  idSigMap : SigMap σ σ
  idSigMap .onOps op = op
  idSigMap .unArity op a = a

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  {υ : AlgTheorySig ℓ3 ℓ'} (F : SigMap σ τ) (G : SigMap τ υ) where
  _⋆SigMap_ : SigMap σ υ
  _⋆SigMap_ .onOps = G .onOps ∘ F .onOps
  _⋆SigMap_ .unArity op a = F .unArity op (G .unArity (F .onOps op) a)

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  (F : SigMap σ τ) where
  ⋆SigMapIdL : idSigMap ⋆SigMap F ≡ F
  ⋆SigMapIdL = refl
  ⋆SigMapIdR : F ⋆SigMap idSigMap ≡ F
  ⋆SigMapIdR = refl

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  {υ : AlgTheorySig ℓ3 ℓ'} {ν : AlgTheorySig ℓ4 ℓ'}
  (F : SigMap σ τ) (G : SigMap τ υ) (H : SigMap υ ν) where
  ⋆SigMapAssoc : ((F ⋆SigMap G) ⋆SigMap H) ≡ (F ⋆SigMap (G ⋆SigMap H))
  ⋆SigMapAssoc = refl

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  (F : SigMap σ τ) where

  reOps : {X : Type ℓX}
    → (∀ (op : τ .ops) → (τ .arities op → X) → X)
    → (∀ (op : σ .ops) → (σ .arities op → X) → X)
  reOps α op x = α (F .onOps op) (λ a → x (F .unArity op a))

  mapTm : {V : Type ℓv} → Tm σ V → Tm τ V
  mapTm (var v) = var v
  mapTm (node op ts) = node (F .onOps op) (λ a → mapTm (ts (F .unArity op a)))

  TmRec-mapTm : {X : Type ℓX}
    (α : ∀ (op : τ .ops) → (τ .arities op → X) → X)
    {V : Type ℓv} (ρ : V → X) (M : Tm σ V)
    → TmRec (reOps α) ρ M ≡ TmRec α ρ (mapTm M)
  TmRec-mapTm α ρ (var v) = refl
  TmRec-mapTm α ρ (node op ts) =
    cong (α (F .onOps op))
      (funExt (λ a → TmRec-mapTm α ρ (ts (F .unArity op a))))

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  {υ : AlgTheorySig ℓ3 ℓ'} (F : SigMap σ τ) (G : SigMap τ υ) where
  reOps-⋆ : {X : Type ℓX}
    (α : ∀ (op : υ .ops) → (υ .arities op → X) → X)
    → reOps (F ⋆SigMap G) α ≡ reOps F (reOps G α)
  reOps-⋆ α = refl

record SetSig ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    sig : AlgTheorySig ℓ ℓ'
    isSetOps : isSet (sig .ops)
    isSetArities : ∀ op → isSet (sig .arities op)
open SetSig

SigMapΣ : (σ : AlgTheorySig ℓ1 ℓ') (τ : AlgTheorySig ℓ2 ℓ')
  → Type (ℓ-max (ℓ-max ℓ1 ℓ2) ℓ')
SigMapΣ σ τ = Σ[ h ∈ (σ .ops → τ .ops) ]
  (∀ op → τ .arities (h op) → σ .arities op)

SigMapIsoΣ : {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  → Iso (SigMap σ τ) (SigMapΣ σ τ)
unquoteDef SigMapIsoΣ = defineRecordIsoΣ SigMapIsoΣ (quote SigMap)

isSetSigMap : {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  → isSet (τ .ops) → (∀ op → isSet (σ .arities op)) → isSet (SigMap σ τ)
isSetSigMap isSetτops isSetσar =
  isOfHLevelRetractFromIso 2 SigMapIsoΣ
    (isSetΣ (isSet→ isSetτops)
      (λ h → isSetΠ λ op → isSet→ (isSetσar op)))

SIG : ∀ ℓ ℓ' → Category (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
SIG ℓ ℓ' .Category.ob = SetSig ℓ ℓ'
SIG ℓ ℓ' .Category.Hom[_,_] σ τ = SigMap (σ .sig) (τ .sig)
SIG ℓ ℓ' .Category.id = idSigMap
SIG ℓ ℓ' .Category._⋆_ = _⋆SigMap_
SIG ℓ ℓ' .Category.⋆IdL f = refl
SIG ℓ ℓ' .Category.⋆IdR f = refl
SIG ℓ ℓ' .Category.⋆Assoc f g h = refl
SIG ℓ ℓ' .Category.isSetHom {x = σ} {y = τ} =
  isSetSigMap (τ .isSetOps) (σ .isSetArities)

PresEqns : {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (τeq : AlgTheoryEqns τ ℓE ℓv)
  (ℓX : Level) (F : SigMap σ τ) → Type _
PresEqns σeq τeq ℓX F =
  (X : hSet ℓX) (B : Alg τeq ⟨ X ⟩)
  (eqn : AlgTheoryEqns.eqns σeq) (ρ : AlgTheoryEqns.vars σeq eqn → ⟨ X ⟩)
  → TmRec (reOps F (Alg.⟨_⟩⟦_⟧op B)) ρ (AlgTheoryEqns.lhs σeq eqn)
    ≡ TmRec (reOps F (Alg.⟨_⟩⟦_⟧op B)) ρ (AlgTheoryEqns.rhs σeq eqn)

isPropPresEqns : {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  {σeq : AlgTheoryEqns σ ℓ'' ℓv} {τeq : AlgTheoryEqns τ ℓE ℓv}
  {F : SigMap σ τ} → isProp (PresEqns σeq τeq ℓX F)
isPropPresEqns = isPropΠ4 λ X _ _ _ → X .snd _ _

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  {σeq : AlgTheoryEqns σ ℓ'' ℓv} {τeq : AlgTheoryEqns τ ℓE ℓv}
  {F : SigMap σ τ} (pF : PresEqns σeq τeq ℓX F) where

  reindexModel : (X : hSet ℓX) → Alg τeq ⟨ X ⟩ → Alg σeq ⟨ X ⟩
  reindexModel X B .Alg.⟨_⟩⟦_⟧op = reOps F (Alg.⟨_⟩⟦_⟧op B)
  reindexModel X B .Alg.⟦_⟧eqn = pF X B

  reindexHomo : {X Y : hSet ℓX} {f : ⟨ X ⟩ → ⟨ Y ⟩}
    {B : Alg τeq ⟨ X ⟩} {C : Alg τeq ⟨ Y ⟩}
    → Homo τeq f B C → Homo σeq f (reindexModel X B) (reindexModel Y C)
  reindexHomo ϕ .Homo.op-hom op x y eq =
    Homo.op-hom ϕ (F .onOps op) _ y eq

  MODReindexᴰ : Functorⱽ (MODᴰ τeq ℓX) (MODᴰ σeq ℓX)
  MODReindexᴰ .Functorᴰ.F-obᴰ {x = X} = reindexModel X
  MODReindexᴰ .Functorᴰ.F-homᴰ = reindexHomo
  MODReindexᴰ .Functorᴰ.F-idᴰ = refl
  MODReindexᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

THEORYᴰ : ∀ ℓ ℓ' ℓ'' ℓv ℓX → Categoryᴰ (SIG ℓ ℓ') _ _
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.ob[_] σ = AlgTheoryEqns (σ .sig) ℓ'' ℓv
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.Hom[_][_,_] F σeq τeq =
  PresEqns σeq τeq ℓX F
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.idᴰ X B = Alg.⟦_⟧eqn B
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ._⋆ᴰ_ pF pG X B =
  pF X (reindexModel pG X B)
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆IdLᴰ fᴰ = refl
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆IdRᴰ fᴰ = refl
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX .Categoryᴰ.isSetHomᴰ {xᴰ = σeq} {yᴰ = τeq} =
  isProp→isSet (isPropPresEqns {σeq = σeq} {τeq = τeq})

THEORY : ∀ ℓ ℓ' ℓ'' ℓv ℓX → Category _ _
THEORY ℓ ℓ' ℓ'' ℓv ℓX = ∫C (THEORYᴰ ℓ ℓ' ℓ'' ℓv ℓX)
