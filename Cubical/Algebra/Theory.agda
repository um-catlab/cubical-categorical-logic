-- Arbitrary algebraic theories
module Cubical.Algebra.Theory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰ''' ℓX ℓY ℓZ ℓW : Level

record AlgTheorySig ℓ ℓ' : Type (ℓ-suc (ℓ ⊔ℓ ℓ')) where
  field
    ops : Type ℓ -- S from Cubical.Data.W
    arities : ops → Type ℓ' -- P from Cbuical.Data.W

module _ (σ : AlgTheorySig ℓ ℓ') where
  open AlgTheorySig σ
  data Tm {ℓv} (V : Type ℓv) : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓv) where
    var : V → Tm V
    node : (op : ops) → (arities op → Tm V) → Tm V

record AlgTheoryEqns {ℓ ℓ'} (σ : AlgTheorySig ℓ ℓ') ℓ'' ℓv
  : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓ-suc ℓ'' ⊔ℓ ℓ-suc ℓv) where
  open AlgTheorySig σ public
  field
    eqns : Type ℓ''
    vars : eqns → Type ℓv
    lhs rhs : (eqn : eqns) → Tm σ (vars eqn)

module _ {σ : AlgTheorySig ℓ ℓ'} where
  open AlgTheorySig σ

  TmRec : {X : Type ℓX} (α : ∀ (op : ops) → (arities op → X) → X)
    {V : Type ℓv} (ρ : V → X) → Tm σ V → X
  TmRec α ρ (var v) = ρ v
  TmRec α ρ (node op ts) = α op (λ a → TmRec α ρ (ts a))

  TmRecᴰ : {X : Type ℓX} (α : ∀ (op : ops) → (arities op → X) → X)
    (Xᴰ : X → Type ℓᴰ)
    (αᴰ : ∀ (op : ops) {x : arities op → X}
        → ((a : arities op) → Xᴰ (x a)) → Xᴰ (α op x))
    {V : Type ℓv} {ρ : V → X} (ρᴰ : (v : V) → Xᴰ (ρ v))
    (M : Tm σ V) → Xᴰ (TmRec α ρ M)
  TmRecᴰ α Xᴰ αᴰ ρᴰ (var v) = ρᴰ v
  TmRecᴰ α Xᴰ αᴰ ρᴰ (node op ts) =
    αᴰ op (λ a → TmRecᴰ α Xᴰ αᴰ ρᴰ (ts a))

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  open AlgTheoryEqns σeq
  record Alg (X : Type ℓX) : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓ'' ⊔ℓ ℓv ⊔ℓ ℓX) where
    field
      ⟨_⟩⟦_⟧op : ∀ (op : ops) → (arities op → X) → X
    ⟦_⟧Tm : {V : Type ℓv} (ρ : V → X) → Tm σ V → X
    ⟦_⟧Tm = TmRec ⟨_⟩⟦_⟧op
    field
      ⟦_⟧eqn : ∀ (eqn : eqns) (ρ : vars eqn → X)
        → ⟦ ρ ⟧Tm (lhs eqn) ≡ ⟦ ρ ⟧Tm (rhs eqn)

  record Homo {X : Type ℓX} {Y : Type ℓY} (f : X → Y) (B : Alg X) (C : Alg Y)
    : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓX ⊔ℓ ℓY) where
    private
      module B = Alg B
      module C = Alg C
    field
      op-hom : ∀ (op : ops) (x : arities op → X) y →
        y ≡ B.⟨ op ⟩⟦ x ⟧op  →
        f y ≡ C.⟨ op ⟩⟦ f ∘ x ⟧op
    op-hom' : ∀ (op : ops) (x : arities op → X) → f B.⟨ op ⟩⟦ x ⟧op ≡ C.⟨ op ⟩⟦ f ∘ x ⟧op
    op-hom' op x = op-hom op x _ refl

  open Homo
  module _ {X : Type ℓX} {B : Alg X} where
    idHomo : Homo (λ x → x) B B
    idHomo .op-hom _ _ _ eq = eq

  module _
    {X : Type ℓX} {B : Alg X}
    {Y : Type ℓY} {C : Alg Y}
    {Z : Type ℓZ} {D : Alg Z}
    {f : X → Y} {g : Y → Z}
    (ϕ : Homo f B C) (ψ : Homo g C D)
    where
    _⋆Homo_ : Homo (g ∘ f) B D
    _⋆Homo_ .op-hom op x y eq = ψ .op-hom op (λ z → f (x z)) (f y) (ϕ .op-hom op x y eq)

  module _
    {X : Type ℓX} {B : Alg X}
    {Y : Type ℓY} {C : Alg Y}
    {f : X → Y}
    (ϕ : Homo f B C)
    where
    ⋆HomoIdL : idHomo ⋆Homo ϕ ≡ ϕ
    ⋆HomoIdL = refl
    ⋆HomoIdR : ϕ ⋆Homo idHomo ≡ ϕ
    ⋆HomoIdR = refl

  module _
    {X : Type ℓX} {B : Alg X}
    {Y : Type ℓY} {C : Alg Y}
    {Z : Type ℓZ} {D : Alg Z}
    {W : Type ℓW} {E : Alg W}
    {f : X → Y} {g : Y → Z} {h : Z → W}
    (ϕ : Homo f B C) (ψ : Homo g C D) (γ : Homo h D E)
    where
    ⋆HomoAssoc : ((ϕ ⋆Homo ψ) ⋆Homo γ) ≡ (ϕ ⋆Homo (ψ ⋆Homo γ))
    ⋆HomoAssoc = refl

  module _ {X : Type ℓX} {Y : Type ℓY}
           {B : Alg X} {C : Alg Y}
           {f : X → Y} where
    isPropHomo : isSet Y → isProp (Homo f B C)
    isPropHomo isSetY ϕ ψ i .op-hom op x y eq =
      isSetY _ _ (ϕ .op-hom op x y eq) (ψ .op-hom op x y eq) i

  record Algᴰ {X : Type ℓX} (B : Alg X) (Xᴰ : X → Type ℓᴰ)
    : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓ'' ⊔ℓ ℓv ⊔ℓ ℓX ⊔ℓ ℓᴰ) where
    open Alg B
    open depReasoning Xᴰ public
    field
      ⟨_⟩⟦_⟧opᴰ : ∀ (op : ops) {x : arities op → X} →
        ((x' : arities op) → Xᴰ (x x')) →
        Xᴰ ⟨ op ⟩⟦ x ⟧op
    ⟦_⟧Tmᴰ : {V : Type ℓv} {ρ : V → X} (ρᴰ : (v : V) → Xᴰ (ρ v))
      (M : Tm σ V) → Xᴰ (⟦ ρ ⟧Tm M)
    ⟦_⟧Tmᴰ = TmRecᴰ ⟨_⟩⟦_⟧op Xᴰ ⟨_⟩⟦_⟧opᴰ
    field
      ⟦_⟧eqnᴰ : ∀ (eqn : eqns) {ρ : vars eqn → X}
        (ρᴰ : (v : vars eqn) → Xᴰ (ρ v))
        → ⟦ ρᴰ ⟧Tmᴰ (lhs eqn) P≡[ ⟦ eqn ⟧eqn ρ ] ⟦ ρᴰ ⟧Tmᴰ (rhs eqn)

    private
      ∫op : ∀ (op : ops) → (arities op → Σ X Xᴰ) → Σ X Xᴰ
      ∫op op x = _ , ⟨ op ⟩⟦ snd ∘ x ⟧opᴰ

      ∫Tm≡ : {V : Type ℓv} (ρ : V → Σ X Xᴰ) (M : Tm σ V)
        → TmRec ∫op ρ M ≡ (⟦ fst ∘ ρ ⟧Tm M , ⟦ snd ∘ ρ ⟧Tmᴰ M)
      ∫Tm≡ ρ (var v) = refl
      ∫Tm≡ ρ (node op ts) = cong (∫op op) (funExt (λ a → ∫Tm≡ ρ (ts a)))

    ∫ : Alg (Σ X Xᴰ)
    ∫ .Alg.⟨_⟩⟦_⟧op = ∫op
    ∫ .Alg.⟦_⟧eqn eqn ρ =
      ∫Tm≡ ρ (lhs eqn)
      ∙ ΣPathP (⟦ eqn ⟧eqn (fst ∘ ρ) , ⟦ eqn ⟧eqnᴰ (snd ∘ ρ))
      ∙ sym (∫Tm≡ ρ (rhs eqn))

  module _ {X : Type ℓX} {Y : Type ℓY}
    {B : Alg X} {C : Alg Y} {f : X → Y}
    (ϕ : Homo f B C)
    {Yᴰ : Y → Type ℓᴰ'} (Cᴰ : Algᴰ C Yᴰ)
    (isSetY : isSet Y)
    where
    private
      module B = Alg B
      module C = Alg C
      module ϕ = Homo ϕ
      module Cᴰ where
        open Algᴰ Cᴰ public
        open hSetReasoning (_ , isSetY) Yᴰ using (rectifyOut) public

      opᴰ : ∀ (op : ops) {x : arities op → X}
        → ((a : arities op) → Yᴰ (f (x a)))
        → Yᴰ (f B.⟨ op ⟩⟦ x ⟧op)
      opᴰ op {x} xᴰ = Cᴰ.reind (sym (ϕ.op-hom' op x)) Cᴰ.⟨ op ⟩⟦ xᴰ ⟧opᴰ

      opᴰ-filler : ∀ (op : ops) (x : arities op → X)
        (xᴰ : (a : arities op) → Yᴰ (f (x a)))
        → Path (Σ Y Yᴰ)
            (f B.⟨ op ⟩⟦ x ⟧op , opᴰ op xᴰ)
            (C.⟨ op ⟩⟦ f ∘ x ⟧op , Cᴰ.⟨ op ⟩⟦ xᴰ ⟧opᴰ)
      opᴰ-filler op x xᴰ = sym (Cᴰ.reind-filler (sym (ϕ.op-hom' op x)))

      Tmᴰ : {V : Type ℓv} {ρ : V → X} (ρᴰ : (v : V) → Yᴰ (f (ρ v)))
        (M : Tm σ V) → Yᴰ (f (B.⟦ ρ ⟧Tm M))
      Tmᴰ = TmRecᴰ B.⟨_⟩⟦_⟧op (λ x → Yᴰ (f x)) opᴰ

      Tmᴰ≡ : {V : Type ℓv} {ρ : V → X} (ρᴰ : (v : V) → Yᴰ (f (ρ v)))
        (M : Tm σ V) → Path (Σ Y Yᴰ)
          (f (B.⟦ ρ ⟧Tm M) , Tmᴰ ρᴰ M) (C.⟦ f ∘ ρ ⟧Tm M , Cᴰ.⟦ ρᴰ ⟧Tmᴰ M)
      Tmᴰ≡ ρᴰ (var v) = refl
      Tmᴰ≡ ρᴰ (node op ts) =
        opᴰ-filler op _ _
        ∙ cong (Cᴰ.∫ .Alg.⟨_⟩⟦_⟧op op) (funExt (λ a → Tmᴰ≡ ρᴰ (ts a)))

    reindexAlgᴰ : Algᴰ B (Yᴰ ∘ f)
    reindexAlgᴰ .Algᴰ.⟨_⟩⟦_⟧opᴰ = opᴰ
    reindexAlgᴰ .Algᴰ.⟦_⟧eqnᴰ eqn ρᴰ = Cᴰ.rectifyOut $
      Tmᴰ≡ ρᴰ (lhs eqn)
      ∙ ΣPathP (C.⟦ eqn ⟧eqn _ , Cᴰ.⟦ eqn ⟧eqnᴰ ρᴰ)
      ∙ sym (Tmᴰ≡ ρᴰ (rhs eqn))

    reindexAlgᴰ-op-filler : ∀ (op : ops) (x : arities op → X)
      (xᴰ : (a : arities op) → Yᴰ (f (x a)))
      → Path (Σ Y Yᴰ)
          (f B.⟨ op ⟩⟦ x ⟧op , Algᴰ.⟨_⟩⟦_⟧opᴰ reindexAlgᴰ op xᴰ)
          (C.⟨ op ⟩⟦ f ∘ x ⟧op , Cᴰ.⟨ op ⟩⟦ xᴰ ⟧opᴰ)
    reindexAlgᴰ-op-filler = opᴰ-filler

  record Homoᴰ {X : Type ℓX} {Y : Type ℓY}
    {B : Alg X} {C : Alg Y} {f : X → Y}
    {Xᴰ : X → Type ℓᴰ} {Yᴰ : Y → Type ℓᴰ'}
    (fᴰ : mapOver f Xᴰ Yᴰ)
    (ϕ : Homo f B C)
    (Bᴰ : Algᴰ B Xᴰ) (Cᴰ : Algᴰ C Yᴰ)
    : Type (ℓ ⊔ℓ ℓ' ⊔ℓ ℓX ⊔ℓ ℓᴰ ⊔ℓ ℓᴰ') where
    private
      module B = Alg B
      module ϕ = Homo ϕ
      module Bᴰ = Algᴰ Bᴰ
      module Cᴰ = Algᴰ Cᴰ
    field
      op-homᴰ : ∀ (op : ops) (x : arities op → X)
        (xᴰ : (a : arities op) → Xᴰ (x a))
        (y : X) (yᴰ : Xᴰ y)
        (eq : y ≡ B.⟨ op ⟩⟦ x ⟧op)
        → yᴰ Bᴰ.P≡[ eq ] Bᴰ.⟨ op ⟩⟦ xᴰ ⟧opᴰ
        → fᴰ y yᴰ Cᴰ.P≡[ ϕ.op-hom op x y eq ]
            Cᴰ.⟨ op ⟩⟦ (λ a → fᴰ (x a) (xᴰ a)) ⟧opᴰ

    op-homᴰ' : ∀ (op : ops) (x : arities op → X)
      (xᴰ : (a : arities op) → Xᴰ (x a))
      → fᴰ _ Bᴰ.⟨ op ⟩⟦ xᴰ ⟧opᴰ Cᴰ.P≡[ ϕ.op-hom' op x ]
          Cᴰ.⟨ op ⟩⟦ (λ a → fᴰ (x a) (xᴰ a)) ⟧opᴰ
    op-homᴰ' op x xᴰ = op-homᴰ op x xᴰ _ _ refl refl

    ∫ : Homo (λ (b , bᴰ) → f b , fᴰ b bᴰ) Bᴰ.∫ Cᴰ.∫
    ∫ .Homo.op-hom op x y eq = ΣPathP
      ( ϕ.op-hom op (fst ∘ x) (y .fst) (λ i → eq i .fst)
      , op-homᴰ op (fst ∘ x) (snd ∘ x) (y .fst) (y .snd)
          (λ i → eq i .fst) (λ i → eq i .snd) )

  open Homoᴰ

  isPropHomoᴰ : {X : Type ℓX} {Y : Type ℓY}
    {B : Alg X} {C : Alg Y} {f : X → Y}
    {ϕ : Homo f B C}
    {Xᴰ : X → Type ℓᴰ} {Yᴰ : Y → Type ℓᴰ'}
    {fᴰ : mapOver f Xᴰ Yᴰ} {Bᴰ : Algᴰ B Xᴰ} {Cᴰ : Algᴰ C Yᴰ}
    (isSetYᴰ : ∀ y → isSet (Yᴰ y))
    → isProp (Homoᴰ fᴰ ϕ Bᴰ Cᴰ)
  isPropHomoᴰ isSetYᴰ ϕᴰ ψᴰ i .op-homᴰ op x xᴰ y yᴰ eq eqᴰ =
    isOfHLevelPathP' 1 (isSetYᴰ _) _ _
      (ϕᴰ .op-homᴰ op x xᴰ y yᴰ eq eqᴰ)
      (ψᴰ .op-homᴰ op x xᴰ y yᴰ eq eqᴰ) i

  module _ {X : Type ℓX} {B : Alg X}
    {Xᴰ : X → Type ℓᴰ} {Bᴰ : Algᴰ B Xᴰ} where
    idHomoᴰ : Homoᴰ (λ _ xᴰ → xᴰ) idHomo Bᴰ Bᴰ
    idHomoᴰ .op-homᴰ _ _ _ _ _ _ eqᴰ = eqᴰ

  module _
    {X : Type ℓX} {B : Alg X} {Xᴰ : X → Type ℓᴰ} {Bᴰ : Algᴰ B Xᴰ}
    {Y : Type ℓY} {C : Alg Y} {Yᴰ : Y → Type ℓᴰ'} {Cᴰ : Algᴰ C Yᴰ}
    {Z : Type ℓZ} {D : Alg Z} {Zᴰ : Z → Type ℓᴰ''} {Dᴰ : Algᴰ D Zᴰ}
    {f : X → Y} {g : Y → Z}
    {ϕ : Homo f B C} {ψ : Homo g C D}
    {fᴰ : mapOver f Xᴰ Yᴰ} {gᴰ : mapOver g Yᴰ Zᴰ}
    (ϕᴰ : Homoᴰ fᴰ ϕ Bᴰ Cᴰ) (ψᴰ : Homoᴰ gᴰ ψ Cᴰ Dᴰ)
    where
    _⋆Homoᴰ_ : Homoᴰ (λ x xᴰ → gᴰ (f x) (fᴰ x xᴰ)) (ϕ ⋆Homo ψ) Bᴰ Dᴰ
    _⋆Homoᴰ_ .op-homᴰ op x xᴰ y yᴰ eq eqᴰ =
      ψᴰ .op-homᴰ op (f ∘ x) (λ a → fᴰ (x a) (xᴰ a)) (f y) (fᴰ y yᴰ)
        (ϕ .Homo.op-hom op x y eq)
        (ϕᴰ .op-homᴰ op x xᴰ y yᴰ eq eqᴰ)

  module _
    {X : Type ℓX} {B : Alg X} {Xᴰ : X → Type ℓᴰ} {Bᴰ : Algᴰ B Xᴰ}
    {Y : Type ℓY} {C : Alg Y} {Yᴰ : Y → Type ℓᴰ'} {Cᴰ : Algᴰ C Yᴰ}
    {f : X → Y} {ϕ : Homo f B C} {fᴰ : mapOver f Xᴰ Yᴰ}
    (ϕᴰ : Homoᴰ fᴰ ϕ Bᴰ Cᴰ)
    where
    ⋆HomoᴰIdL : idHomoᴰ ⋆Homoᴰ ϕᴰ ≡ ϕᴰ
    ⋆HomoᴰIdL = refl
    ⋆HomoᴰIdR : ϕᴰ ⋆Homoᴰ idHomoᴰ ≡ ϕᴰ
    ⋆HomoᴰIdR = refl

  module _
    {X : Type ℓX} {B : Alg X} {Xᴰ : X → Type ℓᴰ} {Bᴰ : Algᴰ B Xᴰ}
    {Y : Type ℓY} {C : Alg Y} {Yᴰ : Y → Type ℓᴰ'} {Cᴰ : Algᴰ C Yᴰ}
    {Z : Type ℓZ} {D : Alg Z} {Zᴰ : Z → Type ℓᴰ''} {Dᴰ : Algᴰ D Zᴰ}
    {W : Type ℓW} {E : Alg W} {Wᴰ : W → Type ℓᴰ'''} {Eᴰ : Algᴰ E Wᴰ}
    {f : X → Y} {g : Y → Z} {h : Z → W}
    {ϕ : Homo f B C} {ψ : Homo g C D} {γ : Homo h D E}
    {fᴰ : mapOver f Xᴰ Yᴰ} {gᴰ : mapOver g Yᴰ Zᴰ} {hᴰ : mapOver h Zᴰ Wᴰ}
    (ϕᴰ : Homoᴰ fᴰ ϕ Bᴰ Cᴰ) (ψᴰ : Homoᴰ gᴰ ψ Cᴰ Dᴰ) (γᴰ : Homoᴰ hᴰ γ Dᴰ Eᴰ)
    where
    ⋆HomoᴰAssoc : ((ϕᴰ ⋆Homoᴰ ψᴰ) ⋆Homoᴰ γᴰ) ≡ (ϕᴰ ⋆Homoᴰ (ψᴰ ⋆Homoᴰ γᴰ))
    ⋆HomoᴰAssoc = refl

  Homoⱽ : {X : Type ℓX} {B : Alg X}
    {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X → Type ℓᴰ'}
    (fᴰ : ∀ x → Xᴰ x → Xᴰ' x)
    (Bᴰ : Algᴰ B Xᴰ) (Bᴰ' : Algᴰ B Xᴰ') → Type _
  Homoⱽ fᴰ Bᴰ Bᴰ' = Homoᴰ fᴰ idHomo Bᴰ Bᴰ'
