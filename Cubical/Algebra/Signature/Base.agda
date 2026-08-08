-- Signatures of an algebraic structure and their algebras and
-- displayed algebras, and sections and displayed sections,
-- homomorphisms and displayed homomorphisms.
--
-- We adopt the terminology that "algberas" are simply operations, and
-- that "models" are algebras that satisfy the equations of a
-- Theory. For that notion see Cubical.Algebra.Theory.Base.
--
-- I've attempted for some minimalism with the notions of homomorphism
-- and composition but didn't fully succeed. In the end there are two
-- primitive notions of morphism: a section and a displayed
-- homomorphism, while ordinary homomorphisms are sections of a
-- weakened algebra. I also need three primitive kinds of composition:
-- dependent composition of sections, composition of a section with a
-- homomorphism and composition of displayed homomorphisms. Other than
-- the dependent composition, these satisfy definitional unit and
-- associativity laws.
module Cubical.Algebra.Signature.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv using (compEquiv; equivΠCod)
open import Cubical.Foundations.Equiv.More using (explicitΠEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Path using (Jequiv)
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ ℓᴰ ℓᴰᴰ ℓ' ℓᴰ' ℓᴰᴰ' ℓ'' ℓᴰ'' ℓO ℓA ℓE : Level

record Signature ℓO ℓA : Type (ℓ-max (ℓ-suc ℓO) (ℓ-suc ℓA)) where
  -- I don't see a reason we would need eta equality for Signatures,
  no-eta-equality
  field
    Op : Type ℓO
    Arity : Op → Type ℓA

  -- This on the other hand we definitely want to have nice equality
  AlgebraWithCarrier : (X : Type ℓ) → Type (ℓ-max (ℓ-max ℓO ℓA) ℓ)
  AlgebraWithCarrier X = ∀ (f : Op) → (ρ : Arity f → X) → X

  Algebra : ∀ ℓ → Type _
  Algebra ℓ = Σ[ X ∈ Type ℓ ] AlgebraWithCarrier X

  ⊤Algebra : AlgebraWithCarrier Unit
  ⊤Algebra f ρ = tt

  ⊤*Algebra : AlgebraWithCarrier {ℓ} Unit*
  ⊤*Algebra f ρ = tt*

  module _ (A : Algebra ℓ) where
    -- Twist on the more obvious definition of displayed Algebra: a
    -- "Yoneda expansion" of the more obvious definition
    AlgebraᴰWithCarrier : (A .fst → Type ℓᴰ) → Type _
    AlgebraᴰWithCarrier Xᴰ =
      ∀ (op : Op) (γ : Arity op → A .fst)
      → (γᴰ : (v : Arity op) → Xᴰ (γ v))
      → (op⟨γ⟩ : A .fst) (op∘γ≡op⟨γ⟩ : A .snd op γ ≡ op⟨γ⟩)
      → Xᴰ op⟨γ⟩

    private
      -- Equivalence with the more obvious definition
      AlgebraᴰWithCarrier' : (A .fst → Type ℓᴰ) → Type _
      AlgebraᴰWithCarrier' Xᴰ =
        ∀ (f : Op) (γ : Arity f → A .fst)
          (γᴰ : (v : Arity f) → Xᴰ (γ v))
        → Xᴰ (A .snd f γ)

      AlgebraᴰWithCarrier'≃AlgebraᴰWithCarrier :
        (Xᴰ : A .fst → Type ℓᴰ)
        → AlgebraᴰWithCarrier' Xᴰ ≃ AlgebraᴰWithCarrier Xᴰ
      AlgebraᴰWithCarrier'≃AlgebraᴰWithCarrier Xᴰ =
        equivΠCod λ f → equivΠCod λ γ → equivΠCod λ γᴰ →
          compEquiv
            (Jequiv (λ f⟨γ⟩ _ → Xᴰ f⟨γ⟩))
            explicitΠEquiv

    Algebraᴰ : ∀ ℓᴰ → Type _
    Algebraᴰ ℓᴰ = Σ[ Xᴰ ∈ (A .fst → Type ℓᴰ) ] AlgebraᴰWithCarrier Xᴰ

  ∫Algebra : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ) → Algebra (ℓ-max ℓ ℓᴰ)
  ∫Algebra Aᴰ .fst = Σ[ a ∈ _ ] Aᴰ .fst a
  ∫Algebra {A = A} Aᴰ .snd f γ .fst =
    A .snd f (fst ∘ γ)
  ∫Algebra {A = A} Aᴰ .snd f γ .snd =
    Aᴰ .snd f (fst ∘ γ) (snd ∘ γ) (A .snd f (fst ∘ γ)) refl

  module _ {A : Algebra ℓ} where
    Algebraᴰᴰ : ∀ (Aᴰ : Algebraᴰ A ℓᴰ) ℓᴰᴰ → Type _
    Algebraᴰᴰ Aᴰ ℓᴰᴰ = Algebraᴰ (∫Algebra Aᴰ) ℓᴰᴰ

    -- Is this definition nice enough?
    ∫ᴰAlgebra : {Aᴰ : Algebraᴰ A ℓᴰ} (Aᴰᴰ : Algebraᴰᴰ Aᴰ ℓᴰᴰ) → Algebraᴰ A _
    ∫ᴰAlgebra Aᴰᴰ .fst a = Σ[ aᴰ ∈ _ ] Aᴰᴰ .fst (a , aᴰ)
    ∫ᴰAlgebra {Aᴰ = Aᴰ} Aᴰᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ .fst =
      Aᴰ .snd op γ (λ v → γᴰ v .fst) op⟨γ⟩ op∘γ≡op⟨γ⟩
    ∫ᴰAlgebra {Aᴰ = Aᴰ} Aᴰᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ .snd =
      Aᴰᴰ .snd op _ (snd ∘ γᴰ) _ λ i →
        (op∘γ≡op⟨γ⟩ i)
        , (Aᴰ .snd op γ (fst ∘ γᴰ) _ (λ j → op∘γ≡op⟨γ⟩ (i ∧ j)))

    isHomo : (Aᴰ : Algebraᴰ A ℓᴰ)
      → (f : (a : A .fst) → Aᴰ .fst a)
      → Type _
    isHomo Aᴰ f =
      ∀ (op : Op) (γ : Arity op → A .fst)
        (op⟨γ⟩ : A .fst) (op∘γ≡op⟨γ⟩ : A .snd op γ ≡ op⟨γ⟩)
      → Aᴰ .snd op γ (f ∘ γ) op⟨γ⟩ op∘γ≡op⟨γ⟩ ≡ f op⟨γ⟩

    Section : (Aᴰ : Algebraᴰ A ℓᴰ) → Type _
    Section Aᴰ = Σ[ f ∈ _ ] isHomo Aᴰ f

  wkAlg : (A : Algebra ℓ) (B : Algebra ℓ') → Algebraᴰ A ℓ'
  wkAlg A B .fst _ = B .fst
  wkAlg A B .snd f _ γ _ _ = B .snd f γ

  isHomoSimpl : (A : Algebra ℓ) (B : Algebra ℓ') →
    (A .fst → B .fst) → Type _
  isHomoSimpl A B = isHomo (wkAlg A B)

  Homo : (A : Algebra ℓ) (B : Algebra ℓ') → Type _
  Homo A B = Σ[ f ∈ (A .fst → B .fst) ] isHomoSimpl A B f

  _×Alg_ : (A : Algebra ℓ) (B : Algebra ℓ') → Algebra _
  A ×Alg B = ∫Algebra (wkAlg A B)

  ×intro : {Γ : Algebra ℓ}{A : Algebra ℓ'}{B : Algebra ℓ''}
    → (ϕ : Homo Γ A)
    → (ψ : Homo Γ B)
    → Homo Γ (A ×Alg B)
  ×intro ϕ ψ .fst = λ z → ϕ .fst z , ψ .fst z
  ×intro ϕ ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
    ΣPathP ((ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩) , (ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))

  idHomo : {A : Algebra ℓ} → Homo A A
  idHomo .fst = λ a → a
  idHomo .snd f γ op⟨γ⟩ pf = pf

  module _ {A : Algebra ℓ}{B : Algebra ℓ'} where
    -- Cartesian Lift, pulling back Algebraᴰ structure along a homomorphism
    _*_ : Homo A B → Algebraᴰ B ℓᴰ → Algebraᴰ A ℓᴰ
    (ϕ * Bᴰ) .fst a = Bᴰ .fst (ϕ .fst a)
    (ϕ * Bᴰ) .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      Bᴰ .snd op (λ z → ϕ .fst (γ z)) γᴰ
        (ϕ .fst op⟨γ⟩)
        (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

  ∫intro : {Γ : Algebra ℓ}{A : Algebra ℓ'}{B : Algebraᴰ A ℓᴰ'}
    → (ϕ : Homo Γ A)
    → (ψ : Section (ϕ * B))
    → Homo Γ (∫Algebra B)
  ∫intro ϕ ψ .fst γ .fst = ϕ .fst γ
  ∫intro ϕ ψ .fst γ .snd = ψ .fst γ
  ∫intro ϕ ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .fst =
    -- To make this definition nice...
    ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i
  ∫intro {B = B} ϕ ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .snd =
    -- ...it seems this definition must be nasty
    hfill
      (λ j → λ
        { (i = i0) →
          B .snd op (λ v → ϕ .fst (γ v)) (λ v → ψ .fst (γ v))
            (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i0) refl
        ; (i = i1) → ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ j
        })
      (inS (
        B .snd op (λ v → ϕ .fst (γ v)) (λ v → ψ .fst (γ v))
          (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i)
          (λ j → ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ (i ∧ j))))
      i1

  module _ {A : Algebra ℓ} {Aᴰ : Algebraᴰ A ℓᴰ} where
    Fst : Homo (∫Algebra Aᴰ) A
    Fst .fst = λ z → z .fst
    Fst .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i = op∘γ≡op⟨γ⟩ i .fst

    -- Too nasty to be nice to use unfortunately
    Snd : Section (Fst * Aᴰ)
    Snd .fst = λ a → a .snd
    Snd .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      sym (fromPathP (λ i →
        Aᴰ .snd op (λ v → γ v .fst) (λ v → γ v .snd)
          (op∘γ≡op⟨γ⟩ i .fst)
          (λ j → op∘γ≡op⟨γ⟩ (i ∧ j) .fst)))
      ∙ fromPathP (λ i → op∘γ≡op⟨γ⟩ i .snd)

  module _ {A : Algebra ℓ} {B : Algebra ℓ'} where
    SndSimpl : Homo (A ×Alg B) B
    SndSimpl .fst = λ z → z .snd
    SndSimpl .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i = op∘γ≡op⟨γ⟩ i .snd

  module _ {A : Algebra ℓ}{B : Algebraᴰ A ℓᴰ}{C : Algebraᴰᴰ B ℓᴰᴰ} where
    -- ϕ : (a : A) → B
    -- need (a : A) → Σ[ a ] B a
    _⋆S_ : (ϕ : Section B)(ψ : Section C) → Section (∫intro {B = B} (idHomo {A = A}) ϕ * C)
    (ϕ ⋆S ψ) .fst a = ψ .fst (a , ϕ .fst a)
    (ϕ ⋆S ψ) .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ = ψ .snd _ _ _ _

  module _ {A : Algebra ℓ}{B : Algebra ℓ'} where
    module _ {Bᴰ : Algebraᴰ B ℓᴰ} where
      -- This is so similar this to _⋆S_ but because of the nastiness
      -- of ∫intro it can't be used definitionally.
      _⋆HS_ : (ϕ : Homo A B) → Section Bᴰ → Section (ϕ * Bᴰ)
      (ϕ ⋆HS ψ) .fst a = ψ .fst (ϕ .fst a)
      (ϕ ⋆HS ψ) .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ = ψ .snd _ _ _ _

  module _ {A : Algebra ℓ}{B : Algebra ℓ'}{C : Algebra ℓ''} where
    _⋆H_ : Homo A B → Homo B C → Homo A C
    ϕ ⋆H ψ = _⋆HS_ {Bᴰ = wkAlg _ C} ϕ ψ

  module _ {A : Algebra ℓ}{B : Algebra ℓ'} (ϕ : Homo A B) where
    ⋆HIdR : _⋆H_ {A = A} {B = B} {C = B} ϕ (idHomo {A = B}) ≡ ϕ
    ⋆HIdR = refl

  module _ {A : Algebra ℓ}{Aᴰ : Algebraᴰ A ℓᴰ} where
    ⋆HSIdL : (Ψ : Section Aᴰ) →
      _⋆HS_ {A = A} {B = A} {Bᴰ = Aᴰ} (idHomo {A = A}) Ψ ≡ Ψ
    ⋆HSIdL Ψ = refl

    *Id : (idHomo * Aᴰ) ≡ Aᴰ
    *Id = refl

  module _ {A : Algebra ℓ}{B : Algebra ℓ'}{C : Algebra ℓ''}{Cᴰ : Algebraᴰ C ℓᴰ''} (ϕ : Homo A B)(ψ : Homo B C) where
    ⋆HHSAssoc : (χ : Section Cᴰ)
      → _⋆HS_ {A = A} {B = C} {Bᴰ = Cᴰ}
          (_⋆H_ {A = A} {B = B} {C = C} ϕ ψ) χ
        ≡ _⋆HS_ {A = A} {B = B} {Bᴰ = ψ * Cᴰ}
            ϕ (_⋆HS_ {A = B} {B = C} {Bᴰ = Cᴰ} ψ χ)
    ⋆HHSAssoc χ = refl

    *∘ : ((_⋆H_ {C = C} ϕ ψ) * Cᴰ) ≡ (ϕ * (ψ * Cᴰ))
    *∘ = refl

  -- This definition doesn't work well
  private
    BadHomoᴰ : {A : Algebra ℓ}{B : Algebra ℓ'}
      (ϕ : Homo A B)(Aᴰ : Algebraᴰ A ℓᴰ)(Bᴰ : Algebraᴰ B ℓᴰ')
      → Type _
    BadHomoᴰ ϕ Aᴰ Bᴰ = Section (Fst {Aᴰ = Aᴰ} * (ϕ * Bᴰ))

    module _ {A : Algebra ℓ} {B : Algebra ℓ'} {C : Algebra ℓ''}
      {Aᴰ : Algebraᴰ A ℓᴰ} {Bᴰ : Algebraᴰ B ℓᴰ'} {Cᴰ : Algebraᴰ C ℓᴰ''}
      {ϕ : Homo A B} {ψ : Homo B C} where
      -- because of the nastiness of ∫intro this definition doesn't
      -- work well
      _Bad⋆Hᴰ_ : BadHomoᴰ ϕ Aᴰ Bᴰ → BadHomoᴰ ψ Bᴰ Cᴰ
        → BadHomoᴰ (_⋆H_ {C = C} ϕ ψ) Aᴰ Cᴰ
      (ϕᴰ Bad⋆Hᴰ ψᴰ) .fst a = ψᴰ .fst (ϕ .fst (a .fst) , ϕᴰ .fst a)
      (ϕᴰ Bad⋆Hᴰ ψᴰ) .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        ψᴰ .snd _ _ _
          (∫ϕᴰ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
        where
        ∫ϕᴰ : Homo (∫Algebra Aᴰ) (∫Algebra Bᴰ)
        ∫ϕᴰ =
          ∫intro {Γ = ∫Algebra Aᴰ} {A = B} {B = Bᴰ}
            (_⋆H_ {A = ∫Algebra Aᴰ} {B = A} {C = B}
              (Fst {Aᴰ = Aᴰ}) ϕ)
            ϕᴰ

  module _ {A : Algebra ℓ}{B : Algebra ℓ'}
    (ϕ : Homo A B)(Aᴰ : Algebraᴰ A ℓᴰ)(Bᴰ : Algebraᴰ B ℓᴰ')
    where
    isHomoᴰSimpl : (∀ (a : A .fst)(aᴰ : Aᴰ .fst a) → Bᴰ .fst (ϕ .fst a)) → Type _
    isHomoᴰSimpl fᴰ =
      ∀ (op : Op)(γ : Arity op → A .fst)(γᴰ : ∀ v → Aᴰ .fst (γ v))
        (op⟨γ⟩ : A .fst) (op∘γ≡op⟨γ⟩ : A .snd op γ ≡ op⟨γ⟩)
        (op⟨γᴰ⟩ : Aᴰ .fst (op⟨γ⟩)) (op∘γᴰ≡op⟨γᴰ⟩ : Aᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ ≡ op⟨γᴰ⟩)
      → Bᴰ .snd op (ϕ .fst ∘ γ) (λ v → fᴰ (γ v) (γᴰ v)) (ϕ .fst op⟨γ⟩) (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩) ≡ fᴰ op⟨γ⟩ op⟨γᴰ⟩

    Homoᴰ : Type _
    Homoᴰ = Σ[ fᴰ ∈ _ ] isHomoᴰSimpl fᴰ

  idHomoᴰ : {A : Algebra ℓ}{Aᴰ : Algebraᴰ A ℓᴰ} → Homoᴰ idHomo Aᴰ Aᴰ
  idHomoᴰ .fst = λ a aᴰ → aᴰ
  idHomoᴰ .snd = λ op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ → op∘γᴰ≡op⟨γᴰ⟩

  module _ {A : Algebra ℓ} {B : Algebra ℓ'} {C : Algebra ℓ''}
    {Aᴰ : Algebraᴰ A ℓᴰ} {Bᴰ : Algebraᴰ B ℓᴰ'} {Cᴰ : Algebraᴰ C ℓᴰ''}
    {ϕ : Homo A B} {ψ : Homo B C} where
    -- Can this one be implemented using some kind of displayed section composition? Idk
    _⋆Hᴰ_ : Homoᴰ ϕ Aᴰ Bᴰ → Homoᴰ ψ Bᴰ Cᴰ → Homoᴰ (_⋆H_ {C = C} ϕ ψ) Aᴰ Cᴰ
    (ϕᴰ ⋆Hᴰ ψᴰ) .fst = λ a aᴰ → ψᴰ .fst (ϕ .fst a) (ϕᴰ .fst a aᴰ)
    (ϕᴰ ⋆Hᴰ ψᴰ) .snd = λ op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ →
                          ψᴰ .snd op (λ z → ϕ .fst (γ z)) (λ v → ϕᴰ .fst (γ v) (γᴰ v))
                          (ϕ .fst op⟨γ⟩) (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
                          (ϕᴰ .fst op⟨γ⟩ op⟨γᴰ⟩)
                          (ϕᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩)

  module _ {A : Algebra ℓ} {B : Algebra ℓ'}
    {Aᴰ : Algebraᴰ A ℓᴰ} {Bᴰ : Algebraᴰ B ℓᴰ'}
    {ϕ : Homo A B} where
    ⋆HᴰIdL : (ϕᴰ : Homoᴰ ϕ Aᴰ Bᴰ) →
      _⋆Hᴰ_ {A = A} {B = A} {C = B}
        {Aᴰ = Aᴰ} {Bᴰ = Aᴰ} {Cᴰ = Bᴰ}
        {ϕ = idHomo} {ψ = ϕ} idHomoᴰ ϕᴰ ≡ ϕᴰ
    ⋆HᴰIdL ϕᴰ = refl

    ⋆HᴰIdR : (ϕᴰ : Homoᴰ ϕ Aᴰ Bᴰ) →
      _⋆Hᴰ_ {A = A} {B = B} {C = B}
        {Aᴰ = Aᴰ} {Bᴰ = Bᴰ} {Cᴰ = Bᴰ}
        {ϕ = ϕ} {ψ = idHomo} ϕᴰ idHomoᴰ ≡ ϕᴰ
    ⋆HᴰIdR ϕᴰ = refl

  module _ {A : Algebra ℓ} {B : Algebra ℓ'} {C : Algebra ℓ''}
    {D : Algebra ℓE}
    {Aᴰ : Algebraᴰ A ℓᴰ} {Bᴰ : Algebraᴰ B ℓᴰ'}
    {Cᴰ : Algebraᴰ C ℓᴰ''} {Dᴰ : Algebraᴰ D ℓᴰᴰ}
    {ϕ : Homo A B} {ψ : Homo B C} {χ : Homo C D} where
    ⋆HᴰAssoc : (ϕᴰ : Homoᴰ ϕ Aᴰ Bᴰ) (ψᴰ : Homoᴰ ψ Bᴰ Cᴰ)
      (χᴰ : Homoᴰ χ Cᴰ Dᴰ) →
      _⋆Hᴰ_ {A = A} {B = C} {C = D}
        {Aᴰ = Aᴰ} {Bᴰ = Cᴰ} {Cᴰ = Dᴰ}
        {ϕ = _⋆H_ {C = C} ϕ ψ} {ψ = χ}
        (_⋆Hᴰ_ {A = A} {B = B} {C = C}
          {Aᴰ = Aᴰ} {Bᴰ = Bᴰ} {Cᴰ = Cᴰ} ϕᴰ ψᴰ)
        χᴰ
      ≡ _⋆Hᴰ_ {A = A} {B = B} {C = D}
          {Aᴰ = Aᴰ} {Bᴰ = Bᴰ} {Cᴰ = Dᴰ}
          {ϕ = ϕ} {ψ = _⋆H_ {C = D} ψ χ}
          ϕᴰ
          (_⋆Hᴰ_ {A = B} {B = C} {C = D}
            {Aᴰ = Bᴰ} {Bᴰ = Cᴰ} {Cᴰ = Dᴰ} ψᴰ χᴰ)
    ⋆HᴰAssoc ϕᴰ ψᴰ χᴰ = refl

  -- Path Algebra
  module _ (A : Algebra ℓ) where
    PathAlg : Algebraᴰ (A ×Alg A) ℓ
    PathAlg .fst (a , a') = a ≡ a'
    PathAlg .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      sym (cong fst op∘γ≡op⟨γ⟩)
      ∙ cong (A .snd op) (funExt γᴰ)
      ∙ cong snd op∘γ≡op⟨γ⟩

    -- TODO: PathAlg Reflection and derive the uniqueness from the eliminator below
    PathAlgReflection : {Γ : Algebra ℓ'} (ϕ ψ : Homo Γ A)
      → Section (×intro {A = A}{B = A} ϕ ψ * PathAlg)
      → ϕ .fst ≡ ψ .fst
    PathAlgReflection ϕ ψ ϕ≡ψ i γ = ϕ≡ψ .fst γ i

  -- Free Algebras
  data |FreeAlgebra| (X : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓA ℓO)) where
    var : X → |FreeAlgebra| X
    app : (op : Op) → (Arity op → |FreeAlgebra| X) → |FreeAlgebra| X

  FreeAlgebra : (X : Type ℓ) → Algebra (ℓ-max ℓ (ℓ-max ℓA ℓO))
  FreeAlgebra X = (|FreeAlgebra| X) , app

  private
    open import Cubical.Data.Empty
    open import Cubical.Data.Sum
    open import Cubical.Data.W.Indexed
    FreeShape : Type ℓ → Type (ℓ-max ℓ ℓO)
    FreeShape X = X ⊎ Op

    FreePosition : {X : Type ℓ} → FreeShape X → Type ℓA
    FreePosition (inl _) = Lift ℓA ⊥
    FreePosition (inr op) = Arity op

    FreeIW : Type ℓ → Type (ℓ-max ℓ (ℓ-max ℓA ℓO))
    FreeIW X = IW (λ (_ : Unit) → FreeShape X)
      (λ _ → FreePosition) (λ _ _ _ → tt) tt

    FreeAlgebra→IW : {X : Type ℓ} → |FreeAlgebra| X → FreeIW X
    FreeAlgebra→IW (var x) = node (inl x) λ { (lift ()) }
    FreeAlgebra→IW (app op γ) =
      node (inr op) (λ v → FreeAlgebra→IW (γ v))

    IW→FreeAlgebra : {X : Type ℓ} → FreeIW X → |FreeAlgebra| X
    IW→FreeAlgebra (node (inl x) γ) = var x
    IW→FreeAlgebra (node (inr op) γ) =
      app op (λ v → IW→FreeAlgebra (γ v))

    IW→FreeAlgebra→IW : {X : Type ℓ} (t : |FreeAlgebra| X)
      → IW→FreeAlgebra (FreeAlgebra→IW t) ≡ t
    IW→FreeAlgebra→IW (var x) = refl
    IW→FreeAlgebra→IW (app op γ) =
      cong (app op) (funExt λ v → IW→FreeAlgebra→IW (γ v))

  isSetFreeAlgebra : {X : Type ℓ} → (isSetOp : isSet Op) → isSet X → isSet (|FreeAlgebra| X)
  isSetFreeAlgebra isSetOp isSetX =
    isSetRetract FreeAlgebra→IW IW→FreeAlgebra IW→FreeAlgebra→IW
      (isOfHLevelSuc-IW 1
        (λ _ → isSet⊎ isSetX isSetOp) tt)

  module _ {X : Type ℓ} (Aᴰ : Algebraᴰ (FreeAlgebra X) ℓ') (ıᴰ : (x : X) → Aᴰ .fst (var x)) where
    |elimFA| : ∀ (t : |FreeAlgebra| X) → Aᴰ .fst t
    -- β reduction is definitional
    |elimFA| (var x) = ıᴰ x
    |elimFA| (app op γ) = Aᴰ .snd op γ (|elimFA| ∘ γ) (app op γ) refl

    elimFA : Section Aᴰ
    elimFA .fst = |elimFA|
    elimFA .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      J
        (λ op⟨γ⟩ op∘γ≡op⟨γ⟩ →
          Aᴰ .snd op γ (|elimFA| ∘ γ) op⟨γ⟩ op∘γ≡op⟨γ⟩
            ≡ |elimFA| op⟨γ⟩)
        refl
        op∘γ≡op⟨γ⟩

  module _ {X : Type ℓ} (A : Algebra ℓ')  where
    recFA : (ı : X → A .fst) → Homo (FreeAlgebra X) A
    recFA ı = elimFA (wkAlg (FreeAlgebra X) A) ı

    recFA-uniq : ∀ (ϕ : Homo (FreeAlgebra X) A) → ϕ .fst ≡ recFA (ϕ .fst ∘ var) .fst
    recFA-uniq ϕ = PathAlgReflection A ϕ (recFA (ϕ .fst ∘ var))
      (elimFA (×intro {A = A}{B = A} ϕ (recFA (ϕ .fst ∘ var)) * PathAlg A) λ _ → refl)

  -- Displayed structure
  -- Vertical Products
  module _ {A : Algebra ℓ}(B : Algebraᴰ A ℓᴰ)(B' : Algebraᴰ A ℓᴰ') where
    _×ⱽ_ : Algebraᴰ A (ℓ-max ℓᴰ ℓᴰ')
    _×ⱽ_ .fst = λ a → B .fst a × B' .fst a
    _×ⱽ_ .snd = λ op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ →
                   B .snd op γ (λ v → γᴰ v .fst) op⟨γ⟩ op∘γ≡op⟨γ⟩ ,
                   B' .snd op γ (λ v → γᴰ v .snd) op⟨γ⟩ op∘γ≡op⟨γ⟩
  module _ {A : Algebra ℓ} where
    ⊤*ⱽ : Algebraᴰ A ℓᴰ
    ⊤*ⱽ .fst a = Unit*
    ⊤*ⱽ .snd = λ op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ → tt*

  module _ {X : Type ℓ}(Xᴰ : X → Type ℓᴰ) where
    data |FreeAlgebraᴰ| : |FreeAlgebra| X → Type (ℓ-max ℓ (ℓ-max ℓA (ℓ-max ℓO ℓᴰ))) where
      var : ∀ {x} (xᴰ : Xᴰ x) → |FreeAlgebraᴰ| (var x)
      app : ∀ op γ
        (γᴰ : (v : Arity op) → |FreeAlgebraᴰ| (γ v))
        op⟨γ⟩
        (op∘γ≡op⟨γ⟩ : FreeAlgebra X .snd op γ ≡ op⟨γ⟩)
        → |FreeAlgebraᴰ| op⟨γ⟩
    -- TODO: prove isSet

    FreeAlgebraᴰ : Algebraᴰ (FreeAlgebra X) (ℓ-max (ℓ-max (ℓ-max ℓO ℓA) ℓ) ℓᴰ)
    FreeAlgebraᴰ .fst = |FreeAlgebraᴰ|
    FreeAlgebraᴰ .snd = app

    module _ (isSetOp : isSet Op) (isSetX : isSet X)
      (isSetXᴰ : ∀ x → isSet (Xᴰ x)) where
      private
        isSetFree : isSet (|FreeAlgebra| X)
        isSetFree = isSetFreeAlgebra isSetOp isSetX

        FreeShapeᴰ : |FreeAlgebra| X → Type _
        FreeShapeᴰ t =
          (Σ[ x ∈ X ] Xᴰ x × (var x ≡ t))
          ⊎ (Σ[ op ∈ Op ] Σ[ γ ∈ (Arity op → |FreeAlgebra| X) ] app op γ ≡ t)

        FreePositionᴰ : ∀ {t} → FreeShapeᴰ t → Type ℓA
        FreePositionᴰ (inl _) = Lift ℓA ⊥
        FreePositionᴰ (inr (op , _)) = Arity op

        FreeIndexᴰ : ∀ t (s : FreeShapeᴰ t) → FreePositionᴰ s → |FreeAlgebra| X
        FreeIndexᴰ t (inl _) (lift ())
        FreeIndexᴰ t (inr (op , γ , _)) v = γ v

        FreeIWᴰ : |FreeAlgebra| X → Type _
        FreeIWᴰ = IW FreeShapeᴰ (λ _ → FreePositionᴰ) FreeIndexᴰ

        FreeAlgebraᴰ→IW : ∀ {t} → |FreeAlgebraᴰ| t → FreeIWᴰ t
        FreeAlgebraᴰ→IW (var {x = x} xᴰ) =
          node (inl (x , xᴰ , refl)) λ { (lift ()) }
        FreeAlgebraᴰ→IW (app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
          node (inr (op , γ , op∘γ≡op⟨γ⟩))
            (λ v → FreeAlgebraᴰ→IW (γᴰ v))

        IW→FreeAlgebraᴰ : ∀ {t} → FreeIWᴰ t → |FreeAlgebraᴰ| t
        IW→FreeAlgebraᴰ (node (inl (x , xᴰ , p)) γ) =
          subst |FreeAlgebraᴰ| p (var xᴰ)
        IW→FreeAlgebraᴰ (node (inr (op , γ , p)) γᴰ) =
          app op γ (λ v → IW→FreeAlgebraᴰ (γᴰ v)) _ p

        IW→FreeAlgebraᴰ→IW : ∀ {t} (tᴰ : |FreeAlgebraᴰ| t)
          → IW→FreeAlgebraᴰ (FreeAlgebraᴰ→IW tᴰ) ≡ tᴰ
        IW→FreeAlgebraᴰ→IW (var xᴰ) =
          substRefl {B = |FreeAlgebraᴰ|} (|FreeAlgebraᴰ|.var xᴰ)
        IW→FreeAlgebraᴰ→IW (app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
          cong
            (λ γᴰ' → app op γ γᴰ' op⟨γ⟩ op∘γ≡op⟨γ⟩)
            (funExt λ v → IW→FreeAlgebraᴰ→IW (γᴰ v))

        isSetFreeShapeᴰ : ∀ t → isSet (FreeShapeᴰ t)
        isSetFreeShapeᴰ t = isSet⊎
          (isSetΣ isSetX λ x →
            isSet× (isSetXᴰ x) (isProp→isSet (isSetFree _ _)))
          (isSetΣ isSetOp λ op →
            isSetΣ (isSetΠ λ _ → isSetFree) λ γ →
              isProp→isSet (isSetFree _ _))

      isSetFreeAlgebraᴰ : ∀ t → isSet (|FreeAlgebraᴰ| t)
      isSetFreeAlgebraᴰ t =
        isSetRetract FreeAlgebraᴰ→IW IW→FreeAlgebraᴰ IW→FreeAlgebraᴰ→IW
          (isOfHLevelSuc-IW 1 isSetFreeShapeᴰ t)

    module _ {A : Algebra ℓ'} (ϕ : Homo (FreeAlgebra X) A)
      (Aᴰ : Algebraᴰ A ℓᴰ')
      (ıᴰ : ∀ x → Xᴰ x → Aᴰ .fst (ϕ .fst (var x))) where
      |recFAᴰ| : ∀ {t} → |FreeAlgebraᴰ| t → Aᴰ .fst (ϕ .fst t)
      |recFAᴰ| (var {x = x} xᴰ) = ıᴰ x xᴰ
      |recFAᴰ| (app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
        Aᴰ .snd op (ϕ .fst ∘ γ) (λ v → |recFAᴰ| (γᴰ v))
          (ϕ .fst op⟨γ⟩)
          (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

      recFAᴰ : Homoᴰ ϕ FreeAlgebraᴰ Aᴰ
      recFAᴰ .fst _ = |recFAᴰ|
      recFAᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
        J
          (λ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ →
            Aᴰ .snd op (ϕ .fst ∘ γ) (λ v → |recFAᴰ| (γᴰ v))
              (ϕ .fst op⟨γ⟩)
              (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
              ≡ |recFAᴰ| op⟨γᴰ⟩)
          refl
          op∘γᴰ≡op⟨γᴰ⟩

    module _ {A : Algebra ℓ'} (ϕ : Homo (FreeAlgebra X) A)
      (Aᴰ : Algebraᴰ A ℓᴰ')
      (ϕᴰ : Homoᴰ ϕ FreeAlgebraᴰ Aᴰ) where
      private
        ıᴰ : ∀ x → Xᴰ x → Aᴰ .fst (ϕ .fst (var x))
        ıᴰ x xᴰ = ϕᴰ .fst (var x) (var xᴰ)

        |recFAᴰ|-η : ∀ {t} (tᴰ : |FreeAlgebraᴰ| t)
          → ϕᴰ .fst t tᴰ ≡ |recFAᴰ| ϕ Aᴰ ıᴰ tᴰ
        |recFAᴰ|-η (var xᴰ) = refl
        |recFAᴰ|-η (app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
          sym (ϕᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
            (app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) refl)
          ∙ cong
              (λ γᴰ' →
                Aᴰ .snd op (ϕ .fst ∘ γ) γᴰ'
                  (ϕ .fst op⟨γ⟩)
                  (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))
              (funExt λ v → |recFAᴰ|-η (γᴰ v))

      recFAᴰ-η : ϕᴰ .fst ≡ recFAᴰ ϕ Aᴰ ıᴰ .fst
      recFAᴰ-η = funExt λ t → funExt λ tᴰ → |recFAᴰ|-η tᴰ
