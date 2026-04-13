-- A reflexive graph is a type equipped with a family

module Cubical.ReflexiveGraph.Base where

open import Cubical.Foundations.Prelude

private
  variable ℓ ℓ' : Level

record ReflexiveGraphOn (X : Type ℓ) ℓ' : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  no-eta-equality
  field
    _≈_ : X → X → Type ℓ'
    rfl : ∀ x → x ≈ x

record ReflexiveGraph ℓ ℓ' : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  no-eta-equality
  field
    X : Type ℓ
    _≈_ : X → X → Type ℓ'
    rfl : ∀ x → x ≈ x

  singlX : X → Type _
  singlX x = Σ[ y ∈ X ] x ≈ y

isUnivalentRG : ReflexiveGraph ℓ ℓ' → Type _
isUnivalentRG 𝓧 = ∀ x → isProp (singlX x) where
  open ReflexiveGraph 𝓧

record ReflexiveGraphᴰ (𝓧 : ReflexiveGraph ℓ ℓ') ℓ'' ℓ''' : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where
  no-eta-equality
  open ReflexiveGraph 𝓧
  field
    Xᴰ : X → Type ℓ''
    _≈[_]_ : ∀ {x y} (xᴰ : Xᴰ x) (p : x ≈ y) (yᴰ : Xᴰ y) → Type ℓ'''
    rflᴰ : ∀ {x} (xᴰ : Xᴰ x) → xᴰ ≈[ rfl x ] xᴰ

  ∫ : ReflexiveGraph (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')
  ∫ .ReflexiveGraph.X = Σ X Xᴰ
  ∫ .ReflexiveGraph._≈_ (x , xᴰ) (y , yᴰ) = Σ (x ≈ y) (xᴰ ≈[_] yᴰ)
  ∫ .ReflexiveGraph.rfl (x , xᴰ) = rfl x , rflᴰ xᴰ

-- unbiased dependent lens
record uLens (𝓧 : ReflexiveGraph ℓ ℓ') ℓ'' ℓ''' : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where
  no-eta-equality
  open ReflexiveGraph 𝓧
  field
    𝓧ᴰ : ∀ {x y} (p : x ≈ y) → ReflexiveGraph ℓ'' ℓ'''
  module Xᴰ {x y} {p : x ≈ y} = ReflexiveGraph (𝓧ᴰ p)
  field
    lext : ∀ {x y} (p : x ≈ y) → Xᴰ.X {p = rfl x} → Xᴰ.X {p = p}
    rext : ∀ {x y} (p : x ≈ y) → Xᴰ.X {p = rfl y} → Xᴰ.X {p = p}
    extRx : ∀ {x} (u : Xᴰ.X {p = rfl x}) → Xᴰ._≈_ {p = rfl x} (lext _ u) (rext _ u)
    rextRx : ∀ {x} (u : Xᴰ.X {p = rfl x}) → Xᴰ._≈_ {p = rfl x} u (rext (rfl x) u)

  asRGᴰ : ReflexiveGraphᴰ 𝓧 ℓ'' ℓ'''
  asRGᴰ .ReflexiveGraphᴰ.Xᴰ x = Xᴰ.X {p = rfl x}
  asRGᴰ .ReflexiveGraphᴰ._≈[_]_ xᴰ p yᴰ = Xᴰ._≈_ {p = p} (lext p xᴰ) (rext p yᴰ)
  asRGᴰ .ReflexiveGraphᴰ.rflᴰ xᴰ = extRx xᴰ

  open ReflexiveGraphᴰ asRGᴰ public

record pushLens (𝓧 : ReflexiveGraph ℓ ℓ') ℓ'' ℓ''' : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where
  no-eta-equality
  open ReflexiveGraph 𝓧
  field
    𝓧ᴰ : (x : X) → ReflexiveGraph ℓ'' ℓ'''
  module 𝓧ᴰ {x} = ReflexiveGraph (𝓧ᴰ x)
  field
    push : ∀ {x y} (p : x ≈ y) → (𝓧ᴰ.X {x = x}) → 𝓧ᴰ.X {x = y}
    push-rfl : ∀ {x} (xᴰ : 𝓧ᴰ.X) → push (rfl x) xᴰ 𝓧ᴰ.≈ xᴰ

  asULens : uLens 𝓧 ℓ'' ℓ'''
  asULens .uLens.𝓧ᴰ {x} {y} p = 𝓧ᴰ y
  asULens .uLens.lext = push
  asULens .uLens.rext = λ p z → z
  asULens .uLens.extRx = push-rfl
  asULens .uLens.rextRx = 𝓧ᴰ.rfl

record pullLens (𝓧 : ReflexiveGraph ℓ ℓ') ℓ'' ℓ''' : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓ'''))) where
  no-eta-equality
  open ReflexiveGraph 𝓧
  field
    𝓧ᴰ : (x : X) → ReflexiveGraph ℓ'' ℓ'''
  module 𝓧ᴰ {x} = ReflexiveGraph (𝓧ᴰ x)
  field
    pull : ∀ {x y} (p : x ≈ y) → 𝓧ᴰ.X {x = y} → (𝓧ᴰ.X {x = x})
    pull-rfl : ∀ {x} (xᴰ : 𝓧ᴰ.X) → xᴰ 𝓧ᴰ.≈ pull (rfl x) xᴰ

  asULens : uLens 𝓧 ℓ'' ℓ'''
  asULens .uLens.𝓧ᴰ {x} {y} p = 𝓧ᴰ x
  asULens .uLens.lext = λ p z → z
  asULens .uLens.rext = pull
  asULens .uLens.extRx = pull-rfl
  asULens .uLens.rextRx = pull-rfl
