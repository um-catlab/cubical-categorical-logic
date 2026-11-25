{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
  using (_×Psh_)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
  hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.ChangeOfObjects
open import Cubical.Categories.Displayed.Instances.Codomain.Base

module _ (ℓ : Level) where
  private
    module SETᴰ = Categoryᴰ (SETᴰ ℓ ℓ)

    El : {X : hSet ℓ} → SETᴰ.ob[ X ] → ⟨ X ⟩ → Type ℓ
    El P x = ⟨ P x ⟩

  ∫El : {X : hSet ℓ} → SETᴰ.ob[ X ] → hSet ℓ
  ∫El {X} P = (Σ ⟨ X ⟩ (El P)) , isSetΣ (X .snd) λ x → P x .snd
  open Functorᴰ

  Σcmp : Functorⱽ (SETᴰ ℓ ℓ) (Codomain (SET ℓ))
  Σcmp .F-obᴰ P = ∫El P , fst
  Σcmp .F-homᴰ {f = h} φ .fst z = h (z .fst) , φ (z .fst) (z .snd)
  Σcmp .F-homᴰ φ .snd = refl
  Σcmp .F-idᴰ = Codomain≡ (SET ℓ) refl refl
  Σcmp .F-seqᴰ φ ψ = Codomain≡ (SET ℓ) refl refl

  SETCod : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
  SETCod = ChangeOfObjectsᴰ (Codomain (SET ℓ)) (Σcmp .F-obᴰ)

  SETCodReind : ChosenReind SETCod
  SETCodReind =
    ChangeOfObjectsReind (Codomain (SET ℓ)) (Σcmp .F-obᴰ) (CodomainReind _)

  private
    module SETCod = Categoryᴰ SETCod

  Fib : {Y : hSet ℓ} → SETᴰ.ob[ Y ] → ⟨ Y ⟩ → Type ℓ
  Fib {Y} Q y = Σ[ w ∈ Σ ⟨ Y ⟩ (El Q) ] (w .fst ≡ y)

  isSetFib : {Y : hSet ℓ} (Q : SETᴰ.ob[ Y ]) (y : ⟨ Y ⟩) → isSet (Fib Q y)
  isSetFib {Y} Q y =
    isSetΣ (∫El Q .snd) λ w → isProp→isSet (Y .snd (w .fst) y)

  Fibᴰ : {Y : hSet ℓ} → SETᴰ.ob[ Y ] → SETᴰ.ob[ Y ]
  Fibᴰ Q y = Fib Q y , isSetFib Q y

  Pointwise : {X Y : hSet ℓ} (h : ⟨ X ⟩ → ⟨ Y ⟩) (P : SETᴰ.ob[ X ])
    (Q : SETᴰ.ob[ Y ]) → Type ℓ
  Pointwise {X} {Y} h P Q = (z : Σ ⟨ X ⟩ (El P)) → Fib Q (h (z .fst))

  module _ {X Y : hSet ℓ} {h : ⟨ X ⟩ → ⟨ Y ⟩} {P : SETᴰ.ob[ X ]}
    {Q : SETᴰ.ob[ Y ]} where
    pt : SETCod.Hom[ h ][ P , Q ] → Pointwise h P Q
    pt φ z .fst = φ .fst z
    pt φ z .snd i = φ .snd i z

    mk : Pointwise h P Q → SETCod.Hom[ h ][ P , Q ]
    mk g .fst z = g z .fst
    mk g .snd i z = g z .snd i

  module _ {X : hSet ℓ} where
    FibPathP : {x x' : ⟨ X ⟩} (r : x ≡ x') {a : SETᴰ.ob[ X ]}
      {u : Fib a x} {u' : Fib a x'} → u .fst ≡ u' .fst
      → PathP (λ i → Fib a (r i)) u u'
    FibPathP r {u = u} {u'} p i .fst = p i
    FibPathP r {u = u} {u'} p i .snd =
      isProp→PathP (λ i → X .snd (p i .fst) (r i)) (u .snd) (u' .snd) i

  _ : {X Y Z : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {g : ⟨ Y ⟩ → ⟨ Z ⟩}
    {P : SETᴰ.ob[ X ]} {Q : SETᴰ.ob[ Y ]} {R : SETᴰ.ob[ Z ]}
    (φ : SETCod.Hom[ f ][ P , Q ]) (ψ : SETCod.Hom[ g ][ Q , R ]) (z : _)
    → (φ SETCod.⋆ᴰ ψ) .fst z ≡ ψ .fst (φ .fst z)
  _ = λ φ ψ z → refl

  _ : {X Y : hSet ℓ} {f g : ⟨ X ⟩ → ⟨ Y ⟩} {P : SETᴰ.ob[ X ]}
    {Q : SETᴰ.ob[ Y ]} (e : f ≡ g) (φ : SETCod.Hom[ f ][ P , Q ])
    → ChosenReind.reind⟨_⟩ SETCodReind e φ .fst ≡ φ .fst
  _ = λ e φ → refl

instance
  SETCodReindInst : ∀ {ℓ} → ChosenReind (SETCod ℓ)
  SETCodReindInst = SETCodReind _

module _ {ℓ : Level} where
  private
    module SETᴰ = Categoryᴰ (SETᴰ ℓ ℓ)
    module SETCod = Categoryᴰ (SETCod ℓ)
    module F = Fibers (SETCod ℓ)
    module F^op = Fibers (SETCod ℓ ^opᴰ)

  reind-fst : ∀ {X Y : hSet ℓ} {f g : ⟨ X ⟩ → ⟨ Y ⟩}
    {P : SETᴰ.ob[ X ]} {Q : SETᴰ.ob[ Y ]} (e : f ≡ g)
    (φ : SETCod.Hom[ f ][ P , Q ])
    → F.reind {aᴰ = P} {bᴰ = Q} e φ .fst ≡ φ .fst
  reind-fst {P = P} {Q} e φ =
    cong (λ z → z .snd .fst) (sym (F.reind-filler {aᴰ = P} {bᴰ = Q} e))

  reind^op-fst : ∀ {X Y : hSet ℓ} {f g : ⟨ X ⟩ → ⟨ Y ⟩}
    {P : SETᴰ.ob[ Y ]} {Q : SETᴰ.ob[ X ]} (e : f ≡ g)
    (φ : SETCod.Hom[ f ][ Q , P ])
    → F^op.reind {aᴰ = P} {bᴰ = Q} e φ .fst ≡ φ .fst
  reind^op-fst {P = P} {Q} e φ =
    cong (λ z → z .snd .fst) (sym (F^op.reind-filler {aᴰ = P} {bᴰ = Q} e))

  module _ {X : hSet ℓ} where
    𝟙Cod : SETᴰ.ob[ X ]
    𝟙Cod x = Unit* , isSetUnit*

    𝟘Cod : SETᴰ.ob[ X ]
    𝟘Cod x = ⊥* , isProp→isSet isProp⊥*

    infixr 6 _×Cod_ _+Cod_

    _×Cod_ : SETᴰ.ob[ X ] → SETᴰ.ob[ X ] → SETᴰ.ob[ X ]
    (a ×Cod b) x = (Fib ℓ a x × Fib ℓ b x)
      , isSet× (isSetFib ℓ a x) (isSetFib ℓ b x)

    _+Cod_ : SETᴰ.ob[ X ] → SETᴰ.ob[ X ] → SETᴰ.ob[ X ]
    (a +Cod b) x = (⟨ a x ⟩ ⊎ ⟨ b x ⟩) , isSet⊎ (a x .snd) (b x .snd)

  module _ {X Y : hSet ℓ} (f : ⟨ X ⟩ → ⟨ Y ⟩) where
    Pull : SETᴰ.ob[ Y ] → SETᴰ.ob[ X ]
    Pull Q x = Fibᴰ ℓ Q (f x)

    Push : SETᴰ.ob[ X ] → SETᴰ.ob[ Y ]
    Push P y =
      (Σ[ z ∈ ⟨ ∫El ℓ P ⟩ ] (f (z .fst) ≡ y))
      , isSetΣ (∫El ℓ P .snd) λ z → isProp→isSet (Y .snd _ _)

    pullπ : (Q : SETᴰ.ob[ Y ]) → SETCod.Hom[ f ][ Pull Q , Q ]
    pullπ Q = mk ℓ λ z → z .snd

    pushσ : (P : SETᴰ.ob[ X ]) → SETCod.Hom[ f ][ P , Push P ]
    pushσ P .fst z = f (z .fst) , z , refl
    pushσ P .snd = refl

  module _ {X W : hSet ℓ} {k : ⟨ W ⟩ → ⟨ X ⟩} {c : SETᴰ.ob[ W ]} where
    !Cod : SETCod.Hom[ k ][ c , 𝟙Cod {X} ]
    !Cod = mk ℓ λ z → (k (z .fst) , tt*) , refl

    !Cod-η : (hᴰ : SETCod.Hom[ k ][ c , 𝟙Cod {X} ]) → !Cod ≡ hᴰ
    !Cod-η hᴰ = Codomain≡ (SET ℓ) refl λ i z → hᴰ .snd (~ i) z , tt*

    module _ (a b : SETᴰ.ob[ X ]) where
      ×Cod-intro : SETCod.Hom[ k ][ c , a ] × SETCod.Hom[ k ][ c , b ]
        → SETCod.Hom[ k ][ c , a ×Cod b ]
      ×Cod-intro g = mk ℓ λ z →
        (k (z .fst) , pt ℓ (g .fst) z , pt ℓ (g .snd) z) , refl

  module _ {X W : hSet ℓ} {k : ⟨ X ⟩ → ⟨ W ⟩} {c : SETᴰ.ob[ W ]} where
    ¡Cod : SETCod.Hom[ k ][ 𝟘Cod {X} , c ]
    ¡Cod .fst (x , ())
    ¡Cod .snd i (x , ())

    ¡Cod-η : (hᴰ : SETCod.Hom[ k ][ 𝟘Cod {X} , c ]) → ¡Cod ≡ hᴰ
    ¡Cod-η hᴰ = Codomain≡ (SET ℓ) refl (funExt λ { (x , ()) })

    module _ (a b : SETᴰ.ob[ X ]) where
      +Cod-case : (⟨ ∫El ℓ a ⟩ → ⟨ ∫El ℓ c ⟩) → (⟨ ∫El ℓ b ⟩ → ⟨ ∫El ℓ c ⟩)
        → ⟨ ∫El ℓ (a +Cod b) ⟩ → ⟨ ∫El ℓ c ⟩
      +Cod-case F G (x , inl p) = F (x , p)
      +Cod-case F G (x , inr q) = G (x , q)

      +Cod-elim : SETCod.Hom[ k ][ a , c ] × SETCod.Hom[ k ][ b , c ]
        → SETCod.Hom[ k ][ a +Cod b , c ]
      +Cod-elim g .fst = +Cod-case (g .fst .fst) (g .snd .fst)
      +Cod-elim g .snd i (x , inl p) = g .fst .snd i (x , p)
      +Cod-elim g .snd i (x , inr q) = g .snd .snd i (x , q)

  module _ {X : hSet ℓ} (a b : SETᴰ.ob[ X ]) where
    ×Codπ₁ : SETCod.Hom[ (λ x → x) ][ a ×Cod b , a ]
    ×Codπ₁ = mk ℓ λ z → z .snd .fst

    ×Codπ₂ : SETCod.Hom[ (λ x → x) ][ a ×Cod b , b ]
    ×Codπ₂ = mk ℓ λ z → z .snd .snd

    +Codσ₁ : SETCod.Hom[ (λ x → x) ][ a , a +Cod b ]
    +Codσ₁ = mk ℓ λ z → (z .fst , inl (z .snd)) , refl

    +Codσ₂ : SETCod.Hom[ (λ x → x) ][ b , a +Cod b ]
    +Codσ₂ = mk ℓ λ z → (z .fst , inr (z .snd)) , refl

  open UniversalElementⱽ'

  TerminalⱽSETCod : (X : hSet ℓ) → UniversalElementⱽ' (SETCod ℓ) X UnitPshᴰ
  TerminalⱽSETCod X .vertexⱽ = 𝟙Cod
  TerminalⱽSETCod X .elementⱽ = tt
  TerminalⱽSETCod X .universalⱽ _ .fst _ = !Cod
  TerminalⱽSETCod X .universalⱽ _ .snd .fst _ = refl
  TerminalⱽSETCod X .universalⱽ _ .snd .snd = !Cod-η

  TerminalsⱽSETCod : Terminalsⱽ (SETCod ℓ)
  TerminalsⱽSETCod X = REPRⱽ (TerminalⱽSETCod X)

  InitialⱽSETCod : (X : hSet ℓ) → UniversalElementⱽ' (SETCod ℓ ^opᴰ) X UnitPshᴰ
  InitialⱽSETCod X .vertexⱽ = 𝟘Cod
  InitialⱽSETCod X .elementⱽ = tt
  InitialⱽSETCod X .universalⱽ _ .fst _ = ¡Cod
  InitialⱽSETCod X .universalⱽ _ .snd .fst _ = refl
  InitialⱽSETCod X .universalⱽ _ .snd .snd = ¡Cod-η

  InitialsⱽSETCod : Initialsⱽ (SETCod ℓ)
  InitialsⱽSETCod X = REPRⱽ (InitialⱽSETCod X)

  BinProductⱽSETCod : {X : hSet ℓ} (a b : SETᴰ.ob[ X ])
    → UniversalElementⱽ' (SETCod ℓ) X (BinProductⱽSpec (SETCod ℓ) a b)
  BinProductⱽSETCod a b .vertexⱽ = a ×Cod b
  BinProductⱽSETCod a b .elementⱽ = ×Codπ₁ a b , ×Codπ₂ a b
  BinProductⱽSETCod a b .universalⱽ _ .fst = ×Cod-intro a b
  BinProductⱽSETCod a b .universalⱽ _ .snd .fst g =
    ΣPathP
      ( Codomain≡ (SET ℓ) refl (reind-fst _ _)
      , Codomain≡ (SET ℓ) refl (reind-fst _ _))
  BinProductⱽSETCod a b .universalⱽ _ .snd .snd hᴰ =
    Codomain≡ (SET ℓ) refl (funExt λ z →
      ΣPathP (base z
      , ΣPathP
        ( FibPathP ℓ (base z) (funExt⁻ (reind-fst _ (hᴰ SETCod.⋆ᴰ ×Codπ₁ a b)) z)
        , FibPathP ℓ (base z) (funExt⁻ (reind-fst _ (hᴰ SETCod.⋆ᴰ ×Codπ₂ a b)) z))))
    where
    base : ∀ z → _ ≡ hᴰ .fst z .fst
    base z i = hᴰ .snd (~ i) z

  BinProductsⱽSETCod : BinProductsⱽ (SETCod ℓ)
  BinProductsⱽSETCod a b .fst = a ×Cod b
  BinProductsⱽSETCod a b .snd =
    improvePshIso (REPRⱽ (BinProductⱽSETCod a b) .snd)
      ( (λ _ hᴰ → hᴰ SETCod.⋆ᴰ ×Codπ₁ a b , hᴰ SETCod.⋆ᴰ ×Codπ₂ a b)
      , funExt λ _ → funExt λ hᴰ → ΣPathP
          ( Codomain≡ (SET ℓ) refl (reind-fst _ _)
          , Codomain≡ (SET ℓ) refl (reind-fst _ _)))
      ((λ _ → ×Cod-intro a b) , refl)

  _ : ∀ {X W : hSet ℓ} {a b : SETᴰ.ob[ X ]} {k : ⟨ W ⟩ → ⟨ X ⟩}
    {c : SETᴰ.ob[ W ]} (hᴰ : SETCod.Hom[ k ][ c , a ×Cod b ]) z
    → BinProductsⱽSETCod a b .snd .PshIso.trans .PshHom.N-ob (W , c , k) hᴰ
      .fst .fst z
      ≡ hᴰ .fst z .snd .fst .fst
  _ = λ hᴰ z → refl

  BinCoProductⱽSETCod : {X : hSet ℓ} (a b : SETᴰ.ob[ X ])
    → UniversalElementⱽ' (SETCod ℓ ^opᴰ) X (BinProductⱽSpec (SETCod ℓ ^opᴰ) a b)
  BinCoProductⱽSETCod a b .vertexⱽ = a +Cod b
  BinCoProductⱽSETCod a b .elementⱽ = +Codσ₁ a b , +Codσ₂ a b
  BinCoProductⱽSETCod a b .universalⱽ _ .fst = +Cod-elim a b
  BinCoProductⱽSETCod a b .universalⱽ _ .snd .fst g =
    ΣPathP
      ( Codomain≡ (SET ℓ) refl (reind^op-fst _ _)
      , Codomain≡ (SET ℓ) refl (reind^op-fst _ _))
  BinCoProductⱽSETCod a b .universalⱽ _ .snd .snd hᴰ =
    Codomain≡ (SET ℓ) refl (funExt λ
      { (x , inl p) →
          funExt⁻ (reind^op-fst _ (+Codσ₁ a b SETCod.⋆ᴰ hᴰ)) (x , p)
      ; (x , inr q) →
          funExt⁻ (reind^op-fst _ (+Codσ₂ a b SETCod.⋆ᴰ hᴰ)) (x , q) })

  BinCoProductsⱽSETCod : BinCoProductsⱽ (SETCod ℓ)
  BinCoProductsⱽSETCod a b .fst = a +Cod b
  BinCoProductsⱽSETCod a b .snd =
    improvePshIso (REPRⱽ (BinCoProductⱽSETCod a b) .snd)
      ( (λ _ hᴰ → +Codσ₁ a b SETCod.⋆ᴰ hᴰ , +Codσ₂ a b SETCod.⋆ᴰ hᴰ)
      , funExt λ _ → funExt λ hᴰ → ΣPathP
          ( Codomain≡ (SET ℓ) refl (reind^op-fst _ _)
          , Codomain≡ (SET ℓ) refl (reind^op-fst _ _)))
      ((λ _ → +Cod-elim a b) , refl)

  _ : ∀ {X W : hSet ℓ} {a b : SETᴰ.ob[ X ]} {k : ⟨ X ⟩ → ⟨ W ⟩}
    {c : SETᴰ.ob[ W ]} (hᴰ : SETCod.Hom[ k ][ a +Cod b , c ]) z
    → BinCoProductsⱽSETCod a b .snd .PshIso.trans .PshHom.N-ob (W , c , k) hᴰ
      .fst .fst z
      ≡ hᴰ .fst (z .fst , inl (z .snd))
  _ = λ hᴰ z → refl

  module _ {X Y : hSet ℓ} (f : ⟨ Y ⟩ → ⟨ X ⟩) (Q : SETᴰ.ob[ X ]) where
    pullIntro : ∀ {W} {g : ⟨ W ⟩ → ⟨ Y ⟩} {c : SETᴰ.ob[ W ]}
      → SETCod.Hom[ (λ w → f (g w)) ][ c , Q ] → SETCod.Hom[ g ][ c , Pull f Q ]
    pullIntro {g = g} φ .fst z = g (z .fst) , φ .fst z , λ i → φ .snd i z
    pullIntro φ .snd = refl

    CartesianLiftSETCod : UniversalElementⱽ' (SETCod ℓ) Y
      (CartesianLiftPshSpec (SET ℓ [-, X ]) (SETCod ℓ) (SETCod ℓ [-][-, Q ]) f)
    CartesianLiftSETCod .vertexⱽ = Pull f Q
    CartesianLiftSETCod .elementⱽ = pullπ f Q
    CartesianLiftSETCod .universalⱽ _ .fst = pullIntro
    CartesianLiftSETCod .universalⱽ _ .snd .fst φ =
      Codomain≡ (SET ℓ) refl (reind-fst _ _)
    CartesianLiftSETCod .universalⱽ _ .snd .snd ψ =
      Codomain≡ (SET ℓ) refl (funExt λ z →
        ΣPathP (base z
        , FibPathP ℓ (cong f (base z))
            (funExt⁻ (reind-fst _ (ψ SETCod.⋆ᴰ pullπ f Q)) z)))
      where
      base : ∀ z → _ ≡ ψ .fst z .fst
      base z i = ψ .snd (~ i) z

  isFibrationSETCod : isFibration (SETCod ℓ)
  isFibrationSETCod Q Y f .fst = Pull f Q
  isFibrationSETCod Q Y f .snd =
    improvePshIso (REPRⱽ (CartesianLiftSETCod f Q) .snd)
      ( (λ _ hᴰ → hᴰ SETCod.⋆ᴰ pullπ f Q)
      , funExt λ _ → funExt λ hᴰ → Codomain≡ (SET ℓ) refl (reind-fst _ _))
      ((λ _ → pullIntro f Q) , refl)

  _ : ∀ {X Y W : hSet ℓ} {Q : SETᴰ.ob[ X ]} {f : ⟨ Y ⟩ → ⟨ X ⟩}
    {g : ⟨ W ⟩ → ⟨ Y ⟩} {c : SETᴰ.ob[ W ]}
    (hᴰ : SETCod.Hom[ g ][ c , Pull f Q ]) z
    → isFibrationSETCod Q Y f .snd .PshIso.trans .PshHom.N-ob (W , c , g) hᴰ
      .fst z
      ≡ hᴰ .fst z .snd .fst
  _ = λ hᴰ z → refl

  module _ {X Y : hSet ℓ} (f : ⟨ X ⟩ → ⟨ Y ⟩) (P : SETᴰ.ob[ X ]) where
    pushElim : ∀ {W} {g : ⟨ Y ⟩ → ⟨ W ⟩} {c : SETᴰ.ob[ W ]}
      → SETCod.Hom[ (λ x → g (f x)) ][ P , c ] → SETCod.Hom[ g ][ Push f P , c ]
    pushElim φ .fst w = φ .fst (w .snd .fst)
    pushElim {g = g} φ .snd = funExt λ w →
      funExt⁻ (φ .snd) (w .snd .fst) ∙ cong g (w .snd .snd)

    OpcartesianLiftSETCod : UniversalElementⱽ' (SETCod ℓ ^opᴰ) Y
      (CartesianLiftPshSpec ((SET ℓ ^op) [-, X ]) (SETCod ℓ ^opᴰ)
        ((SETCod ℓ ^opᴰ) [-][-, P ]) f)
    OpcartesianLiftSETCod .vertexⱽ = Push f P
    OpcartesianLiftSETCod .elementⱽ = pushσ f P
    OpcartesianLiftSETCod .universalⱽ _ .fst = pushElim
    OpcartesianLiftSETCod .universalⱽ _ .snd .fst φ =
      Codomain≡ (SET ℓ) refl (reind^op-fst _ _)
    OpcartesianLiftSETCod .universalⱽ _ .snd .snd ψ =
      Codomain≡ (SET ℓ) refl (funExt λ w →
        funExt⁻ (reind^op-fst _ (pushσ f P SETCod.⋆ᴰ ψ)) (w .snd .fst)
        ∙ cong (ψ .fst) (λ i →
            w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j)))

  isOpfibrationSETCod : isFibration (SETCod ℓ ^opᴰ)
  isOpfibrationSETCod P Y f .fst = Push f P
  isOpfibrationSETCod P Y f .snd =
    improvePshIso (REPRⱽ (OpcartesianLiftSETCod f P) .snd)
      ( (λ _ hᴰ → pushσ f P SETCod.⋆ᴰ hᴰ)
      , funExt λ _ → funExt λ hᴰ → Codomain≡ (SET ℓ) refl (reind^op-fst _ _))
      ((λ _ → pushElim f P) , refl)

  _ : ∀ {X Y W : hSet ℓ} {P : SETᴰ.ob[ X ]} {f : ⟨ X ⟩ → ⟨ Y ⟩}
    {g : ⟨ Y ⟩ → ⟨ W ⟩} {c : SETᴰ.ob[ W ]}
    (hᴰ : SETCod.Hom[ g ][ Push f P , c ]) z
    → isOpfibrationSETCod P Y f .snd .PshIso.trans .PshHom.N-ob (W , c , g) hᴰ
      .fst z
      ≡ hᴰ .fst (f (z .fst) , z , refl)
  _ = λ hᴰ z → refl

module _ {ℓ : Level} where
  SETCodCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-suc ℓ) ℓ
  SETCodCCⱽ = cartesiancategoryⱽ (SETCod ℓ) TerminalsⱽSETCod BinProductsⱽSETCod
    isFibrationSETCod
