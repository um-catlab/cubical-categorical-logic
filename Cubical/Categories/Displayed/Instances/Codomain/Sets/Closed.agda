{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Sets.Closed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
  hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets.Base

module _ {ℓ : Level} where
  private
    module SETᴰ = Categoryᴰ (SETᴰ ℓ ℓ)
    module SETCod = Categoryᴰ (SETCod ℓ)

  open UniversalElementⱽ'
  open PshHom

  AllLRⱽSETCod : AllLRⱽ (SETCod ℓ)
  AllLRⱽSETCod =
    BinProductsⱽ+Fibration→AllLRⱽ (SETCod ℓ) BinProductsⱽSETCod isFibrationSETCod

  module _ {X : hSet ℓ} (a : SETᴰ.ob[ X ]) where
    module _ {W : hSet ℓ} {k : ⟨ W ⟩ → ⟨ X ⟩} {c : SETᴰ.ob[ W ]} where
      ×Pull≡ : (z z' : ⟨ ∫El ℓ (c ×Cod Pull k a) ⟩)
        → z .snd .fst .fst ≡ z' .snd .fst .fst
        → z .snd .snd .fst .snd .fst ≡ z' .snd .snd .fst .snd .fst
        → z ≡ z'
      ×Pull≡ z z' p q i =
        base i
        , FibPathP ℓ base {u = z .snd .fst} {u' = z' .snd .fst} p i
        , FibPathP ℓ base {u = z .snd .snd} {u' = z' .snd .snd}
            (λ j → mid j
              , FibPathP ℓ (λ l → k (mid l)) {u = z .snd .snd .fst .snd}
                  {u' = z' .snd .snd .fst .snd} q j) i
        where
        base : z .fst ≡ z' .fst
        base =
          sym (z .snd .fst .snd) ∙ cong fst p ∙ z' .snd .fst .snd
        mid : z .snd .snd .fst .fst ≡ z' .snd .snd .fst .fst
        mid = z .snd .snd .snd ∙ base ∙ sym (z' .snd .snd .snd)

      module _ {v : SETᴰ.ob[ X ]} (h : SETCod.Hom[ k ][ c , v ])
        (e : (λ w → k w) ≡ k) where
        ×LRmap : SETCod.Hom[ k ][ c ×Cod Pull k a , v ×Cod Pull (λ x → x) a ]
        ×LRmap =
          Functor.F-hom (×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (SETCod ℓ) (a , AllLRⱽSETCod a)))
            {x = W , c , k} {y = X , v , λ x → x} (k , h , e) .snd .fst

        ×LRmap₁ : ∀ z → ×LRmap .fst z .snd .fst .fst ≡ h .fst (z .snd .fst .fst)
        ×LRmap₁ z = refl

        ×LRmap₂ : ∀ z → ×LRmap .fst z .snd .snd .fst .snd .fst
          ≡ z .snd .snd .fst .snd .fst
        ×LRmap₂ z = cong (λ t → t .snd .fst z)
          (×LRⱽPshᴰ-β₂ⱽ a (AllLRⱽSETCod a) (k , h , e))

  module _ {X : hSet ℓ} where
    infixr 5 _⇒Cod_

    _⇒Cod_ : SETᴰ.ob[ X ] → SETᴰ.ob[ X ] → SETᴰ.ob[ X ]
    (a ⇒Cod b) x = (Fib ℓ a x → Fib ℓ b x) , isSet→ (isSetFib ℓ b x)

  module _ {X : hSet ℓ} (a b : SETᴰ.ob[ X ]) where
    appCod : SETCod.Hom[ (λ x → x) ][ (a ⇒Cod b) ×Cod Pull (λ x → x) a , b ]
    appCod .fst z =
      z .snd .fst .fst .snd
        ( z .snd .snd .fst .snd .fst
        , z .snd .snd .fst .snd .snd ∙ z .snd .snd .snd
          ∙ sym (z .snd .fst .snd))
        .fst
    appCod .snd i z =
      (z .snd .fst .fst .snd
        ( z .snd .snd .fst .snd .fst
        , z .snd .snd .fst .snd .snd ∙ z .snd .snd .snd
          ∙ sym (z .snd .fst .snd))
        .snd
      ∙ z .snd .fst .snd) i

    appCong : {t t' : ⟨ ∫El ℓ (a ⇒Cod b) ⟩} (P : t ≡ t')
      (u : Fib ℓ a (t .fst)) (u' : Fib ℓ a (t' .fst))
      → u .fst ≡ u' .fst → t .snd u .fst ≡ t' .snd u' .fst
    appCong P u u' q i =
      P i .snd (FibPathP ℓ (cong fst P) {u = u} {u' = u'} q i) .fst

    module _ {W : hSet ℓ} {k : ⟨ W ⟩ → ⟨ X ⟩} {c : SETᴰ.ob[ W ]} where
      ldaCod : SETCod.Hom[ k ][ c ×Cod Pull k a , b ] → SETCod.Hom[ k ][ c , a ⇒Cod b ]
      ldaCod f = mk ℓ λ z →
        ( k (z .fst)
        , λ ua → pt ℓ f (z .fst , (z , refl) , (z .fst , ua) , refl))
        , refl

      module _ (h : SETCod.Hom[ k ][ c , a ⇒Cod b ]) where
        private
          base : ∀ z → k (z .fst) ≡ h .fst z .fst
          base z i = h .snd (~ i) z

        ldaSlice : ∀ z → Fib ℓ a (k (z .fst)) → ⟨ ∫El ℓ (c ×Cod Pull k a) ⟩
        ldaSlice z u = z .fst , (z , refl) , (z .fst , u) , refl

        lda-η : (g : SETCod.Hom[ k ][ c ×Cod Pull k a , b ])
          → (∀ z (u₀ : Fib ℓ a (k (z .fst))) (u₁ : Fib ℓ a (h .fst z .fst))
            → u₀ .fst ≡ u₁ .fst
            → g .fst (ldaSlice z u₀) ≡ h .fst z .snd u₁ .fst)
          → ldaCod g ≡ h
        lda-η g H = Codomain≡ (SET ℓ) refl (funExt λ z i →
          base z i
          , funExtDep {A = λ i → Fib ℓ a (base z i)}
              {B = λ i _ → Fib ℓ b (base z i)}
              {f = λ u → pt ℓ g (ldaSlice z u)} {g = h .fst z .snd}
              (λ {u₀} {u₁} pu → FibPathP ℓ (base z)
                {u = pt ℓ g (ldaSlice z u₀)} {u' = h .fst z .snd u₁}
                (H z u₀ u₁ λ j → pu j .fst))
              i)

        evArg : (z : ⟨ ∫El ℓ (c ×Cod Pull k a) ⟩)
          → Fib ℓ a (h .fst (z .snd .fst .fst) .fst)
        evArg z =
          z .snd .snd .fst .snd .fst
          , z .snd .snd .fst .snd .snd
            ∙ cong k (z .snd .snd .snd ∙ sym (z .snd .fst .snd))
            ∙ (λ i → h .snd (~ i) (z .snd .fst .fst))

        evCod : SETCod.Hom[ k ][ c ×Cod Pull k a , b ]
        evCod .fst z = h .fst (z .snd .fst .fst) .snd (evArg z) .fst
        evCod .snd i z =
          ( h .fst (z .snd .fst .fst) .snd (evArg z) .snd
          ∙ (λ j → h .snd j (z .snd .fst .fst))
          ∙ cong k (z .snd .fst .snd)) i

    private
      Expⱽ = LRⱽObᴰ→LRⱽ (SETCod ℓ) (a , AllLRⱽSETCod a)
        ⇒ⱽPshSmall (SETCod ℓ [-][-, b ])

    ExponentialⱽSETCod : UniversalElementⱽ' (SETCod ℓ) X Expⱽ
    ExponentialⱽSETCod .vertexⱽ = a ⇒Cod b
    ExponentialⱽSETCod .elementⱽ = appCod
    ExponentialⱽSETCod .universalⱽ _ .fst = ldaCod
    ExponentialⱽSETCod .universalⱽ (W , c , k) .snd .fst f =
      Codomain≡ (SET ℓ) refl
        ( reind-fst {P = c ×Cod Pull k a} {Q = b} _ _
        ∙ funExt λ z → cong (f .fst)
            (×Pull≡ a _ z
              refl
              (×LRmap₂ a (ldaCod f) (Category.⋆IdR (SET ℓ) k) z)))
    ExponentialⱽSETCod .universalⱽ (W , c , k) .snd .snd h =
      lda-η h (yoRecⱽ Expⱽ appCod .N-ob (W , c , k) h) λ z u₀ u₁ q →
        funExt⁻ (reind-fst {P = c ×Cod Pull k a} {Q = b} _ _)
          (ldaSlice h z u₀)
        ∙ appCong (×LRmap₁ a h e (ldaSlice h z u₀)) _ u₁
            (×LRmap₂ a h e (ldaSlice h z u₀) ∙ q)
      where
      e = Category.⋆IdR (SET ℓ) {x = W} {y = X} k

  ExponentialsⱽSETCod : Exponentialsⱽ (SETCod ℓ) AllLRⱽSETCod
  ExponentialsⱽSETCod a b .fst = a ⇒Cod b
  ExponentialsⱽSETCod {X} a b .snd =
    improvePshIso (REPRⱽ (ExponentialⱽSETCod a b) .snd)
      ( (λ _ h → evCod a b h)
      , funExt λ (W , c , k) → funExt λ h →
          Codomain≡ (SET ℓ) refl
            ( reind-fst {P = c ×Cod Pull k a} {Q = b} _ _
            ∙ funExt λ z →
                appCong a b
                  (×LRmap₁ a h (Category.⋆IdR (SET ℓ) {x = W} {y = X} k) z)
                  _ (evArg a b h z)
                  (×LRmap₂ a h (Category.⋆IdR (SET ℓ) {x = W} {y = X} k) z)))
      ((λ _ → ldaCod a b) , refl)

  _ : ∀ {X W : hSet ℓ} {a b : SETᴰ.ob[ X ]} {k : ⟨ W ⟩ → ⟨ X ⟩}
    {c : SETᴰ.ob[ W ]} (h : SETCod.Hom[ k ][ c , a ⇒Cod b ]) z
    → ExponentialsⱽSETCod a b .snd .PshIso.trans .PshHom.N-ob (W , c , k) h
      .fst z
      ≡ h .fst (z .snd .fst .fst) .snd (evArg a b h z) .fst
  _ = λ h z → refl
