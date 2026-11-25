{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Closed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Kripke

private
  variable
    ℓC ℓC' : Level

open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} {ℓ : Level} where
  AllLRⱽPSHCod : AllLRⱽ (PSHCod {C = C} ℓ)
  AllLRⱽPSHCod =
    BinProductsⱽ+Fibration→AllLRⱽ (PSHCod ℓ) BinProductsⱽPSHCod isFibrationPSHCod

  private
    module PSH = Category (PSH {C = C} ℓ)
    module PSHCod = Categoryᴰ (PSHCod {C = C} ℓ)

  module _ {X : Presheaf C ℓ} (a : Presheafᴰ X (Unitᴰ C) ℓ) where
    module _ {D : Presheaf C ℓ} {k : PSH.Hom[ D , X ]} {c : Presheafᴰ D (Unitᴰ
      C) ℓ} where
      module _ {v : Presheafᴰ X (Unitᴰ C) ℓ}
        (m : (PSHCod ℓ / (PSH {C = C} ℓ [-, X ]))
          [ (D , c , k) , (X , v , PSH.id) ]) where
        private
          module FCod = Fibers (PSHCod {C = C} ℓ)

        ×LRmap₁ : ∀ Γ z
          → ((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF) ⟪ m ⟫)
              .snd .fst .fst .N-ob Γ z .snd .fst .fst
            ≡ m .snd .fst .fst .N-ob Γ (z .snd .fst .fst)
        ×LRmap₁ Γ z = refl

        ×LRmap₂ : ∀ Γ z
          → ((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF) ⟪ m ⟫)
              .snd .fst .fst .N-ob Γ z .snd .snd .fst .snd .fst
            ≡ z .snd .snd .fst .snd .fst
        ×LRmap₂ Γ z = cong (λ t → t .snd .fst .N-ob Γ z)
          (×LRⱽPshᴰ-β₂ⱽ a (AllLRⱽPSHCod a) m)

module _ {C : Category ℓC ℓC'} (ℓ₀ : Level) where
  private
    ℓ = ℓ-max (ℓ-max ℓC ℓC') ℓ₀
    module C = Category C
    module PSH = Category (PSH {C = C} ℓ)
    module PSHCod = Categoryᴰ (PSHCod {C = C} ℓ)

  open UniversalElementⱽ'
  open PshHom

  module _ {X : Presheaf C ℓ} (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
    private
      module X = PresheafNotation X
      Expⱽ = LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)
        ⇒ⱽPshSmall (PSHCod ℓ [-][-, b ])

    module _ {D : Presheaf C ℓ} {k : PSH.Hom[ D , X ]} {c : Presheafᴰ D (Unitᴰ
      C) ℓ} where
      expN : (h : PSHCod.Hom[ k ][ c , _⇒ᴾ_ ℓ₀ a b ])
        → yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h .fst .N-ob
          ≡ (λ Γ z → appFun ℓ₀ a b Γ
            (((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF)
              ⟪ k , h , PSH.⋆IdR k ⟫) .snd .fst .fst .N-ob Γ z) .fst)
      expN h = reind-fstPsh {P = c ×ᴾ Pull k a} {Q = b} _ _

      module _ (f : PSHCod.Hom[ k ][ c ×ᴾ Pull k a , b ]) where
        expβ : yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) (ldaPsh ℓ₀ a b f) ≡
          f
        expβ = Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath
          (expN (ldaPsh ℓ₀ a b f) ∙ funExt λ Γ → funExt λ z → βpt ℓ₀ a b f z
            (((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF)
              ⟪ k , ldaPsh ℓ₀ a b f , PSH.⋆IdR k ⟫) .snd .fst .fst .N-ob Γ z)
            (×LRmap₁ a (k , ldaPsh ℓ₀ a b f , PSH.⋆IdR k) Γ z)
            (×LRmap₂ a (k , ldaPsh ℓ₀ a b f , PSH.⋆IdR k) Γ z)))

      module _ (h : PSHCod.Hom[ k ][ c , _⇒ᴾ_ ℓ₀ a b ]) where
        expηpt : ∀ {Γ} zc
          → PathP (λ i → ⇒Fun ℓ₀ a b (Γ , tt , h .snd (~ i) .N-ob Γ zc))
              (ldaPsh ℓ₀ a b (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h)
                .fst .N-ob Γ zc .snd .fst)
              (h .fst .N-ob Γ zc .snd .fst)
        expηpt {Γ} zc = ηG ℓ₀ a b h zc
          (ldaPsh ℓ₀ a b (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h)
            .fst .N-ob Γ zc .snd .fst)
          (λ m₀ u →
            ((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a))
              ^opF) ⟪ k , h , PSH.⋆IdR k ⟫) .snd .fst .fst .N-ob _
              (ldaIn ℓ₀ a b zc m₀ u))
          (λ m₀ u → ×LRmap₁ a (k , h , PSH.⋆IdR k) _ (ldaIn ℓ₀ a b zc m₀ u))
          (λ m₀ u → ×LRmap₂ a (k , h , PSH.⋆IdR k) _ (ldaIn ℓ₀ a b zc m₀ u))
          (λ m₀ u → funExt⁻ (funExt⁻ (expN h) _) (ldaIn ℓ₀ a b zc m₀ u))


        evArgPsh : ∀ {Γ} (z : ⟨ ∫ᴾ ℓ (c ×ᴾ Pull k a) .F-ob Γ ⟩)
          → FibPsh ℓ a Γ (h .fst .N-ob Γ (z .snd .fst .fst) .fst)
        evArgPsh {Γ} z =
          z .snd .snd .fst .snd .fst
          , z .snd .snd .fst .snd .snd
            ∙ cong (k .N-ob Γ) (z .snd .snd .snd ∙ sym (z .snd .fst .snd))
            ∙ (λ i → h .snd (~ i) .N-ob Γ (z .snd .fst .fst))

        evN : ∀ Γ → ⟨ ∫ᴾ ℓ (c ×ᴾ Pull k a) .F-ob Γ ⟩ → ⟨ ∫ᴾ ℓ b .F-ob Γ ⟩
        evN Γ z = h .fst .N-ob Γ (z .snd .fst .fst) .snd .fst
          (C.id , tt , X.⋆IdL _) (evArgPsh z) .fst

        evN≡pt : ∀ Γ z
          → appFun ℓ₀ a b Γ
              (((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF)
                ⟪ k , h , PSH.⋆IdR k ⟫) .snd .fst .fst .N-ob Γ z) .fst
            ≡ evN Γ z
        evN≡pt Γ z = evPt ℓ₀ a b
          (((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (PSHCod ℓ) (a , AllLRⱽPSHCod a)) ^opF)
            ⟪ k , h , PSH.⋆IdR k ⟫) .snd .fst .fst .N-ob Γ z)
          (h .fst .N-ob Γ (z .snd .fst .fst)) (evArgPsh z)
          (×LRmap₁ a (k , h , PSH.⋆IdR k) Γ z)
          (×LRmap₂ a (k , h , PSH.⋆IdR k) Γ z)

        evN≡ : yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h .fst .N-ob ≡ evN
        evN≡ = expN h ∙ funExt λ Γ → funExt (evN≡pt Γ)

        evPsh : PSHCod.Hom[ k ][ c ×ᴾ Pull k a , b ]
        evPsh = improvePsh ℓ (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h)
          evN evN≡

        evᴾ≡ : yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h ≡ evPsh
        evᴾ≡ = improveᴾ≡ ℓ (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h)
          evN evN≡

        expηN : ∀ Γ zc
          → ldaPsh ℓ₀ a b (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h)
              .fst .N-ob Γ zc
            ≡ h .fst .N-ob Γ zc
        expηN Γ zc = ΣPathP
          ( (λ i → h .snd (~ i) .N-ob Γ zc)
          , ΣPathPProp (isProp⇒Nat ℓ₀ a b) (expηpt zc))

        expη : ldaPsh ℓ₀ a b (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob (D , c , k) h) ≡
          h
        expη = lda-η ℓ₀ a b h _ expηN

    expUniversal : isPshIso (yoRecⱽ Expⱽ (appPsh ℓ₀ a b))
    expUniversal (D , c , k) = ldaPsh ℓ₀ a b , expβ , expη

    evSingl : singl (yoRecⱽ Expⱽ (appPsh ℓ₀ a b) .N-ob)
    evSingl .fst (D , c , k) h = evPsh h
    evSingl .snd i (D , c , k) h = evᴾ≡ h i

    expIso₀ : PshIsoⱽ (PSHCod ℓ [-][-, _⇒ᴾ_ ℓ₀ a b ]) Expⱽ
    expIso₀ = pshiso (yoRecⱽ Expⱽ (appPsh ℓ₀ a b)) expUniversal

    ldaSingl : singl (invPshIso expIso₀ .PshIso.trans .N-ob)
    ldaSingl .fst (D , c , k) = ldaPsh ℓ₀ a b
    ldaSingl .snd i (D , c , k) = ldaPsh ℓ₀ a b

    expIso : PshIsoⱽ (PSHCod ℓ [-][-, _⇒ᴾ_ ℓ₀ a b ]) Expⱽ
    expIso = improvePshIso expIso₀ evSingl ldaSingl

  ExponentialsⱽPSHCod : Exponentialsⱽ (PSHCod {C = C} ℓ) AllLRⱽPSHCod
  ExponentialsⱽPSHCod a b = _⇒ᴾ_ ℓ₀ a b , expIso a b

  _ : ∀ {X D : Presheaf C ℓ} {a b : Presheafᴰ X (Unitᴰ C) ℓ} {k : PSH.Hom[ D , X
    ]}
    {c : Presheafᴰ D (Unitᴰ C) ℓ} (h : PSHCod.Hom[ k ][ c , _⇒ᴾ_ ℓ₀ a b ]) Γ z
    → ExponentialsⱽPSHCod a b .snd .PshIso.trans .PshHom.N-ob (D , c , k) h
      .fst .N-ob Γ z
      ≡ evN a b h Γ z
  _ = λ h Γ z → refl
