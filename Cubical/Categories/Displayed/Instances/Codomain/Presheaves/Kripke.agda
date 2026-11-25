{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Kripke where

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

private
  variable
    ℓC ℓC' : Level

open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} {ℓ : Level} where
  private
    module PSH = Category (PSH {C = C} ℓ)

  module _ {X : Presheaf C ℓ} (a : Presheafᴰ X (Unitᴰ C) ℓ) where
    module _ {D : Presheaf C ℓ} {k : PSH.Hom[ D , X ]} {c : Presheafᴰ D (Unitᴰ
      C) ℓ} where
      ×Pull≡Psh : ∀ {Γ} (z z' : ⟨ ∫ᴾ ℓ (c ×ᴾ Pull k a) .F-ob Γ ⟩)
        → z .snd .fst .fst ≡ z' .snd .fst .fst
        → z .snd .snd .fst .snd .fst ≡ z' .snd .snd .fst .snd .fst
        → z ≡ z'
      ×Pull≡Psh {Γ} z z' p q i =
        base i
        , FibPathPPsh ℓ base {u = z .snd .fst} {u' = z' .snd .fst} p i
        , FibPathPPsh ℓ base {u = z .snd .snd} {u' = z' .snd .snd}
            (λ j → mid j
              , FibPathPPsh ℓ (λ l → k .N-ob Γ (mid l))
                  {u = z .snd .snd .fst .snd}
                  {u' = z' .snd .snd .fst .snd} q j) i
        where
        base : z .fst ≡ z' .fst
        base =
          sym (z .snd .fst .snd) ∙ cong fst p ∙ z' .snd .fst .snd
        mid : z .snd .snd .fst .fst ≡ z' .snd .snd .fst .fst
        mid = z .snd .snd .snd ∙ base ∙ sym (z' .snd .snd .snd)


module _ {C : Category ℓC ℓC'} (ℓ₀ : Level) where
  private
    ℓ = ℓ-max (ℓ-max ℓC ℓC') ℓ₀
    module C = Category C
    module PSH = Category (PSH {C = C} ℓ)
    module PSHCod = Categoryᴰ (PSHCod {C = C} ℓ)

  module _ {X : Presheaf C ℓ} where
    private
      module X = PresheafNotation X
      module E = Category (Unitᴰ C / X)

    module _ (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
      ⇒Fun : E.ob → Type ℓ
      ⇒Fun Γx = ∀ {Δx} → E.Hom[ Δx , Γx ]
        → ⟨ FibᴰPsh ℓ a .F-ob Δx ⟩ → ⟨ FibᴰPsh ℓ b .F-ob Δx ⟩

      ⇒Nat : ∀ {Γx} → ⇒Fun Γx → Type ℓ
      ⇒Nat {Γx} G = ∀ {Δx Δx'} (n : E.Hom[ Δx' , Δx ]) (m : E.Hom[ Δx , Γx ]) u
        → G (n E.⋆ m) (FibᴰPsh ℓ a .F-hom n u) ≡ FibᴰPsh ℓ b .F-hom n (G m u)

      isProp⇒Nat : ∀ {Γx} (G : ⇒Fun Γx) → isProp (⇒Nat G)
      isProp⇒Nat G = isPropImplicitΠ2 λ _ Δx' → isPropΠ3 λ _ _ _ →
        FibᴰPsh ℓ b .F-ob Δx' .snd _ _

    infixr 5 _⇒ᴾ_

    _⇒ᴾ_ : Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ X
      (Unitᴰ C) ℓ
    (a ⇒ᴾ b) .F-ob Γx = Σ (⇒Fun a b Γx) (⇒Nat a b)
      , isSetΣ
          (isSetImplicitΠ λ Δx → isSetΠ2 λ _ _ → FibᴰPsh ℓ b .F-ob Δx .snd)
          (λ G → isProp→isSet (isProp⇒Nat a b G))
    (a ⇒ᴾ b) .F-hom f G .fst n = G .fst (n E.⋆ f)
    (a ⇒ᴾ b) .F-hom f G .snd n m u =
      cong (λ m' → G .fst m' (FibᴰPsh ℓ a .F-hom n u)) (E.⋆Assoc n m f)
      ∙ G .snd n (m E.⋆ f) u
    (a ⇒ᴾ b) .F-id = funExt λ G →
      ΣPathPProp (isProp⇒Nat a b)
        (implicitFunExt λ {Δx} → funExt λ n →
          cong (λ m → G .fst {Δx} m) (E.⋆IdR n))
    (a ⇒ᴾ b) .F-seq f g = funExt λ G →
      ΣPathPProp (isProp⇒Nat a b)
        (implicitFunExt λ {Δx} → funExt λ n →
          cong (λ m → G .fst {Δx} m) (sym (E.⋆Assoc n g f)))

    module _ (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
      ⇒cong : ∀ {Γ} {t t' : ⟨ ∫ᴾ ℓ (a ⇒ᴾ b) .F-ob Γ ⟩} (s : t ≡ t')
        {Δ} {x x' : X.p[ Δ ]} (r : x ≡ x')
        {m : E.Hom[ (Δ , tt , x) , (Γ , tt , t .fst) ]}
        {m' : E.Hom[ (Δ , tt , x') , (Γ , tt , t' .fst) ]}
        {u : FibPsh ℓ a Δ x} {u' : FibPsh ℓ a Δ x'}
        → m .fst ≡ m' .fst → u .fst ≡ u' .fst
        → t .snd .fst m u .fst ≡ t' .snd .fst m' u' .fst
      ⇒cong s {Δ} r {m} {m'} {u} {u'} p q i =
        s i .snd .fst {Δ , tt , r i}
          ( p i , tt
          , isProp→PathP (λ i → X.isSetPsh (p i X.⋆ s i .fst) (r i))
              (m .snd .snd) (m' .snd .snd) i)
          (FibPathPPsh ℓ r {u = u} {u' = u'} q i) .fst

  module _ {X : Presheaf C ℓ} (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
    private
      module X = PresheafNotation X
      module E = Category (Unitᴰ C / X)

    appDomPsh : Presheafᴰ X (Unitᴰ C) ℓ
    appDomPsh = (a ⇒ᴾ b) ×ᴾ Pull PSH.id a

    appMor : ∀ {Γ} (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Γ ⟩)
      → E.Hom[ (Γ , tt , y .fst) , (Γ , tt , y .snd .fst .fst .fst) ]
    appMor y = C.id , tt , X.⋆IdL _ ∙ y .snd .fst .snd

    appArg : ∀ {Γ} (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Γ ⟩) → FibPsh ℓ a Γ (y .fst)
    appArg y =
      y .snd .snd .fst .snd .fst
      , y .snd .snd .fst .snd .snd ∙ y .snd .snd .snd

    appFun : ∀ Γ (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Γ ⟩) → FibPsh ℓ b Γ (y .fst)
    appFun Γ y = y .snd .fst .fst .snd .fst (appMor y) (appArg y)

    appPsh : PSHCod.Hom[ PSH.id ][ appDomPsh , b ]
    appPsh = mkPsh ℓ {P = appDomPsh} {Q = b}
      ( appFun
      , λ {Γ} {Δ} ρ → funExt λ y →
          ⇒cong a b {t = y .snd .fst .fst} refl refl
            {m = appMor (∫ᴾ ℓ appDomPsh .F-hom ρ y) E.⋆ (ρ , tt , refl)}
            {m' = (ρ , tt , refl) E.⋆ appMor y}
            {u = appArg (∫ᴾ ℓ appDomPsh .F-hom ρ y)}
            {u' = FibᴰPsh ℓ a .F-hom (ρ , tt , refl) (appArg y)}
            (C.⋆IdL ρ ∙ sym (C.⋆IdR ρ)) refl
          ∙ cong fst
              (y .snd .fst .fst .snd .snd (ρ , tt , refl) (appMor y)
                (appArg y)))

    evPt : ∀ {Γ} (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Γ ⟩)
      (t' : ⟨ ∫ᴾ ℓ (a ⇒ᴾ b) .F-ob Γ ⟩) (u' : FibPsh ℓ a Γ (t' .fst))
      → y .snd .fst .fst ≡ t'
      → y .snd .snd .fst .snd .fst ≡ u' .fst
      → appFun Γ y .fst ≡ t' .snd .fst (C.id , tt , X.⋆IdL _) u' .fst
    evPt y t' u' s q =
      ⇒cong a b s (sym (y .snd .fst .snd) ∙ cong fst s)
        {m = appMor y} {m' = C.id , tt , X.⋆IdL _}
        {u = appArg y} {u' = u'} refl q

    module _ {D : Presheaf C ℓ} {k : PSH.Hom[ D , X ]} {c : Presheafᴰ D (Unitᴰ
      C) ℓ} where
      private
        module D = PresheafNotation D

      module _ {Γ} (zc : ⟨ ∫ᴾ ℓ c .F-ob Γ ⟩) where
        ldaIn : ∀ {Δ x'}
          (m : E.Hom[ (Δ , tt , x') , (Γ , tt , k .N-ob Γ (zc .fst)) ])
          (u : FibPsh ℓ a Δ x') → ⟨ ∫ᴾ ℓ (c ×ᴾ Pull k a) .F-ob Δ ⟩
        ldaIn m u =
          m .fst D.⋆ zc .fst
          , (∫ᴾ ℓ c .F-hom (m .fst) zc , refl)
          , ( ( m .fst D.⋆ zc .fst
              , u .fst
              , u .snd ∙ sym (m .snd .snd)
                ∙ sym (funExt⁻ (k .N-hom (m .fst)) (zc .fst)))
            , refl)

      module _ (f : PSHCod.Hom[ k ][ c ×ᴾ Pull k a , b ]) where
        private
          module _ {Γ} (zc : ⟨ ∫ᴾ ℓ c .F-ob Γ ⟩) where
            ldaG : ⇒Fun a b (Γ , tt , k .N-ob Γ (zc .fst))
            ldaG {Δ , _ , x'} m u =
              f .fst .N-ob Δ (ldaIn zc m u)
              , ptPsh ℓ f .fst Δ (ldaIn zc m u) .snd
                ∙ funExt⁻ (k .N-hom (m .fst)) (zc .fst) ∙ m .snd .snd

            ldaNat : ⇒Nat a b ldaG
            ldaNat {Δ , _ , _} {Δ' , _ , _} n m u =
              FibPathPPsh ℓ refl
                ( cong (f .fst .N-ob Δ')
                    (×Pull≡Psh a _ _
                      (funExt⁻ (∫ᴾ ℓ c .F-seq (m .fst) (n .fst)) zc) refl)
                ∙ funExt⁻ (f .fst .N-hom (n .fst)) (ldaIn zc m u))

        ldaPsh : PSHCod.Hom[ k ][ c , a ⇒ᴾ b ]
        ldaPsh = mkPsh ℓ {P = c} {Q = a ⇒ᴾ b}
          ( (λ Γ zc → (k .N-ob Γ (zc .fst) , ldaG zc , ldaNat zc) , refl)
          , λ {Γ} {Δ} ρ → funExt λ zc → ΣPathP
              ( funExt⁻ (k .N-hom ρ) (zc .fst)
              , ΣPathPProp (isProp⇒Nat a b) λ i {Δx} →
                  funExtDep
                    {A = λ i → E.Hom[ Δx
                      , (Δ , tt , funExt⁻ (k .N-hom ρ) (zc .fst) i) ]}
                    {B = λ _ _ → ⟨ FibᴰPsh ℓ a .F-ob Δx ⟩
                      → ⟨ FibᴰPsh ℓ b .F-ob Δx ⟩}
                    {f = ldaG (∫ᴾ ℓ c .F-hom ρ zc)}
                    {g = λ m → ldaG zc (m E.⋆ (ρ , tt , refl))}
                    (λ {m₀} {m₁} mp → funExt λ u → FibPathPPsh ℓ refl
                      (cong (f .fst .N-ob (Δx .fst))
                        (×Pull≡Psh a _ _
                          ( cong (λ σ → ∫ᴾ ℓ c .F-hom σ
                              (∫ᴾ ℓ c .F-hom ρ zc)) (λ j → mp j .fst)
                          ∙ sym (funExt⁻ (∫ᴾ ℓ c .F-seq ρ (m₁ .fst)) zc))
                          refl)))
                    i))

        βpt : ∀ {Γ} (z : ⟨ ∫ᴾ ℓ (c ×ᴾ Pull k a) .F-ob Γ ⟩)
          (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Γ ⟩)
          → y .snd .fst .fst ≡ ldaPsh .fst .N-ob Γ (z .snd .fst .fst)
          → y .snd .snd .fst .snd .fst ≡ z .snd .snd .fst .snd .fst
          → appFun Γ y .fst ≡ f .fst .N-ob Γ z
        βpt {Γ} z y e e' =
          ⇒cong a b e refl {m = appMor y}
            {m' = C.id , tt
              , cong (λ t → C.id X.⋆ t .fst) (sym e) ∙ appMor y .snd .snd}
            {u = appArg y} {u' = appArg y} refl refl
          ∙ cong (f .fst .N-ob Γ)
              (×Pull≡Psh a _ z (funExt⁻ (∫ᴾ ℓ c .F-id) (z .snd .fst .fst)) e')

      module _ (h : PSHCod.Hom[ k ][ c , a ⇒ᴾ b ]) where
        ηpt : ∀ {Γ} (zc : ⟨ ∫ᴾ ℓ c .F-ob Γ ⟩) {Δ x'}
          (m₀ : E.Hom[ (Δ , tt , x') , (Γ , tt , k .N-ob Γ (zc .fst)) ])
          (m₁ : E.Hom[ (Δ , tt , x') , (Γ , tt , h .fst .N-ob Γ zc .fst) ])
          → m₀ .fst ≡ m₁ .fst → (u : FibPsh ℓ a Δ x')
          (y : ⟨ ∫ᴾ ℓ appDomPsh .F-ob Δ ⟩)
          → y .snd .fst .fst ≡ h .fst .N-ob Δ (∫ᴾ ℓ c .F-hom (m₀ .fst) zc)
          → y .snd .snd .fst .snd .fst ≡ u .fst
          → appFun Δ y .fst ≡ h .fst .N-ob Γ zc .snd .fst m₁ u .fst
        ηpt {Γ} zc {Δ} {x'} m₀ m₁ mp u y e e' =
          ⇒cong a b e refl {m = appMor y} {m' = C.id , tt , q0}
            {u = appArg y} {u' = appArg y} refl refl
          ∙ ⇒cong a b s1 refl {m = C.id , tt , q0} {m' = C.id , tt , q1}
            {u = appArg y} {u' = appArg y} refl refl
          ∙ ⇒cong a b {t = h .fst .N-ob Γ zc} refl r2
            {m = (C.id , tt , q1) E.⋆ (m₀ .fst , tt , refl)}
            {m' = m₁} {u = appArg y} {u' = u} (C.⋆IdL (m₀ .fst) ∙ mp) e'
          where
          s1 = funExt⁻ (h .fst .N-hom (m₀ .fst)) zc
          q0 = cong (λ t → C.id X.⋆ t .fst) (sym e) ∙ appMor y .snd .snd
          q1 = cong (λ t → C.id X.⋆ t .fst) (sym s1) ∙ q0
          r2 = sym (appArg y .snd) ∙ cong fst e' ∙ u .snd

        ηG : ∀ {Γ} (zc : ⟨ ∫ᴾ ℓ c .F-ob Γ ⟩)
          (G₀ : ⇒Fun a b (Γ , tt , k .N-ob Γ (zc .fst)))
          (Y : ∀ {Δ x'}
            → E.Hom[ (Δ , tt , x') , (Γ , tt , k .N-ob Γ (zc .fst)) ]
            → FibPsh ℓ a Δ x' → ⟨ ∫ᴾ ℓ appDomPsh .F-ob Δ ⟩)
          → (∀ {Δ x'} m₀ (u : FibPsh ℓ a Δ x')
            → Y m₀ u .snd .fst .fst
              ≡ h .fst .N-ob Δ (∫ᴾ ℓ c .F-hom (m₀ .fst) zc))
          → (∀ {Δ x'} m₀ (u : FibPsh ℓ a Δ x')
            → Y m₀ u .snd .snd .fst .snd .fst ≡ u .fst)
          → (∀ {Δ x'} m₀ (u : FibPsh ℓ a Δ x')
            → G₀ m₀ u .fst ≡ appFun Δ (Y m₀ u) .fst)
          → PathP (λ i → ⇒Fun a b (Γ , tt , h .snd (~ i) .N-ob Γ zc))
              G₀ (h .fst .N-ob Γ zc .snd .fst)
        ηG {Γ} zc G₀ Y e e' hyp i {Δx} =
          funExtDep
            {A = λ i → E.Hom[ Δx , (Γ , tt , h .snd (~ i) .N-ob Γ zc) ]}
            {B = λ _ _ → ⟨ FibᴰPsh ℓ a .F-ob Δx ⟩ → ⟨ FibᴰPsh ℓ b .F-ob Δx ⟩}
            {f = G₀} {g = h .fst .N-ob Γ zc .snd .fst}
            (λ {m₀} {m₁} mp → funExt λ u → FibPathPPsh ℓ refl
              {u = G₀ m₀ u} {u' = h .fst .N-ob Γ zc .snd .fst m₁ u}
              (hyp m₀ u
              ∙ ηpt zc m₀ m₁ (λ j → mp j .fst) u (Y m₀ u) (e m₀ u) (e' m₀ u)))
            i

        lda-η : (g : PSHCod.Hom[ k ][ c ×ᴾ Pull k a , b ])
          → (∀ Γ zc → ldaPsh g .fst .N-ob Γ zc ≡ h .fst .N-ob Γ zc)
          → ldaPsh g ≡ h
        lda-η g H =
          Codomain≡ (PSH {C = C} ℓ) refl
            (makeNatTransPath (funExt λ Γ → funExt (H Γ)))
