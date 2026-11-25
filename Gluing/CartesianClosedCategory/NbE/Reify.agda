{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.NbE.Reify where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  using (_×_; ↑_)
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.UncurriedElim

open import Gluing.CartesianClosedCategory.Renamings
open import Gluing.CartesianClosedCategory.NormalForms
open import Gluing.CartesianClosedCategory.NbE.Base
open import Gluing.CartesianClosedCategory.NbE.Neutral

private
  variable ℓQ ℓQ' : Level

open Functor
open NatTrans

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  open NfPresheaf Q
  open NePresheaf Q

  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'
    R = REN Q
    N = nerve Q
    Motive = NbEMotive Q
    module Motive = CartesianClosedCategoryᴰ Motive
    module GL = ChosenReindNotation Motive.Cᴰ
      ⦃ reindexReind (PSHCod ℓ) N ⦄

  Gl : ∀ A → Presheafᴰ (N ⟅ A ⟆) (Unitᴰ R) ℓ
  Gl = elimOb Q Motive (λ o → Nf[ ↑ o ])

  module _ {A} {P : Presheafᴰ (N ⟅ A ⟆) (Unitᴰ R) ℓ}
    (φ : GL.Hom[ idₑ ][ P , Nf[ A ] ]) where
    module _ {Γ} (z : fst (∫ᴾ ℓ P .F-ob Γ)) where
      nfOf : Nf Q Γ A
      nfOf = φ .fst .N-ob Γ z .snd .fst

      nfOf≡ : ⌈_⌉ Q nfOf ≡ z .fst
      nfOf≡ = φ .fst .N-ob Γ z .snd .snd ∙ ptPsh ℓ φ .fst Γ z .snd
        ∙ ⋆ₑIdR (z .fst)

    nfOf-nat : ∀ {Δ Γ} (ρ : R [ Δ , Γ ]) (z : fst (∫ᴾ ℓ P .F-ob Γ))
      → nfOf (∫ᴾ ℓ P .F-hom ρ z) ≡ renNf Q ρ (nfOf z)
    nfOf-nat ρ z = cong (λ w → w .snd .fst) (funExt⁻ (φ .fst .N-hom ρ) z)

  module _ {A B} {f : Expr Q A B} {P : Presheafᴰ (N ⟅ A ⟆) (Unitᴰ R) ℓ}
    {P' : Presheafᴰ (N ⟅ B ⟆) (Unitᴰ R) ℓ} (φ : GL.Hom[ f ][ P , P' ]) {Γ}
    (z : fst (∫ᴾ ℓ P .F-ob Γ)) where
    tri≡ : φ .fst .N-ob Γ z .fst ≡ z .fst ⋆ₑ f
    tri≡ = ptPsh ℓ φ .fst Γ z .snd

    hom-nat : ∀ {Δ} (ρ : R [ Δ , Γ ])
      → φ .fst .N-ob Δ (∫ᴾ ℓ P .F-hom ρ z)
        ≡ ∫ᴾ ℓ P' .F-hom ρ (φ .fst .N-ob Γ z)
    hom-nat ρ = funExt⁻ (φ .fst .N-hom ρ) z

  module _ {A B} (X : Presheafᴰ (N ⟅ A ⟆) (Unitᴰ R) ℓ)
    (Y : Presheafᴰ (N ⟅ B ⟆) (Unitᴰ R) ℓ) {Γ} where
    private
      XY = Motive.bpᴰ X Y .fst
    module _ (z : fst (∫ᴾ ℓ XY .F-ob Γ)) where
      cX : fst (∫ᴾ ℓ X .F-ob Γ)
      cX = z .snd .fst .fst .snd .fst
      cY : fst (∫ᴾ ℓ Y .F-ob Γ)
      cY = z .snd .snd .fst .snd .fst
      eX : cX .fst ≡ z .fst ⋆ₑ π₁
      eX = z .snd .fst .fst .snd .snd ∙ cong (_⋆ₑ π₁) (z .snd .fst .snd)
      eY : cY .fst ≡ z .fst ⋆ₑ π₂
      eY = z .snd .snd .fst .snd .snd ∙ cong (_⋆ₑ π₂) (z .snd .snd .snd)

    pairElt : (x : fst (∫ᴾ ℓ X .F-ob Γ)) (y : fst (∫ᴾ ℓ Y .F-ob Γ))
      → fst (∫ᴾ ℓ XY .F-ob Γ)
    pairElt x y =
      ⟨ x .fst , y .fst ⟩
      , ((⟨ x .fst , y .fst ⟩ , x , sym ×β₁) , refl)
      , ((⟨ x .fst , y .fst ⟩ , y , sym ×β₂) , refl)

    pairElt-η : (z : fst (∫ᴾ ℓ XY .F-ob Γ)) {x : fst (∫ᴾ ℓ X .F-ob Γ)}
      {y : fst (∫ᴾ ℓ Y .F-ob Γ)} → cX z ≡ x → cY z ≡ y → z ≡ pairElt x y
    pairElt-η z {x} {y} p q = ΣPathP (base
      , ΣPathP
        ( FibPathPPsh ℓ base (ΣPathP (z .snd .fst .snd ∙ base
            , FibPathPPsh ℓ (cong (_⋆ₑ π₁) (z .snd .fst .snd ∙ base)) p))
        , FibPathPPsh ℓ base (ΣPathP (z .snd .snd .snd ∙ base
            , FibPathPPsh ℓ (cong (_⋆ₑ π₂) (z .snd .snd .snd ∙ base)) q))))
      where
      base : z .fst ≡ ⟨ x .fst , y .fst ⟩
      base = ×η
        ∙ cong₂ ⟨_,_⟩ (sym (eX z) ∙ cong fst p) (sym (eY z) ∙ cong fst q)

  reflect : ∀ A → GL.Hom[ idₑ ][ Ne[ A ] , Gl A ]
  reify : ∀ A → GL.Hom[ idₑ ][ Gl A , Nf[ A ] ]

  reflect (↑ o) = mkPsh ℓ {h = N ⟪ idₑ ⟫} {P = Ne[ ↑ o ]}
    {Q = Gl (↑ o)}
    ( (λ Γ z → (z .fst , ne (z .snd .fst) , z .snd .snd)
        , sym (⋆ₑIdR (z .fst)))
    , λ ρ → funExt λ z → ΣPathP (refl
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))
  reflect ⊤ = GL.reind⟨ sym (⊤η idₑ) ⟩ (Motive.termᴰ.introᴰ tt)
  reflect (A × B) = GL.reind⟨ cong₂ ⟨_,_⟩ (⋆ₑIdR _ ∙ sym (⋆ₑIdL _))
      (⋆ₑIdR _ ∙ sym (⋆ₑIdL _)) ∙ sym ×η ⟩
    (Motive.bpᴰ.introᴰ
      (fstNe Q GL.⋆ᴰ reflect A , sndNe Q GL.⋆ᴰ reflect B))
  reflect (A ⇒ B) = GL.reind⟨ cong λ-_ (⋆ₑIdR _
      ∙ cong (_⋆ₑ eval) (cong₂ ⟨_,_⟩ (sym (⋆ₑIdR π₁)) (⋆ₑIdR π₂)))
      ∙ sym (λη idₑ) ⟩
    (Motive.λᴰ ((Motive.bpᴰ.introᴰ
      (Motive.bpᴰ.πᴰ₁ , Motive.bpᴰ.πᴰ₂ GL.⋆ᴰ reify A)
      GL.⋆ᴰ appNe Q) GL.⋆ᴰ reflect B))

  reify (↑ o) = mkPsh ℓ {h = N ⟪ idₑ ⟫} {P = Gl (↑ o)}
    {Q = Nf[ ↑ o ]}
    ( (λ Γ z → (z .fst , z .snd .fst , z .snd .snd) , sym (⋆ₑIdR (z .fst)))
    , λ ρ → funExt λ z → ΣPathP (refl
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))
  reify ⊤ = mkPsh ℓ {h = N ⟪ idₑ ⟫} {P = Gl ⊤}
    {Q = Nf[ ⊤ ]}
    ( (λ Γ z → (z .fst , unit , sym (⊤η _)) , sym (⋆ₑIdR (z .fst)))
    , λ ρ → funExt λ z → ΣPathP (refl
        , ΣPathPProp (λ _ → isSetExpr _ _) refl))
  reify (A × B) = mkPsh ℓ {h = N ⟪ idₑ ⟫} {P = Gl (A × B)}
    {Q = Nf[ A × B ]}
    ( (λ Γ z → (z .fst
        , pair (nfOf (reify A) (cX (Gl A) (Gl B) z))
            (nfOf (reify B) (cY (Gl A) (Gl B) z))
        , cong₂ ⟨_,_⟩
            (nfOf≡ (reify A) (cX (Gl A) (Gl B) z) ∙ eX (Gl A) (Gl B) z)
            (nfOf≡ (reify B) (cY (Gl A) (Gl B) z) ∙ eY (Gl A) (Gl B) z)
          ∙ sym ×η)
        , sym (⋆ₑIdR (z .fst)))
    , λ ρ → funExt λ z → ΣPathP (refl
        , ΣPathPProp (λ _ → isSetExpr _ _)
            (cong₂ pair (nfOf-nat (reify A) ρ (cX (Gl A) (Gl B) z))
              (nfOf-nat (reify B) ρ (cY (Gl A) (Gl B) z)))))
  reify (A ⇒ B) = mkPsh ℓ {h = N ⟪ idₑ ⟫} {P = Gl (A ⇒ B)}
    {Q = Nf[ A ⇒ B ]}
    ( (λ Γ z → (z .fst
        , lam (nfOf (reify B) (appGl .fst .N-ob (Γ × (↑ A)) (argElt z)))
        , body≡ z)
        , sym (⋆ₑIdR (z .fst)))
    , λ ρ → funExt λ z → ΣPathP (refl
        , ΣPathPProp (λ _ → isSetExpr _ _) (cong lam (nat ρ z))))
    where
    GlAB = Gl (A ⇒ B)
    AppDom = Motive.bpᴰ GlAB (Gl A) .fst
    appGl : GL.Hom[ eval ][ AppDom , Gl B ]
    appGl = Motive.appᴰ {A} {B} {Gl A} {Gl B}
    module _ {Γ} where
      varElt : fst (∫ᴾ ℓ Ne[ A ] .F-ob (Γ × (↑ A)))
      varElt = π₂ , var (vz Q) , refl
      varGl : fst (∫ᴾ ℓ (Gl A) .F-ob (Γ × (↑ A)))
      varGl = reflect A .fst .N-ob (Γ × (↑ A)) varElt
      module _ (z : fst (∫ᴾ ℓ GlAB .F-ob Γ)) where
        wkElt : fst (∫ᴾ ℓ GlAB .F-ob (Γ × (↑ A)))
        wkElt = ∫ᴾ ℓ GlAB .F-hom (wkRen Q A) z
        argElt : fst (∫ᴾ ℓ AppDom .F-ob (Γ × (↑ A)))
        argElt = pairElt GlAB (Gl A) wkElt varGl
        body≡ : λ- (⌈_⌉ Q
          (nfOf (reify B) (appGl .fst .N-ob (Γ × (↑ A)) argElt))) ≡ z .fst
        body≡ = cong λ-_
            ( nfOf≡ (reify B) (appGl .fst .N-ob (Γ × (↑ A)) argElt)
            ∙ tri≡ {f = eval} {P = AppDom} {P' = Gl B} appGl argElt
            ∙ cong (_⋆ₑ eval) (cong₂ ⟨_,_⟩
                refl
                (tri≡ {f = idₑ} {P = Ne[ A ]} {P' = Gl A}
                  (reflect A) varElt
                  ∙ ⋆ₑIdR _)))
          ∙ sym (λη (z .fst))
    module _ {Δ Γ} (ρ : R [ Δ , Γ ]) where
      private
        ρ⁺ = extendRenaming Q A ρ
      varEq : ∫ᴾ ℓ Ne[ A ] .F-hom ρ⁺ (varElt {Γ}) ≡ varElt {Δ}
      varEq = ΣPathP (×β₂ , ΣPathPProp (λ _ → isSetExpr _ _)
        (cong var (ren-extend-vz Q A ρ)))
      varGlEq : ∫ᴾ ℓ (Gl A) .F-hom ρ⁺ (varGl {Γ}) ≡ varGl {Δ}
      varGlEq = sym (hom-nat {f = idₑ} {P = Ne[ A ]} {P' = Gl A}
          (reflect A) (varElt {Γ}) ρ⁺)
        ∙ cong (reflect A .fst .N-ob (Δ × (↑ A))) varEq
      module _ (z : fst (∫ᴾ ℓ GlAB .F-ob Γ)) where
        wkEq : ∫ᴾ ℓ GlAB .F-hom ρ⁺ (wkElt z) ≡ wkElt (∫ᴾ ℓ GlAB .F-hom ρ z)
        wkEq = sym (funExt⁻ (∫ᴾ ℓ GlAB .F-seq _ _) z)
          ∙ cong (λ σ → ∫ᴾ ℓ GlAB .F-hom σ z) (weakening-natural Q A ρ)
          ∙ funExt⁻ (∫ᴾ ℓ GlAB .F-seq _ _) z
        argEq : argElt (∫ᴾ ℓ GlAB .F-hom ρ z)
          ≡ ∫ᴾ ℓ AppDom .F-hom ρ⁺ (argElt z)
        argEq = sym (pairElt-η GlAB (Gl A)
          (∫ᴾ ℓ AppDom .F-hom ρ⁺ (argElt z)) wkEq varGlEq)
        bnat₁ : appGl .fst .N-ob (Δ × (↑ A)) (∫ᴾ ℓ AppDom .F-hom ρ⁺ (argElt z))
          ≡ ∫ᴾ ℓ (Gl B) .F-hom ρ⁺ (appGl .fst .N-ob (Γ × (↑ A)) (argElt z))
        bnat₁ = hom-nat {f = eval} {P = AppDom} {P' = Gl B}
          appGl (argElt z) ρ⁺
        nat : nfOf (reify B)
            (appGl .fst .N-ob (Δ × (↑ A)) (argElt (∫ᴾ ℓ GlAB .F-hom ρ z)))
          ≡ renNf Q ρ⁺
            (nfOf (reify B) (appGl .fst .N-ob (Γ × (↑ A)) (argElt z)))
        nat = cong (nfOf {B} {Gl B} (reify B))
            (cong (appGl .fst .N-ob (Δ × (↑ A))) argEq ∙ bnat₁)
          ∙ nfOf-nat {B} {Gl B} (reify B) ρ⁺
              (appGl .fst .N-ob (Γ × (↑ A)) (argElt z))
