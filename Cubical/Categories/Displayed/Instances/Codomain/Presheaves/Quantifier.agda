{-# OPTIONS --lossy-unification #-}
module
  Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Quantifier where

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
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Closed
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

private
  variable
    ℓC ℓC' : Level

open Functor
open NatTrans
open UniversalElement

module _ {C : Category ℓC ℓC'} (ℓ₀ : Level) where
  private
    ℓ = ℓ-max (ℓ-max ℓC ℓC') ℓ₀
    module C = Category C
    module PSH = Category (PSH {C = C} ℓ)
    module PSHCod = Categoryᴰ (PSHCod {C = C} ℓ)
    _×P_ : Presheaf C ℓ → Presheaf C ℓ → Presheaf C ℓ
    P ×P Q = ×𝓟 C ℓ (P , Q) .vertex

  module _ {Γ A : Presheaf C ℓ} (Aᴰ : Presheafᴰ (Γ ×P A) (Unitᴰ C) ℓ) where
    private
      module Γ = PresheafNotation Γ
      module A = PresheafNotation A
      module ΓA = PresheafNotation (Γ ×P A)

    ∀Fun : ∀ Θ → Γ.p[ Θ ] → Type ℓ
    ∀Fun Θ γ = ∀ {Δ} (ρ : C [ Δ , Θ ]) (x : A.p[ Δ ])
      → FibPsh ℓ Aᴰ Δ (ρ Γ.⋆ γ , x)

    ∀Nat : ∀ {Θ γ} → ∀Fun Θ γ → Type ℓ
    ∀Nat {γ = γ} G = ∀ {Δ Δ'} (σ : C [ Δ' , Δ ]) ρ x
      → G (σ C.⋆ ρ) (σ A.⋆ x)
        ≡ FibᴰPsh ℓ Aᴰ .F-hom (σ , tt , ΣPathP (sym (Γ.⋆Assoc σ ρ γ) , refl))
            (G ρ x)

    isProp∀Nat : ∀ {Θ γ} (G : ∀Fun Θ γ) → isProp (∀Nat G)
    isProp∀Nat G = isPropImplicitΠ2 λ _ Δ' → isPropΠ3 λ _ _ _ →
      isSetFibPsh ℓ Aᴰ Δ' _ _ _

    retarget : ∀ {Δ} {p q : ΓA.p[ Δ ]} → FibPsh ℓ Aᴰ Δ p → p ≡ q
      → FibPsh ℓ Aᴰ Δ q
    retarget u e = u .fst , u .snd ∙ e

    ∀ᴾ : Presheafᴰ Γ (Unitᴰ C) ℓ
    ∀ᴾ .F-ob (Θ , _ , γ) = Σ (∀Fun Θ γ) ∀Nat
      , isSetΣ
          (isSetImplicitΠ λ Δ → isSetΠ2 λ _ x → isSetFibPsh ℓ Aᴰ Δ _)
          (λ G → isProp→isSet (isProp∀Nat G))
    ∀ᴾ .F-hom {x = _ , _ , γ} (ρ , _ , e) G .fst σ x =
      retarget (G .fst (σ C.⋆ ρ) x)
        (ΣPathP (Γ.⋆Assoc σ ρ γ ∙ cong (σ Γ.⋆_) e , refl))
    ∀ᴾ .F-hom {x = _ , _ , γ} (ρ , _ , e) G .snd σ' σ x =
      FibPathPPsh ℓ refl
        ( cong (λ r → G .fst r (σ' A.⋆ x) .fst) (C.⋆Assoc σ' σ ρ)
        ∙ cong fst (G .snd σ' (σ C.⋆ ρ) x))
    ∀ᴾ .F-id = funExt λ G → ΣPathPProp isProp∀Nat
      (implicitFunExt λ {Δ} → funExt λ σ → funExt λ x →
        FibPathPPsh ℓ refl (cong (λ r → G .fst r x .fst) (C.⋆IdR σ)))
    ∀ᴾ .F-seq g g' = funExt λ G → ΣPathPProp isProp∀Nat
      (implicitFunExt λ {Δ} → funExt λ σ → funExt λ x →
        FibPathPPsh ℓ refl
          (cong (λ r → G .fst r x .fst) (sym (C.⋆Assoc σ (g' .fst) (g .fst)))))

    private
      Pull∀ = Pull (×𝓟 C ℓ (Γ , A) .element .fst) ∀ᴾ
      ∀Spec = ∀Pshⱽ (PSHCod ℓ) A (λ X → ×𝓟 C ℓ (X , A))
        (λ X yᴰ → isFibrationPSHCod yᴰ (X ×P A) (×𝓟 C ℓ (X , A) .element .fst))
        Aᴰ

    instᴾ₀ : PSHCod.Hom[ PSH.id ][ Pull∀ , Aᴰ ]
    instᴾ₀ = mkPsh ℓ {P = Pull∀} {Q = Aᴰ}
      ( (λ Θ z → retarget (z .snd .fst .snd .fst C.id (z .fst .snd))
          (ΣPathP (Γ.⋆IdL _ ∙ z .snd .snd , refl)))
      , λ ρ → funExt λ z →
          cong (λ r → z .snd .fst .snd .fst r (ρ A.⋆ z .fst .snd) .fst)
            (C.⋆IdL ρ ∙ sym (C.⋆IdR ρ))
          ∙ cong fst (z .snd .fst .snd .snd ρ C.id (z .fst .snd)))

    elt : PSHCod.Hom[ BinProductWithF (PSH {C = C} ℓ) (λ X → ×𝓟 C ℓ (X , A))
      ⟪ PSH.id ⟫ ][ Pull∀ , Aᴰ ]
    elt = ChosenReind.reind⟨_⟩ (PSHCodReind ℓ) (makeNatTransPath refl) instᴾ₀

    module _ {Δ : Presheaf C ℓ} {γ : PSH.Hom[ Δ , Γ ]} {c : Presheafᴰ Δ (Unitᴰ
      C) ℓ} where
      private
        module D = PresheafNotation Δ
        Fγ = BinProductWithF (PSH {C = C} ℓ) (λ X → ×𝓟 C ℓ (X , A)) ⟪ γ ⟫
        Pc = Pull (×𝓟 C ℓ (Δ , A) .element .fst) c

      module _ (g : PSHCod.Hom[ Fγ ][ Pc , Aᴰ ]) where
        private
          wz : ∀ {Θ} (z : ⟨ ∫ᴾ ℓ c .F-ob Θ ⟩) {Δ'} (ρ : C [ Δ' , Θ ])
            (x : A.p[ Δ' ]) → ⟨ ∫ᴾ ℓ Pc .F-ob Δ' ⟩
          wz z ρ x = (ρ D.⋆ z .fst , x) , ∫ᴾ ℓ c .F-hom ρ z , refl

          module _ {Θ} (z : ⟨ ∫ᴾ ℓ c .F-ob Θ ⟩) where
            genG : ∀Fun Θ (γ .N-ob Θ (z .fst))
            genG ρ x = retarget (ptPsh ℓ g .fst _ (wz z ρ x))
              (ΣPathP (funExt⁻ (γ .N-hom ρ) (z .fst) , refl))

            genNat : ∀Nat genG
            genNat {Δ'' } {Δ'} σ ρ x = FibPathPPsh ℓ refl
              ( cong (g .fst .N-ob Δ')
                  (ΣPathP
                    ( ΣPathP (D.⋆Assoc σ ρ (z .fst) , refl)
                    , FibPathPPsh ℓ (D.⋆Assoc σ ρ (z .fst))
                        (funExt⁻ (∫ᴾ ℓ c .F-seq ρ σ) z)))
              ∙ funExt⁻ (g .fst .N-hom σ) (wz z ρ x))

        genPsh : PSHCod.Hom[ γ ][ c , ∀ᴾ ]
        genPsh = mkPsh ℓ {P = c} {Q = ∀ᴾ}
          ( (λ Θ z → (γ .N-ob Θ (z .fst) , genG z , genNat z) , refl)
          , λ {Θ} {Θ'} ρ → funExt λ z → ΣPathP
              ( funExt⁻ (γ .N-hom ρ) (z .fst)
              , ΣPathPProp isProp∀Nat λ i {Δ'} σ x →
                  FibPathPPsh ℓ
                    (λ j → σ Γ.⋆ funExt⁻ (γ .N-hom ρ) (z .fst) j , x)
                    {u = genG (∫ᴾ ℓ c .F-hom ρ z) σ x}
                    {u' = ∀ᴾ .F-hom (ρ , tt , refl) (genG z , genNat z)
                      .fst σ x}
                    (cong (g .fst .N-ob Δ')
                      (ΣPathP
                        ( ΣPathP (sym (D.⋆Assoc σ ρ (z .fst)) , refl)
                        , FibPathPPsh ℓ (sym (D.⋆Assoc σ ρ (z .fst)))
                            (sym (funExt⁻ (∫ᴾ ℓ c .F-seq ρ σ) z)))))
                    i))

      newN : PSHCod.Hom[ γ ][ c , ∀ᴾ ]
        → ∀ Θ → ⟨ ∫ᴾ ℓ Pc .F-ob Θ ⟩ → ⟨ ∫ᴾ ℓ Aᴰ .F-ob Θ ⟩
      newN h Θ w =
        h .fst .N-ob Θ (w .snd .fst) .snd .fst C.id (w .fst .snd) .fst

      module _ (h : PSHCod.Hom[ γ ][ c , ∀ᴾ ]) where
        inst≡N :
          yoRecⱽ ∀Spec elt .PshHom.N-ob (Δ , c , γ) h .fst .N-ob ≡ newN h
        inst≡N =
          reind-fstPsh {P = Pc} {Q = Aᴰ} _ _
          ∙ cong (λ t Θ w → t Θ w .snd .fst C.id (w .fst .snd) .fst)
              (reind-fstPsh {P = Pc} {Q = ∀ᴾ} _ _)

        instᴾ⟨_⟩ : PSHCod.Hom[ Fγ ][ Pc , Aᴰ ]
        instᴾ⟨_⟩ = improvePsh ℓ (yoRecⱽ ∀Spec elt .PshHom.N-ob (Δ , c , γ) h)
          (newN h) inst≡N

        inst≡ : yoRecⱽ ∀Spec elt .PshHom.N-ob (Δ , c , γ) h ≡ instᴾ⟨_⟩
        inst≡ = improveᴾ≡ ℓ (yoRecⱽ ∀Spec elt .PshHom.N-ob (Δ , c , γ) h)
          (newN h) inst≡N

      inst-gen : (g : PSHCod.Hom[ Fγ ][ Pc , Aᴰ ]) → instᴾ⟨ genPsh g ⟩ ≡ g
      inst-gen g = Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath
        (funExt λ Θ → funExt λ w → cong (g .fst .N-ob Θ)
          (ΣPathP
            ( ΣPathP (D.⋆IdL _ ∙ w .snd .snd , refl)
            , FibPathPPsh ℓ (D.⋆IdL _ ∙ w .snd .snd)
                (funExt⁻ (∫ᴾ ℓ c .F-id) (w .snd .fst))))))

      gen-inst : (h : PSHCod.Hom[ γ ][ c , ∀ᴾ ]) → genPsh instᴾ⟨ h ⟩ ≡ h
      gen-inst h = Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath
        (funExt λ Θ → funExt λ z → ΣPathP
          ( b Θ z
          , ΣPathPProp isProp∀Nat λ i {Δ'} σ x →
              FibPathPPsh ℓ (λ j → σ Γ.⋆ b Θ z j , x)
                {u = genPsh instᴾ⟨ h ⟩ .fst .N-ob Θ z .snd .fst σ x}
                {u' = h .fst .N-ob Θ z .snd .fst σ x}
                ( cong (λ t → t .snd .fst C.id x .fst)
                    (funExt⁻ (h .fst .N-hom σ) z)
                ∙ cong (λ r → h .fst .N-ob Θ z .snd .fst r x .fst)
                    (C.⋆IdL σ))
                i)))
        where
        b : ∀ Θ z → γ .N-ob Θ (z .fst) ≡ h .fst .N-ob Θ z .fst
        b Θ z i = h .snd (~ i) .N-ob Θ z


    ∀univ : isPshIso (yoRecⱽ ∀Spec elt)
    ∀univ (Δ , c , γ) .fst = genPsh {Δ = Δ} {γ = γ} {c = c}
    ∀univ (Δ , c , γ) .snd .fst g =
      inst≡ {Δ = Δ} {γ = γ} {c = c} (genPsh g) ∙ inst-gen g
    ∀univ (Δ , c , γ) .snd .snd h =
      cong genPsh (inst≡ {Δ = Δ} {γ = γ} {c = c} h) ∙ gen-inst h

    ∀Iso₀ : PshIsoⱽ (PSHCod ℓ [-][-, ∀ᴾ ]) ∀Spec
    ∀Iso₀ = pshiso (yoRecⱽ ∀Spec elt) ∀univ

    instSingl : singl (∀Iso₀ .PshIso.trans .PshHom.N-ob)
    instSingl .fst (Δ , c , γ) h = instᴾ⟨ h ⟩
    instSingl .snd i (Δ , c , γ) h = inst≡ h i

    genSingl : singl (invPshIso ∀Iso₀ .PshIso.trans .PshHom.N-ob)
    genSingl .fst (Δ , c , γ) = genPsh
    genSingl .snd i (Δ , c , γ) = genPsh

    ∀PSHCod : UniversalQuantifier (PSHCod ℓ) A (λ X → ×𝓟 C ℓ (X , A))
      (λ X yᴰ → isFibrationPSHCod yᴰ (X ×P A) (×𝓟 C ℓ (X , A) .element .fst))
      Aᴰ
    ∀PSHCod = ∀ᴾ , improvePshIso ∀Iso₀ instSingl genSingl

  UniversalQuantifiersPSHCod :
    UniversalQuantifiers (PSHCod {C = C} ℓ) (×𝓟 C ℓ) isFibrationPSHCod
  UniversalQuantifiersPSHCod Aᴰ = ∀PSHCod Aᴰ

  module _ {Γ A Δ : Presheaf C ℓ}
    {Aᴰ : Presheafᴰ (×𝓟 C ℓ (Γ , A) .vertex) (Unitᴰ C) ℓ} {γ : PSH.Hom[ Δ , Γ ]}
    {c : Presheafᴰ Δ (Unitᴰ C) ℓ} where
    private
      module D = PresheafNotation Δ
      module A = PresheafNotation A
      Pc = Pull (×𝓟 C ℓ (Δ , A) .element .fst) c

    _ : (h : PSHCod.Hom[ γ ][ c , ∀ᴾ Aᴰ ]) (Θ : C.ob) (w : ⟨ ∫ᴾ ℓ Pc .F-ob Θ ⟩)
      → UniversalQuantifiersPSHCod Aᴰ .snd .PshIso.trans .PshHom.N-ob
          (Δ , c , γ) h .fst .N-ob Θ w
        ≡ h .fst .N-ob Θ (w .snd .fst) .snd .fst C.id (w .fst .snd) .fst
    _ = λ h Θ w → refl

    _ : (g : PSHCod.Hom[ BinProductWithF (PSH {C = C} ℓ)
           (λ X → ×𝓟 C ℓ (X , A)) ⟪ γ ⟫ ][ Pc , Aᴰ ])
      (Θ : C.ob) (z : ⟨ ∫ᴾ ℓ c .F-ob Θ ⟩) {Δ' : C.ob} (σ : C [ Δ' , Θ ])
      (x : A.p[ Δ' ])
      → invPshIso (UniversalQuantifiersPSHCod Aᴰ .snd) .PshIso.trans
          .PshHom.N-ob (Δ , c , γ) g .fst .N-ob Θ z .snd .fst σ x .fst
        ≡ g .fst .N-ob Δ' ((σ D.⋆ z .fst , x) , ∫ᴾ ℓ c .F-hom σ z , refl)
    _ = λ g Θ z σ x → refl

PSHCodCCCⱽ : {C : Category ℓC ℓC'} (ℓ₀ : Level)
  → CartesianClosedCategoryⱽ (𝓟-CC C ℓ₀) _ _
PSHCodCCCⱽ ℓ₀ .CartesianClosedCategoryⱽ.CCⱽ =
  cartesiancategoryⱽ (PSHCod _) TerminalsⱽPSHCod BinProductsⱽPSHCod isFibrationPSHCod
PSHCodCCCⱽ ℓ₀ .CartesianClosedCategoryⱽ.lrⱽ = AllLRⱽPSHCod
PSHCodCCCⱽ ℓ₀ .CartesianClosedCategoryⱽ.expⱽ = ExponentialsⱽPSHCod ℓ₀
PSHCodCCCⱽ ℓ₀ .CartesianClosedCategoryⱽ.forallⱽ = UniversalQuantifiersPSHCod ℓ₀
