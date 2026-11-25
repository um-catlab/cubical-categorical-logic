{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.TotalCategory using (∫C)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.ChangeOfObjects
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Base

module _ {ℓO ℓA ℓE ℓEA} (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T
    MOD = MODEL T L
    module MOD = Category MOD
    module Mᴰ = Categoryᴰ (ModelCBPVᴰ T)

  ∫MC : Category (ℓ-suc L) L
  ∫MC = ∫C (ModelCBPV T .fst)

  private
    module Tr = Categoryᴰ (Codomain ∫MC)

  projHomo : ∀ {B : MOD.ob} (Bᴰ : Mᴰ.ob[ 𝒞 , B ])
    → MOD [ ∫Model {M = B} Bᴰ , B ]
  projHomo Bᴰ .fst = fst
  projHomo Bᴰ .snd op γ op⟨γ⟩ p = cong fst p

  cmp : ∀ {c} → Mᴰ.ob[ c ] → Tr.ob[ c ]
  cmp {𝒱 , A} P .fst =
    𝒱 , (Σ ⟨ A ⟩ λ a → ⟨ P a ⟩) , isSetΣ (A .snd) λ a → P a .snd
  cmp {𝒱 , A} P .snd = ı tt , fst
  cmp {𝒞 , B} Bᴰ .fst = 𝒞 , ∫Model {M = B} Bᴰ
  cmp {𝒞 , B} Bᴰ .snd = ı tt , projHomo Bᴰ

  ModelCod : CBPVCatᴰ (ModelCBPV T .fst) (ℓ-suc L) L
  ModelCod = ChangeOfObjectsᴰ (Codomain ∫MC) cmp

  ModelCodReind : ChosenReind ModelCod
  ModelCodReind = ChangeOfObjectsReind (Codomain ∫MC) cmp (CodomainReind ∫MC)

  private
    module Tᴰ = Categoryᴰ ModelCod
    module Tᴰop = Categoryᴰ (ModelCod ^opᴰᴰ)
    module Tᴰ^op = Categoryᴰ (ModelCod ^opᴰ)

  module _ {A : hSet L} {B : MOD.ob} (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
    (Bᴰ : Mᴰ.ob[ 𝒞 , B ]) where
    private
      fᵁ : ∫MC [ (𝒱 , A) , (𝒞 , B) ]
      fᵁ = ı tt , f

    Pullᵁ : Mᴰ.ob[ 𝒱 , A ]
    Pullᵁ a = Fibᴰ L (Bᴰ .fst) (f a)

    pullᵁπ : Tᴰ.Hom[ fᵁ ][ Pullᵁ , Bᴰ ]
    pullᵁπ .fst = ı tt , λ z → z .snd .fst
    pullᵁπ .snd i = ı tt , λ z → z .snd .snd i

    private
      intro : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fᵁ ][ c , Bᴰ ] → Tᴰ.Hom[ k ][ c , Pullᵁ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {k = ı () , _}

      intro-β : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fᵁ ][ c , Bᴰ ])
        → intro gᴰ Tᴰ.⋆ᴰ pullᵁπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl refl
      intro-β {𝒞 , W} {k = ı () , _}

      intro-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullᵁ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullᵁπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → B .fst .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = ı () , _}

    ModelCod-Uⱽ : CartesianLift ModelCod fᵁ Bᴰ
    ModelCod-Uⱽ = mkCartesianLift ModelCod pullᵁπ intro intro-β intro-η

  module _ {A : hSet L} {B : MOD.ob} (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
    (Aᴰ : Mᴰ.ob[ 𝒱 , A ]) where
    private
      ΣA = Σ ⟨ A ⟩ λ a → ⟨ Aᴰ a ⟩

      fᶠ : ∫C (ModelCBPV T .fst ^opᴰ) [ (𝒞 , B) , (𝒱 , A) ]
      fᶠ = ı tt , f

    module PushᶠNotation where
      ∫Aᴰ : hSet L
      ∫Aᴰ = ΣA , isSetΣ (A .snd) λ a → Aᴰ a .snd

      Free∫ : MOD.ob
      Free∫ = FreeModel ΣA

      h : MOD [ Free∫ , B ]
      h = recFM ΣA B (λ x → f (x .fst))

    open PushᶠNotation

    Pushᶠ : Mᴰ.ob[ 𝒞 , B ]
    Pushᶠ = FiberModelᴰ {M = Free∫} {N = B} h

    pushᶠσ : Tᴰop.Hom[ fᶠ ][ Pushᶠ , Aᴰ ]
    pushᶠσ .fst = ı tt , λ z → f (z .fst) , var z , refl
    pushᶠσ .snd = refl

    private
      module _ {C : MOD.ob} (Cᴰ : Mᴰ.ob[ 𝒞 , C ])
        (g : ΣA → ⟨ ∫Model {M = C} Cᴰ .fst ⟩) where
        outM : MOD [ Free∫ , ∫Model {M = C} Cᴰ ]
        outM = recFM ΣA (∫Model {M = C} Cᴰ) g

        outF : ⟨ ∫Model {M = B} Pushᶠ .fst ⟩ → ⟨ ∫Model {M = C} Cᴰ .fst ⟩
        outF x = outM .fst (x .snd .fst)

        outH : MOD [ ∫Model {M = B} Pushᶠ , ∫Model {M = C} Cᴰ ]
        outH .fst = outF
        outH .snd op γ op⟨γ⟩ p = cong outF p

        out-sq : (ψ : MOD [ B , C ])
          → (∀ z → g z .fst ≡ ψ .fst (f (z .fst)))
          → ∀ x → outF x .fst ≡ ψ .fst (x .fst)
        out-sq ψ sq x =
          funExt⁻ lem (x .snd .fst) ∙ cong (ψ .fst) (x .snd .snd)
          where
          φ₁ φ₂ : MOD [ Free∫ , C ]
          φ₁ = outM ⋆⟨ MOD ⟩ projHomo Cᴰ
          φ₂ = h ⋆⟨ MOD ⟩ ψ
          lem : φ₁ .fst ≡ φ₂ .fst
          lem = recFM-uniq ΣA C φ₁
            ∙ cong (λ k → recFM ΣA C k .fst) (funExt sq)
            ∙ sym (recFM-uniq ΣA C φ₂)

      ιF : ⟨ Free∫ .fst ⟩ → ⟨ ∫Model {M = B} Pushᶠ .fst ⟩
      ιF t = h .fst t , t , refl

      ιH : MOD [ Free∫ , ∫Model {M = B} Pushᶠ ]
      ιH .fst = ιF
      ιH .snd op γ op⟨γ⟩ p =
        ΣPathP (refl , ΣPathP (refl , B .fst .snd _ _ _ _)) ∙ cong ιF p

      η-pt : ∀ {C : MOD.ob} (Cᴰ : Mᴰ.ob[ 𝒞 , C ])
        (k : MOD [ ∫Model {M = B} Pushᶠ , ∫Model {M = C} Cᴰ ]) x
        → k .fst x ≡ outF Cᴰ (λ z → k .fst (pushᶠσ .fst .snd z)) x
      η-pt Cᴰ k x = cong (k .fst) xP
        ∙ funExt⁻ (recFM-uniq ΣA (∫Model Cᴰ) (ιH ⋆⟨ MOD ⟩ k)) (x .snd .fst)
        where
        xP : x ≡ ιF (x .snd .fst)
        xP i = x .snd .snd (~ i) , x .snd .fst , λ j → x .snd .snd (~ i ∧ j)

      out : ∀ {z} {c : Mᴰ.ob[ z ]}
        {g : ∫C (ModelCBPV T .fst ^opᴰ) [ z , (𝒞 , B) ]}
        → Tᴰop.Hom[ g ⋆⟨ ∫C (ModelCBPV T .fst ^opᴰ) ⟩ fᶠ ][ c , Aᴰ ]
        → Tᴰop.Hom[ g ][ c , Pushᶠ ]
      out {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ .fst = ı tt , outH Cᴰ (gᴰ .fst .snd)
      out {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ .snd = ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _
          (funExt (out-sq Cᴰ (gᴰ .fst .snd) ψ λ z i → gᴰ .snd i .snd z)))
      out {𝒱 , _} {g = ı () , _}

      out-β : ∀ {z} {c : Mᴰ.ob[ z ]}
        {g : ∫C (ModelCBPV T .fst ^opᴰ) [ z , (𝒞 , B) ]}
        (gᴰ : Tᴰop.Hom[ g ⋆⟨ ∫C (ModelCBPV T .fst ^opᴰ) ⟩ fᶠ ][
          c , Aᴰ ])
        → out gᴰ Tᴰop.⋆ᴰ pushᶠσ ≡ gᴰ
      out-β {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ = Codomain≡ ∫MC refl refl
      out-β {𝒱 , _} {g = ı () , _}

      out-η : ∀ {z} {c : Mᴰ.ob[ z ]}
        {g : ∫C (ModelCBPV T .fst ^opᴰ) [ z , (𝒞 , B) ]}
        (hᴰ : Tᴰop.Hom[ g ][ c , Pushᶠ ])
        → out (hᴰ Tᴰop.⋆ᴰ pushᶠσ) ≡ hᴰ
      out-η {𝒞 , C} {Cᴰ} {_ , ψ} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _ (funExt λ x →
          sym (η-pt Cᴰ (hᴰ .fst .snd) x))))
      out-η {𝒱 , _} {g = ı () , _}

    ModelCod-Fⱽ : CartesianLift (ModelCod ^opᴰᴰ) fᶠ Aᴰ
    ModelCod-Fⱽ = mkCartesianLift (ModelCod ^opᴰᴰ) pushᶠσ out out-β out-η

  ModelCodⱽ : MultCBPVCatⱽ (ModelCBPV T .fst) (ℓ-suc L) L
  ModelCodⱽ .fst = ModelCod
  ModelCodⱽ .snd .fst f Bᴰ = ModelCod-Uⱽ f Bᴰ
  ModelCodⱽ .snd .snd f Aᴰ = ModelCod-Fⱽ f Aᴰ

  ModelCodModel : ModelEnrichmentᴰ T (ModelCBPVModel T) ModelCod
  ModelCodModel .fst {A} {B} Aᴰ Bᴰ = eff , effEq
    where
    ∫Bop = ∫Model {M = B} Bᴰ .snd .fst
    P = PowerModel ⟨ A ⟩ B
    Hom = λ (M : ⟨ A ⟩ → ⟨ B .fst ⟩)
      → Tᴰ.Hom[_][_,_] {x = 𝒱 , A} {y = 𝒞 , B} (ı tt , M) Aᴰ Bᴰ
    eff : AlgebraᴰWithCarrier (Model→Algebra P) Hom
    eff op γ γᴰ op⟨γ⟩ p .fst =
      ı tt , λ z → ∫Bop op (λ v → γᴰ v .fst .snd z)
    eff op γ γᴰ op⟨γ⟩ p .snd i = ı tt , λ z →
      ((λ j → B .snd .fst op (λ v → γᴰ v .snd j .snd z))
        ∙ (λ j → p j (z .fst))) i
    interpEff : ∀ {ℓV} {V : Type ℓV} (ρ : V → ⟨ A ⟩ → ⟨ B .fst ⟩)
      (ρᴰ : ∀ v → Hom (ρ v)) t z
      → interpᴰ (Hom , eff) ρ ρᴰ t .fst .snd z
        ≡ interp (Model→Algebra (∫Model {M = B} Bᴰ))
            (λ v → ρᴰ v .fst .snd z) t
    interpEff ρ ρᴰ (var v) z = refl
    interpEff ρ ρᴰ (app op γ) z =
      cong (∫Bop op) (funExt λ v → interpEff ρ ρᴰ (γ v) z)
    effEq : IsModelᴰ P (Hom , eff)
    effEq e ρ ρᴰ = Codomain≡ ∫MC (λ i → ı tt , P .snd .snd e ρ i)
      (ΣPathP (refl , funExt λ z →
        interpEff ρ ρᴰ (lhs e) z
        ∙ ∫Model {M = B} Bᴰ .snd .snd e (λ v → ρᴰ v .fst .snd z)
        ∙ sym (interpEff ρ ρᴰ (rhs e) z)))
  ModelCodModel .snd .fst Vᴰ _ _ _ _ _ _ pᴰ =
    Codomain≡ ∫MC refl λ i → (Vᴰ Tᴰ.⋆ᴰ pᴰ i) .fst
  ModelCodModel .snd .snd Sᴰ op _ _ _ _ _ pᴰ =
    Codomain≡ ∫MC refl
      (ΣPathP (refl , funExt λ z → Sᴰ .fst .snd .snd op _ _ refl)
      ∙ (λ i → (pᴰ i Tᴰ.⋆ᴰ Sᴰ) .fst))

  private
    instance
      ModelCodReindInst : ChosenReind ModelCod
      ModelCodReindInst = ModelCodReind

  module _ {B : MOD.ob} (a b : Modelᴰ B L) where
    private
      Aᴰ = Modelᴰ→Algebraᴰ B a
      Bᴰ = Modelᴰ→Algebraᴰ B b

      interpProd : ∀ {ℓV} {V : Type ℓV} (ρ : V → ⟨ B .fst ⟩)
        (ρᴰ : ∀ v → ⟨ a .fst (ρ v) ⟩ × ⟨ b .fst (ρ v) ⟩) t
        → interpᴰ (Aᴰ ×ⱽ Bᴰ) ρ ρᴰ t
          ≡ ( interpᴰ Aᴰ ρ (λ v → ρᴰ v .fst) t
            , interpᴰ Bᴰ ρ (λ v → ρᴰ v .snd) t)
      interpProd ρ ρᴰ (var v) = refl
      interpProd ρ ρᴰ (app op γ) = cong₂ _,_
        (cong (λ γᴰ → a .snd .fst op
            (λ v → interp (Model→Algebra B) ρ (γ v)) γᴰ
            (interp (Model→Algebra B) ρ (app op γ))
            (recFA (Model→Algebra B) ρ .snd op γ (app op γ) refl))
          (funExt λ v → cong fst (interpProd ρ ρᴰ (γ v))))
        (cong (λ γᴰ → b .snd .fst op
            (λ v → interp (Model→Algebra B) ρ (γ v)) γᴰ
            (interp (Model→Algebra B) ρ (app op γ))
            (recFA (Model→Algebra B) ρ .snd op γ (app op γ) refl))
          (funExt λ v → cong snd (interpProd ρ ρᴰ (γ v))))

    _×ᴹ_ : Modelᴰ B L
    _×ᴹ_ .fst x =
      (⟨ a .fst x ⟩ × ⟨ b .fst x ⟩) , isSet× (a .fst x .snd) (b .fst x .snd)
    _×ᴹ_ .snd .fst = (Aᴰ ×ⱽ Bᴰ) .snd
    _×ᴹ_ .snd .snd e ρ ρᴰ =
      interpProd ρ ρᴰ (lhs e)
      ◁ (λ i → a .snd .snd e ρ (λ v → ρᴰ v .fst) i
             , b .snd .snd e ρ (λ v → ρᴰ v .snd) i)
      ▷ sym (interpProd ρ ρᴰ (rhs e))

  FibM : ∀ {B : MOD.ob} (Bᴰ : Mᴰ.ob[ 𝒞 , B ]) → Mᴰ.ob[ 𝒞 , B ]
  FibM {B} Bᴰ = FiberModelᴰ {M = ∫Model {M = B} Bᴰ} {N = B} (projHomo Bᴰ)

  𝟙ᶜ : ∀ {B : MOD.ob} → Mᴰ.ob[ 𝒞 , B ]
  𝟙ᶜ .fst _ = Unit* , isSetUnit*
  𝟙ᶜ .snd .fst _ _ _ _ _ = tt*
  𝟙ᶜ .snd .snd _ _ _ = isProp→PathP (λ _ → isPropUnit*) _ _

  _×ᶜ_ : ∀ {B : MOD.ob} → Mᴰ.ob[ 𝒞 , B ] → Mᴰ.ob[ 𝒞 , B ]
    → Mᴰ.ob[ 𝒞 , B ]
  a ×ᶜ b = FibM a ×ᴹ FibM b

  module _ (X : hSet L) where
    private
      ! : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , X) ]}
        → Tᴰ.Hom[ k ][ c , 𝟙Cod {X = X} ]
      ! {𝒱 , W} {k = _ , k} = (ı tt , λ z → k (z .fst) , tt*) , refl
      ! {𝒞 , W} {k = ı () , _}

      !-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , X) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , 𝟙Cod {X = X} ]) → ! ≡ hᴰ
      !-η {𝒱 , W} {k = _ , k} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
        ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , refl)))
      !-η {𝒞 , W} {k = ı () , _}

    ModelCodValueTerminalⱽ : Terminalⱽ ModelCod (𝒱 , X)
    ModelCodValueTerminalⱽ = mkTerminalⱽ ModelCod (𝟙Cod {X = X}) ! !-η

    private
      ¡ : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ (𝒱 , X) , w ]}
        → Tᴰ.Hom[ k ][ 𝟘Cod {X = X} , c ]
      ¡ {𝒱 , W} .fst .fst = ı tt
      ¡ {𝒱 , W} .fst .snd (x , ())
      ¡ {𝒱 , W} .snd i .fst = ı tt
      ¡ {𝒱 , W} .snd i .snd (x , ())
      ¡ {𝒞 , W} .fst .fst = ı tt
      ¡ {𝒞 , W} .fst .snd (x , ())
      ¡ {𝒞 , W} .snd i .fst = ı tt
      ¡ {𝒞 , W} .snd i .snd (x , ())

      ¡-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ (𝒱 , X) , w ]}
        (hᴰ : Tᴰ.Hom[ k ][ 𝟘Cod {X = X} , c ]) → ¡ ≡ hᴰ
      ¡-η {𝒱 , W} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ { (x , ()) }))
      ¡-η {𝒞 , W} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ { (x , ()) }))

    ModelCodValueInitialⱽ : Initialⱽ ModelCod (𝒱 , X)
    ModelCodValueInitialⱽ = mkTerminalⱽ (ModelCod ^opᴰ) (𝟘Cod {X = X}) ¡ ¡-η

  module _ (B : MOD.ob) where
    private
      !H : ∀ {W} (k : MOD [ W , B ]) (c : Mᴰ.ob[ 𝒞 , W ])
        → MOD [ ∫Model {M = W} c , ∫Model {M = B} (𝟙ᶜ {B}) ]
      !H k c .fst z = k .fst (z .fst) , tt*
      !H k c .snd op γ op⟨γ⟩ p = ΣPathP (k .snd op _ _ (cong fst p) , refl)

      ! : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ][ c , 𝟙ᶜ {B} ]
      ! {𝒱 , W} {k = _ , k} = (ı tt , λ z → k (z .fst) , tt*) , refl
      ! {𝒞 , W} {c} {_ , k} = (ı tt , !H k c)
        , ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl)

      !-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , 𝟙ᶜ {B} ]) → ! ≡ hᴰ
      !-η {𝒱 , W} {k = _ , k} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
        ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , refl)))
      !-η {𝒞 , W} {k = _ , k} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _ (funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z) , refl))))

    ModelCodComputationTerminalⱽ : Terminalⱽ ModelCod (𝒞 , B)
    ModelCodComputationTerminalⱽ = mkTerminalⱽ ModelCod (𝟙ᶜ {B}) ! !-η

  module _ {X : hSet L} (a b : Mᴰ.ob[ 𝒱 , X ]) where
    private
      π₁ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        (_×Cod_ a b) a
      π₁ = (ı tt , λ z → z .snd .fst .fst)
        , λ i → ı tt , λ z → z .snd .fst .snd i
      π₂ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        (_×Cod_ a b) b
      π₂ = (ı tt , λ z → z .snd .snd .fst)
        , λ i → ı tt , λ z → z .snd .snd .snd i

      pair : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , X) ]}
        → Tᴰ.Hom[ k ][ c , a ] → Tᴰ.Hom[ k ][ c , b ]
        → Tᴰ.Hom[ k ][ c , _×Cod_ a b ]
      pair {𝒱 , W} {k = _ , k} g₁ g₂ =
        (ı tt , λ z → k (z .fst)
          , (g₁ .fst .snd z , λ i → g₁ .snd i .snd z)
          , (g₂ .fst .snd z , λ i → g₂ .snd i .snd z)) , refl
      pair {𝒞 , W} {k = ı () , _}

      pair-β : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , X) ]}
        (φ : Tᴰ.Hom[ k ][ c , a ] × Tᴰ.Hom[ k ][ c , b ])
        → ( ChosenReind.reind⟨_⟩ ModelCodReind (Category.⋆IdR ∫MC k)
                (pair (φ .fst) (φ .snd) Tᴰ.⋆ᴰ π₁)
            , ChosenReind.reind⟨_⟩ ModelCodReind (Category.⋆IdR ∫MC k)
                (pair (φ .fst) (φ .snd) Tᴰ.⋆ᴰ π₂))
          ≡ φ
      pair-β {𝒱 , W} {k = _ , k} _ =
        ≡-× (Codomain≡ ∫MC refl refl) (Codomain≡ ∫MC refl refl)
      pair-β {𝒞 , W} {k = ı () , _}

      pair-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , X) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , _×Cod_ a b ])
        → pair (ChosenReind.reind⟨_⟩ ModelCodReind (Category.⋆IdR ∫MC k)
              (hᴰ Tᴰ.⋆ᴰ π₁))
            (ChosenReind.reind⟨_⟩ ModelCodReind (Category.⋆IdR ∫MC k)
              (hᴰ Tᴰ.⋆ᴰ π₂))
          ≡ hᴰ
      pair-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z)
            , ΣPathP (FibPathP L _ refl , FibPathP L _ refl))))
      pair-η {𝒞 , W} {k = ı () , _}

    ModelCodValueProductⱽ : BinProductⱽ ModelCod a b
    ModelCodValueProductⱽ =
      mkBinProductⱽ ModelCod (_×Cod_ a b) π₁ π₂ pair pair-β pair-η

  module _ {X : hSet L} (a b : Mᴰ.ob[ 𝒱 , X ]) where
    private
      σ₁ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        a (_+Cod_ a b)
      σ₁ = (ı tt , λ z → z .fst , inl (z .snd)) , refl
      σ₂ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        b (_+Cod_ a b)
      σ₂ = (ı tt , λ z → z .fst , inr (z .snd)) , refl

      case : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ (𝒱 , X) , w ]}
        → Tᴰ.Hom[ k ][ a , c ] → Tᴰ.Hom[ k ][ b , c ]
        → Tᴰ.Hom[ k ][ _+Cod_ a b , c ]
      case {𝒱 , W} g h .fst .fst = ı tt
      case {𝒱 , W} g h .fst .snd (x , inl p) = g .fst .snd (x , p)
      case {𝒱 , W} g h .fst .snd (x , inr q) = h .fst .snd (x , q)
      case {𝒱 , W} g h .snd i .fst = ı tt
      case {𝒱 , W} g h .snd i .snd (x , inl p) = g .snd i .snd (x , p)
      case {𝒱 , W} g h .snd i .snd (x , inr q) = h .snd i .snd (x , q)
      case {𝒞 , W} g h .fst .fst = ı tt
      case {𝒞 , W} g h .fst .snd (x , inl p) = g .fst .snd (x , p)
      case {𝒞 , W} g h .fst .snd (x , inr q) = h .fst .snd (x , q)
      case {𝒞 , W} g h .snd i .fst = ı tt
      case {𝒞 , W} g h .snd i .snd (x , inl p) = g .snd i .snd (x , p)
      case {𝒞 , W} g h .snd i .snd (x , inr q) = h .snd i .snd (x , q)

    ModelCodValueCoProductⱽ : BinCoProductⱽ ModelCod a b
    ModelCodValueCoProductⱽ =
      mkBinProductⱽ (ModelCod ^opᴰ) (_+Cod_ a b) σ₁ σ₂ case
        (λ { {𝒱 , W} _ → ≡-× (Codomain≡ ∫MC refl refl) (Codomain≡ ∫MC refl refl)
           ; {𝒞 , W} _ → ≡-× (Codomain≡ ∫MC refl refl) (Codomain≡ ∫MC refl refl) })
        (λ { {𝒱 , W} hᴰ → Codomain≡ ∫MC refl (ΣPathP (refl ,
               funExt λ { (x , inl p) → refl ; (x , inr q) → refl }))
           ; {𝒞 , W} hᴰ → Codomain≡ ∫MC refl (ΣPathP (refl ,
               funExt λ { (x , inl p) → refl ; (x , inr q) → refl })) })

  module _ {B : MOD.ob} (a b : Mᴰ.ob[ 𝒞 , B ]) where
    private
      isSetB = B .fst .snd

      π₁ : Tᴰ.Hom[_][_,_] {x = 𝒞 , B} {y = 𝒞 , B} (ı tt , MOD.id)
        (a ×ᶜ b) a
      π₁ .fst = ı tt , (λ z → z .snd .fst .fst) , λ op γ op⟨γ⟩ p →
        cong (λ z → z .snd .fst .fst) p
      π₁ .snd = ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _ λ i z → z .snd .fst .snd i)

      π₂ : Tᴰ.Hom[_][_,_] {x = 𝒞 , B} {y = 𝒞 , B} (ı tt , MOD.id)
        (a ×ᶜ b) b
      π₂ .fst = ı tt , (λ z → z .snd .snd .fst) , λ op γ op⟨γ⟩ p →
        cong (λ z → z .snd .snd .fst) p
      π₂ .snd = ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _ λ i z → z .snd .snd .snd i)

      pair : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ][ c , a ] → Tᴰ.Hom[ k ][ c , b ]
        → Tᴰ.Hom[ k ][ c , a ×ᶜ b ]
      pair {𝒱 , W} {k = _ , k} g₁ g₂ =
        (ı tt , λ z → k (z .fst)
          , (g₁ .fst .snd z , λ i → g₁ .snd i .snd z)
          , (g₂ .fst .snd z , λ i → g₂ .snd i .snd z)) , refl
      pair {𝒞 , W} {c} {_ , k} g₁ g₂ .fst = ı tt , m , mH
        where
        m : ⟨ ∫Model {M = W} c .fst ⟩ → ⟨ ∫Model {M = B} (a ×ᶜ b) .fst ⟩
        m z = k .fst (z .fst)
          , (g₁ .fst .snd .fst z , λ i → g₁ .snd i .snd .fst z)
          , (g₂ .fst .snd .fst z , λ i → g₂ .snd i .snd .fst z)
        mH : isHomoSimpl (_ , ∫Model {M = W} c .snd .fst)
          (_ , ∫Model {M = B} (a ×ᶜ b) .snd .fst) m
        mH op γ op⟨γ⟩ p = ΣPathP (k .snd op _ _ (cong fst p)
          , ΣPathP
            ( ΣPathP (g₁ .fst .snd .snd op γ op⟨γ⟩ p
              , isProp→PathP (λ i → isSetB _ _) _ _)
            , ΣPathP (g₂ .fst .snd .snd op γ op⟨γ⟩ p
              , isProp→PathP (λ i → isSetB _ _) _ _)))
      pair {𝒞 , W} {k = _ , k} g₁ g₂ .snd =
        ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl)

    ModelCodComputationProductⱽ : BinProductⱽ ModelCod a b
    ModelCodComputationProductⱽ =
      mkBinProductⱽ ModelCod (a ×ᶜ b) π₁ π₂ pair
        (λ { {𝒱 , W} {g = _ , k} _ →
               ≡-× (Codomain≡ ∫MC refl refl) (Codomain≡ ∫MC refl refl)
           ; {𝒞 , W} {g = _ , k} _ → ≡-×
               (Codomain≡ ∫MC refl
                 (ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl)))
               (Codomain≡ ∫MC refl
                 (ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl))) })
        (λ { {𝒱 , W} {g = _ , k} hᴰ →
               Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
                 ΣPathP ((λ i → hᴰ .snd (~ i) .snd z)
                   , ΣPathP
                     ( FibPathP L {X = B .fst} _ {a = a .fst} refl
                     , FibPathP L {X = B .fst} _ {a = b .fst} refl))))
           ; {𝒞 , W} {g = _ , k} hᴰ →
               Codomain≡ ∫MC refl (ΣPathP (refl ,
                 isFaithfulMODELForget T _ _ _ _
                   (funExt λ z → ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z)
                     , ΣPathP
                       ( FibPathP L {X = B .fst} _ {a = a .fst} refl
                       , FibPathP L {X = B .fst} _ {a = b .fst} refl))))) })

  module _ {A A' : hSet L} (f : ⟨ A ⟩ → ⟨ A' ⟩) (P : Mᴰ.ob[ 𝒱 , A' ]) where
    private
      fⱽ : ∫MC [ (𝒱 , A) , (𝒱 , A') ]
      fⱽ = ı tt , f

    Pullⱽ : Mᴰ.ob[ 𝒱 , A ]
    Pullⱽ a = Fibᴰ L P (f a)

    pullⱽπ : Tᴰ.Hom[ fⱽ ][ Pullⱽ , P ]
    pullⱽπ .fst = ı tt , λ z → z .snd .fst
    pullⱽπ .snd i = ı tt , λ z → z .snd .snd i

    private
      intro : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fⱽ ][ c , P ] → Tᴰ.Hom[ k ][ c , Pullⱽ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {k = ı () , _}

      intro-β : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fⱽ ][ c , P ])
        → intro gᴰ Tᴰ.⋆ᴰ pullⱽπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl refl
      intro-β {𝒞 , W} {k = ı () , _}

      intro-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒱 , A) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullⱽ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullⱽπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → A' .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = ı () , _}

    ModelCodValueCartesianLift : CartesianLift ModelCod fⱽ P
    ModelCodValueCartesianLift =
      mkCartesianLift ModelCod pullⱽπ intro intro-β intro-η

  module _ {A A' : hSet L} (f : ⟨ A ⟩ → ⟨ A' ⟩) (P : Mᴰ.ob[ 𝒱 , A ]) where
    private
      fⱽ : (∫MC ^op) [ (𝒱 , A') , (𝒱 , A) ]
      fⱽ = ı tt , f

    Pushⱽ : Mᴰ.ob[ 𝒱 , A' ]
    Pushⱽ y .fst = Σ[ z ∈ Σ ⟨ A ⟩ (λ a → ⟨ P a ⟩) ] f (z .fst) ≡ y
    Pushⱽ y .snd = isSetΣ (isSetΣ (A .snd) λ a → P a .snd)
      λ _ → isProp→isSet (A' .snd _ _)

    pushⱽσ : Tᴰ^op.Hom[ fⱽ ][ Pushⱽ , P ]
    pushⱽσ .fst = ı tt , λ z → f (z .fst) , z , refl
    pushⱽσ .snd = refl

    private
      intro : ∀ {w} {c : Mᴰ.ob[ w ]} {k : (∫MC ^op) [ w , (𝒱 , A') ]}
        → Tᴰ^op.Hom[ k ⋆⟨ ∫MC ^op ⟩ fⱽ ][ c , P ]
        → Tᴰ^op.Hom[ k ][ c , Pushⱽ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst =
        ı tt , λ w → gᴰ .fst .snd (w .snd .fst)
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = ΣPathP (refl , funExt λ w →
        (λ i → gᴰ .snd i .snd (w .snd .fst)) ∙ cong k (w .snd .snd))
      intro {𝒞 , W} {k = _ , k} gᴰ .fst =
        ı tt , λ w → gᴰ .fst .snd (w .snd .fst)
      intro {𝒞 , W} {k = _ , k} gᴰ .snd = ΣPathP (refl , funExt λ w →
        (λ i → gᴰ .snd i .snd (w .snd .fst)) ∙ cong k (w .snd .snd))

      intro-β : ∀ {w} {c : Mᴰ.ob[ w ]} {k : (∫MC ^op) [ w , (𝒱 , A') ]}
        (gᴰ : Tᴰ^op.Hom[ k ⋆⟨ ∫MC ^op ⟩ fⱽ ][ c , P ])
        → intro gᴰ Tᴰ^op.⋆ᴰ pushⱽσ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl refl
      intro-β {𝒞 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl refl

      intro-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : (∫MC ^op) [ w , (𝒱 , A') ]}
        (hᴰ : Tᴰ^op.Hom[ k ][ c , Pushⱽ ])
        → intro (hᴰ Tᴰ^op.⋆ᴰ pushⱽσ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ w →
          cong (hᴰ .fst .snd) (λ i →
            w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j))))
      intro-η {𝒞 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ w →
          cong (hᴰ .fst .snd) (λ i →
            w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j))))

    ModelCodValueOpcartesianLift : CartesianLift (ModelCod ^opᴰ) fⱽ P
    ModelCodValueOpcartesianLift =
      mkCartesianLift (ModelCod ^opᴰ) pushⱽσ intro intro-β intro-η

  module _ {B B' : MOD.ob} (ϕ : MOD [ B , B' ]) (Bᴰ : Mᴰ.ob[ 𝒞 , B' ]) where
    private
      fᶜ : ∫MC [ (𝒞 , B) , (𝒞 , B') ]
      fᶜ = ı tt , ϕ

    Pullᶜ : Mᴰ.ob[ 𝒞 , B ]
    Pullᶜ = _*_ {M = B} {N = B'} ϕ (FibM Bᴰ)

    pullᶜπ : Tᴰ.Hom[ fᶜ ][ Pullᶜ , Bᴰ ]
    pullᶜπ .fst = ı tt , (λ z → z .snd .fst) , λ op γ op⟨γ⟩ p →
      cong (λ z → z .snd .fst) p
    pullᶜπ .snd = ΣPathP (refl ,
      isFaithfulMODELForget T _ _ _ _ λ i z → z .snd .snd i)

    private
      intro : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fᶜ ][ c , Bᴰ ] → Tᴰ.Hom[ k ][ c , Pullᶜ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {c} {_ , k} gᴰ .fst = ı tt , m , mH
        where
        m : ⟨ ∫Model {M = W} c .fst ⟩ → ⟨ ∫Model {M = B} Pullᶜ .fst ⟩
        m z = k .fst (z .fst) , gᴰ .fst .snd .fst z
          , λ i → gᴰ .snd i .snd .fst z
        mH : isHomoSimpl (_ , ∫Model {M = W} c .snd .fst)
          (_ , ∫Model {M = B} Pullᶜ .snd .fst) m
        mH op γ op⟨γ⟩ p = ΣPathP (k .snd op _ _ (cong fst p) ,
          ΣPathP (gᴰ .fst .snd .snd op γ op⟨γ⟩ p
            , isProp→PathP (λ i → B' .fst .snd _ _) _ _))
      intro {𝒞 , W} {k = _ , k} gᴰ .snd =
        ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl)

      intro-β : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫MC ⟩ fᶜ ][ c , Bᴰ ])
        → intro gᴰ Tᴰ.⋆ᴰ pullᶜπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl refl
      intro-β {𝒞 , W} {k = _ , k} gᴰ = Codomain≡ ∫MC refl
        (ΣPathP (refl , isFaithfulMODELForget T _ _ _ _ refl))

      intro-η : ∀ {w} {c : Mᴰ.ob[ w ]} {k : ∫MC [ w , (𝒞 , B) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullᶜ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullᶜπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫MC refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → B' .fst .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = _ , k} hᴰ = Codomain≡ ∫MC refl (ΣPathP (refl ,
        isFaithfulMODELForget T _ _ _ _ (funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z) , ΣPathP (refl ,
            isProp→PathP (λ i → B' .fst .snd _ _) _ _)))))

    ModelCodComputationCartesianLift : CartesianLift ModelCod fᶜ Bᴰ
    ModelCodComputationCartesianLift =
      mkCartesianLift ModelCod pullᶜπ intro intro-β intro-η

  ModelCodAddⱽ : AddCBPVCatⱽ (ModelCBPV T .fst) (ℓ-suc L) L
  ModelCodAddⱽ .fst = ModelCodⱽ
  ModelCodAddⱽ .snd .fst = ModelCodValueTerminalⱽ
  ModelCodAddⱽ .snd .snd .fst = ModelCodValueProductⱽ
  ModelCodAddⱽ .snd .snd .snd .fst f = ModelCodValueCartesianLift f
  ModelCodAddⱽ .snd .snd .snd .snd .fst = ModelCodValueInitialⱽ
  ModelCodAddⱽ .snd .snd .snd .snd .snd .fst = ModelCodValueCoProductⱽ
  ModelCodAddⱽ .snd .snd .snd .snd .snd .snd .fst f =
    ModelCodValueOpcartesianLift f
  ModelCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .fst =
    ModelCodComputationTerminalⱽ
  ModelCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst =
    ModelCodComputationProductⱽ
  ModelCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd f =
    ModelCodComputationCartesianLift f
