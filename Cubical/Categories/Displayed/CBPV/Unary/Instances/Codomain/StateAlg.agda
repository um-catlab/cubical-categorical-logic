{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.StateAlg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory using (∫C)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.ChangeOfObjects
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Vertical
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Base

module _ (ℓ : Level) where
  ∫SA : Category (ℓ-suc ℓ) ℓ
  ∫SA = ∫C (StateAlgCBPV {ℓ = ℓ} .fst)

  private
    module SAᴰ = Categoryᴰ (StateAlgCBPVᴰ ℓ ℓ)
    module T = Categoryᴰ (Codomain ∫SA)

  ∫Alg : ∀ {B : StateAlgebra ℓ} → SAᴰ.ob[ 𝒞 , B ] → StateAlgebra ℓ
  ∫Alg {B} Bᴰ .fst .fst = Σ ⟨ B .fst ⟩ λ b → ⟨ Bᴰ .fst b ⟩
  ∫Alg {B} Bᴰ .fst .snd = isSetΣ (B .fst .snd) λ b → Bᴰ .fst b .snd
  ∫Alg {B} Bᴰ .snd = StateAlgᴰ.∫ (Bᴰ .snd)

  projHomo : ∀ {B : StateAlgebra ℓ} (Bᴰ : SAᴰ.ob[ 𝒞 , B ])
    → Homo fst (∫Alg Bᴰ .snd) (B .snd)
  projHomo Bᴰ .Homo.rd-hom _ _ _ p = cong fst p
  projHomo Bᴰ .Homo.wt-hom _ _ _ p = cong fst p

  cmp : ∀ {c} → SAᴰ.ob[ c ] → T.ob[ c ]
  cmp {𝒱 , A} P .fst =
    𝒱 , (Σ ⟨ A ⟩ λ a → ⟨ P a ⟩) , isSetΣ (A .snd) λ a → P a .snd
  cmp {𝒱 , A} P .snd = ı tt , fst
  cmp {𝒞 , B} Bᴰ .fst = 𝒞 , ∫Alg Bᴰ
  cmp {𝒞 , B} Bᴰ .snd = ı tt , fst , projHomo Bᴰ

  StateAlgCod : CBPVCatᴰ (StateAlgCBPV {ℓ = ℓ} .fst) (ℓ-suc ℓ) ℓ
  StateAlgCod = ChangeOfObjectsᴰ (Codomain ∫SA) cmp

  StateAlgCodReind : ChosenReind StateAlgCod
  StateAlgCodReind = ChangeOfObjectsReind (Codomain ∫SA) cmp (CodomainReind ∫SA)

  private
    module Tᴰ = Categoryᴰ StateAlgCod

  module _ {A : hSet ℓ} {B : StateAlgebra ℓ} (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
    (Bᴰ : SAᴰ.ob[ 𝒞 , B ]) where
    private
      fᵁ : ∫SA [ (𝒱 , A) , (𝒞 , B) ]
      fᵁ = ı tt , f

    Pullᵁ : SAᴰ.ob[ 𝒱 , A ]
    Pullᵁ a = Fibᴰ ℓ (Bᴰ .fst) (f a)

    pullᵁπ : Tᴰ.Hom[ fᵁ ][ Pullᵁ , Bᴰ ]
    pullᵁπ .fst = ı tt , λ z → z .snd .fst
    pullᵁπ .snd i = ı tt , λ z → z .snd .snd i

    private
      intro : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fᵁ ][ c , Bᴰ ] → Tᴰ.Hom[ k ][ c , Pullᵁ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {k = ı () , _}

      intro-β : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fᵁ ][ c , Bᴰ ])
        → intro gᴰ Tᴰ.⋆ᴰ pullᵁπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl refl
      intro-β {𝒞 , W} {k = ı () , _}

      intro-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullᵁ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullᵁπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → B .fst .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = ı () , _}

    StateAlgCod-Uⱽ : CartesianLift StateAlgCod fᵁ Bᴰ
    StateAlgCod-Uⱽ = mkCartesianLift StateAlgCod pullᵁπ intro intro-β intro-η

  private
    module Tᴰop = Categoryᴰ (StateAlgCod ^opᴰᴰ)

  module _ {A : hSet ℓ} {B : StateAlgebra ℓ} (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
    (Aᴰ : SAᴰ.ob[ 𝒱 , A ]) where
    private
      module B = StateAlg (B .snd)
      ΣA = Σ ⟨ A ⟩ λ a → ⟨ Aᴰ a ⟩

      fᶠ : ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) [ (𝒞 , B) , (𝒱 , A) ]
      fᶠ = ı tt , f

    Pushᶠ : SAᴰ.ob[ 𝒞 , B ]
    Pushᶠ = StateAlgCBPV-F-obⱽ f Aᴰ

    pushᶠσ : Tᴰop.Hom[ fᶠ ][ Pushᶠ , Aᴰ ]
    pushᶠσ .fst = ı tt , λ z →
      f (z .fst) , StateAlgCBPV-retⱽ f Aᴰ (z .fst) (z .snd)
    pushᶠσ .snd = refl

    private
      unpackHomo : Homo (λ x → x .snd .fst .fst , x .snd .snd)
        (∫Alg Pushᶠ .snd) (StateAlgᴰ.∫ (FreeStateAlgᴰ ⟨ A ⟩ λ a → ⟨ Aᴰ a ⟩))
      unpackHomo .Homo.rd-hom _ _ _ p =
        cong (λ x → x .snd .fst .fst , x .snd .snd) p
      unpackHomo .Homo.wt-hom _ _ _ p =
        cong (λ x → x .snd .fst .fst , x .snd .snd) p

      module _ {C : StateAlgebra ℓ} (Cᴰ : SAᴰ.ob[ 𝒞 , C ])
        (h : ΣA → ⟨ ∫Alg Cᴰ .fst ⟩) where
        outF : ⟨ ∫Alg Pushᶠ .fst ⟩ → ⟨ ∫Alg Cᴰ .fst ⟩
        outF x = recFSA-f ΣA (∫Alg Cᴰ .snd) h
          (pack-f (x .snd .fst .fst , x .snd .snd))

        outH : Homo outF (∫Alg Pushᶠ .snd) (∫Alg Cᴰ .snd)
        outH = unpackHomo ⋆Homo (pack ⋆Homo recFSA ΣA (∫Alg Cᴰ .snd) h)

      η-pt : ∀ {C : StateAlgebra ℓ} (Cᴰ : SAᴰ.ob[ 𝒞 , C ])
        (k : StateAlgHom (∫Alg Pushᶠ) (∫Alg Cᴰ)) x
        → k .fst x ≡ outF Cᴰ (λ z → k .fst (pushᶠσ .fst .snd z)) x
      η-pt Cᴰ k x = cong (k .fst) Px
        ∙ k.rd-hom' _ _ ∙ cong₂ Cᴰ.rd (k.wt-hom' _ _) (k.wt-hom' _ _)
        where
        module k = Homo (k .snd)
        module Cᴰ = StateAlg (∫Alg Cᴰ .snd)
        module P = StateAlg (∫Alg Pushᶠ .snd)
        ret = pushᶠσ .fst .snd
        s = x .snd .fst .fst
        sᴰ = x .snd .snd
        s' : Bool → Bool × ⟨ A ⟩
        s' = FreeStateAlg.rd ⟨ A ⟩ (λ _ → s true) (λ _ → s false)
        sP : s ≡ s'
        sP = funExt λ { true → refl ; false → refl }
        sᴰP : ∀ b → PathP (λ i → ⟨ Aᴰ (sP i b .snd) ⟩) (sᴰ b)
          (P.rd (P.wt (s true .fst) (ret (s true .snd , sᴰ true)))
            (P.wt (s false .fst) (ret (s false .snd , sᴰ false))) .snd .snd b)
        sᴰP true = refl
        sᴰP false = refl
        Px : x ≡ P.rd (P.wt (s true .fst) (ret (s true .snd , sᴰ true)))
          (P.wt (s false .fst) (ret (s false .snd , sᴰ false)))
        Px = ΣPathP (sym (x .snd .fst .snd) , ΣPathP
          ( ΣPathP (sP , isProp→PathP (λ i → B .fst .snd _ _) _ _)
          , λ i b → sᴰP b i))

      out : ∀ {z} {c : SAᴰ.ob[ z ]}
        {g : ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) [ z , (𝒞 , B) ]}
        → Tᴰop.Hom[ g ⋆⟨ ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) ⟩ fᶠ ][ c , Aᴰ ]
        → Tᴰop.Hom[ g ][ c , Pushᶠ ]
      out {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ .fst =
        ı tt , outF Cᴰ (gᴰ .fst .snd) , outH Cᴰ (gᴰ .fst .snd)
      out {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ .snd = ΣPathP (refl ,
        ∫Homo≡ _ _ (C .fst .snd) (funExt λ x →
          cong₂ C.rd (cong (C.wt _) (sq _)) (cong (C.wt _) (sq _))
          ∙ sym (cong₂ C.rd (ψ.wt-hom' _ _) (ψ.wt-hom' _ _))
          ∙ sym (ψ.rd-hom' _ _)
          ∙ cong (ψ .fst) (x .snd .fst .snd)))
        where
        module C = StateAlg (C .snd)
        module ψ = Homo (ψ .snd)
        sq : ∀ z → gᴰ .fst .snd z .fst ≡ ψ .fst (f (z .fst))
        sq z i = gᴰ .snd i .snd z
      out {𝒱 , _} {g = ı () , _}

      out-β : ∀ {z} {c : SAᴰ.ob[ z ]}
        {g : ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) [ z , (𝒞 , B) ]}
        (gᴰ : Tᴰop.Hom[ g ⋆⟨ ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) ⟩ fᶠ ][
          c , Aᴰ ])
        → out gᴰ Tᴰop.⋆ᴰ pushᶠσ ≡ gᴰ
      out-β {𝒞 , C} {Cᴰ} {_ , ψ} gᴰ = Codomain≡ ∫SA refl (ΣPathP (refl ,
        funExt λ z → sym (StateAlg.rd-wt (∫Alg Cᴰ .snd) (gᴰ .fst .snd z))))
      out-β {𝒱 , _} {g = ı () , _}

      out-η : ∀ {z} {c : SAᴰ.ob[ z ]}
        {g : ∫C (StateAlgCBPV {ℓ = ℓ} .fst ^opᴰ) [ z , (𝒞 , B) ]}
        (hᴰ : Tᴰop.Hom[ g ][ c , Pushᶠ ])
        → out (hᴰ Tᴰop.⋆ᴰ pushᶠσ) ≡ hᴰ
      out-η {𝒞 , C} {Cᴰ} {_ , ψ} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl ,
        ∫Homo≡ _ _ (∫Alg Cᴰ .fst .snd) (funExt λ x →
          sym (η-pt Cᴰ (hᴰ .fst .snd) x))))
      out-η {𝒱 , _} {g = ı () , _}

    StateAlgCod-Fⱽ : CartesianLift (StateAlgCod ^opᴰᴰ) fᶠ Aᴰ
    StateAlgCod-Fⱽ = mkCartesianLift (StateAlgCod ^opᴰᴰ) pushᶠσ out out-β out-η

  StateAlgCodⱽ : MultCBPVCatⱽ (StateAlgCBPV {ℓ = ℓ} .fst) (ℓ-suc ℓ) ℓ
  StateAlgCodⱽ .fst = StateAlgCod
  StateAlgCodⱽ .snd .fst f Bᴰ = StateAlgCod-Uⱽ f Bᴰ
  StateAlgCodⱽ .snd .snd f Aᴰ = StateAlgCod-Fⱽ f Aᴰ

  StateAlgCodState : StateAlgEnrichmentᴰ (StateAlgCBPVState {ℓ = ℓ}) StateAlgCod
  StateAlgCodState .fst {A} {B} Aᴰ Bᴰ = eff
    where
    module B = StateAlg (B .snd)
    module ∫B = StateAlg (∫Alg Bᴰ .snd)
    eff : StateAlgᴰ (StateAlgCBPVState .fst A B)
      (λ M → Tᴰ.Hom[_][_,_] {x = 𝒱 , A} {y = 𝒞 , B} (ı tt , M) Aᴰ Bᴰ)
    eff .StateAlgᴰ.rdᴰ mt mf .fst =
      ı tt , λ z → ∫B.rd (mt .fst .snd z) (mf .fst .snd z)
    eff .StateAlgᴰ.rdᴰ mt mf .snd i =
      ı tt , λ z → B.rd (mt .snd i .snd z) (mf .snd i .snd z)
    eff .StateAlgᴰ.wtᴰ b m .fst = ı tt , λ z → ∫B.wt b (m .fst .snd z)
    eff .StateAlgᴰ.wtᴰ b m .snd i = ı tt , λ z → B.wt b (m .snd i .snd z)
    eff .StateAlgᴰ.wt-rdᴰ false _ _ _ _ =
      Codomain≡ ∫SA _ (ΣPathP (refl , funExt λ _ → ∫B.wt-rd false _ _))
    eff .StateAlgᴰ.wt-rdᴰ true _ _ _ _ =
      Codomain≡ ∫SA _ (ΣPathP (refl , funExt λ _ → ∫B.wt-rd true _ _))
    eff .StateAlgᴰ.rd-wtᴰ _ _ =
      Codomain≡ ∫SA _ (ΣPathP (refl , funExt λ _ → ∫B.rd-wt _))
    eff .StateAlgᴰ.wt-wtᴰ _ _ _ _ =
      Codomain≡ ∫SA _ (ΣPathP (refl , funExt λ _ → ∫B.wt-wt _ _ _))
  StateAlgCodState .snd .fst Vᴰ .Homoᴰ.rd-homᴰ _ _ _ _ _ _ _ pᴰ =
    Codomain≡ ∫SA _ λ i → (Vᴰ Tᴰ.⋆ᴰ pᴰ i) .fst
  StateAlgCodState .snd .fst Vᴰ .Homoᴰ.wt-homᴰ _ _ _ _ _ _ pᴰ =
    Codomain≡ ∫SA _ λ i → (Vᴰ Tᴰ.⋆ᴰ pᴰ i) .fst
  StateAlgCodState .snd .snd Sᴰ .Homoᴰ.rd-homᴰ _ _ _ _ _ _ _ pᴰ =
    Codomain≡ ∫SA _ ((λ i → (pᴰ i Tᴰ.⋆ᴰ Sᴰ) .fst)
      ∙ ΣPathP (refl , funExt λ _ → Homo.rd-hom' (Sᴰ .fst .snd .snd) _ _))
  StateAlgCodState .snd .snd Sᴰ .Homoᴰ.wt-homᴰ _ _ _ _ _ _ pᴰ =
    Codomain≡ ∫SA _ ((λ i → (pᴰ i Tᴰ.⋆ᴰ Sᴰ) .fst)
      ∙ ΣPathP (refl , funExt λ _ → Homo.wt-hom' (Sᴰ .fst .snd .snd) _ _))

  private
    instance
      StateAlgCodReindInst : ChosenReind StateAlgCod
      StateAlgCodReindInst = StateAlgCodReind

    module Tᴰ^op = Categoryᴰ (StateAlgCod ^opᴰ)

  module _ {B : StateAlgebra ℓ} (Bᴰ : SAᴰ.ob[ 𝒞 , B ]) where
    private
      module B = StateAlg (B .snd)
      module ∫B = StateAlg (∫Alg Bᴰ .snd)

    FibAlg : StateAlgᴰ (B .snd) (Fib ℓ (Bᴰ .fst))
    FibAlg .StateAlgᴰ.rdᴰ u v =
      ∫B.rd (u .fst) (v .fst) , cong₂ B.rd (u .snd) (v .snd)
    FibAlg .StateAlgᴰ.wtᴰ b u = ∫B.wt b (u .fst) , cong (B.wt b) (u .snd)
    FibAlg .StateAlgᴰ.wt-rdᴰ false _ _ u v =
      ΣPathP (∫B.wt-rd false _ _ , isProp→PathP (λ i → B .fst .snd _ _) _ _)
    FibAlg .StateAlgᴰ.wt-rdᴰ true _ _ u v =
      ΣPathP (∫B.wt-rd true _ _ , isProp→PathP (λ i → B .fst .snd _ _) _ _)
    FibAlg .StateAlgᴰ.rd-wtᴰ _ u =
      ΣPathP (∫B.rd-wt _ , isProp→PathP (λ i → B .fst .snd _ _) _ _)
    FibAlg .StateAlgᴰ.wt-wtᴰ _ _ _ u =
      ΣPathP (∫B.wt-wt _ _ _ , isProp→PathP (λ i → B .fst .snd _ _) _ _)

  𝟙ᶜ : ∀ {B : StateAlgebra ℓ} → SAᴰ.ob[ 𝒞 , B ]
  𝟙ᶜ {B} = (λ _ → Unit* , isSetUnit*) , Unitⱽ (B .snd) ℓ

  _×ᶜ_ : ∀ {B : StateAlgebra ℓ} → SAᴰ.ob[ 𝒞 , B ] → SAᴰ.ob[ 𝒞 , B ]
    → SAᴰ.ob[ 𝒞 , B ]
  (a ×ᶜ b) .fst = _×Cod_ (a .fst) (b .fst)
  (a ×ᶜ b) .snd = Prodⱽ (FibAlg a) (FibAlg b)

  module _ (X : hSet ℓ) where
    private
      ! : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , X) ]}
        → Tᴰ.Hom[ k ][ c , 𝟙Cod {X = X} ]
      ! {𝒱 , W} {k = _ , k} = (ı tt , λ z → k (z .fst) , tt*) , refl
      ! {𝒞 , W} {k = ı () , _}

      !-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , X) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , 𝟙Cod {X = X} ]) → ! ≡ hᴰ
      !-η {𝒱 , W} {k = _ , k} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
        ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , refl)))
      !-η {𝒞 , W} {k = ı () , _}

    StateAlgCodValueTerminalⱽ : Terminalⱽ StateAlgCod (𝒱 , X)
    StateAlgCodValueTerminalⱽ = mkTerminalⱽ StateAlgCod (𝟙Cod {X = X}) ! !-η

    private
      ¡ : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ (𝒱 , X) , w ]}
        → Tᴰ.Hom[ k ][ 𝟘Cod {X = X} , c ]
      ¡ {𝒱 , W} .fst .fst = ı tt
      ¡ {𝒱 , W} .fst .snd (x , ())
      ¡ {𝒱 , W} .snd i .fst = ı tt
      ¡ {𝒱 , W} .snd i .snd (x , ())
      ¡ {𝒞 , W} .fst .fst = ı tt
      ¡ {𝒞 , W} .fst .snd (x , ())
      ¡ {𝒞 , W} .snd i .fst = ı tt
      ¡ {𝒞 , W} .snd i .snd (x , ())

      ¡-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ (𝒱 , X) , w ]}
        (hᴰ : Tᴰ.Hom[ k ][ 𝟘Cod {X = X} , c ]) → ¡ ≡ hᴰ
      ¡-η {𝒱 , W} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ { (x , ()) }))
      ¡-η {𝒞 , W} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ { (x , ()) }))

    StateAlgCodValueInitialⱽ : Initialⱽ StateAlgCod (𝒱 , X)
    StateAlgCodValueInitialⱽ = mkTerminalⱽ (StateAlgCod ^opᴰ) (𝟘Cod {X = X}) ¡ ¡-η

  module _ (B : StateAlgebra ℓ) where
    private
      !H : ∀ {W} (k : StateAlgHom W B) (c : SAᴰ.ob[ 𝒞 , W ])
        → Homo (λ z → k .fst (z .fst) , tt*)
            (∫Alg c .snd) (∫Alg (𝟙ᶜ {B}) .snd)
      !H k c .Homo.rd-hom _ _ _ p =
        ΣPathP (Homo.rd-hom (k .snd) _ _ _ (cong fst p) , refl)
      !H k c .Homo.wt-hom _ _ _ p =
        ΣPathP (Homo.wt-hom (k .snd) _ _ _ (cong fst p) , refl)

      ! : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ][ c , 𝟙ᶜ {B} ]
      ! {𝒱 , W} {k = _ , k} = (ı tt , λ z → k (z .fst) , tt*) , refl
      ! {𝒞 , W} {c} {_ , k} = (ı tt , (λ z → k .fst (z .fst) , tt*) , !H k c)
        , ΣPathP (refl , ∫Homo≡ _ _ (B .fst .snd) refl)

      !-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , 𝟙ᶜ {B} ]) → ! ≡ hᴰ
      !-η {𝒱 , W} {k = _ , k} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
        ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , refl)))
      !-η {𝒞 , W} {k = _ , k} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl ,
        ∫Homo≡ _ _ (∫Alg (𝟙ᶜ {B}) .fst .snd) (funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z) , refl))))

    StateAlgCodComputationTerminalⱽ : Terminalⱽ StateAlgCod (𝒞 , B)
    StateAlgCodComputationTerminalⱽ = mkTerminalⱽ StateAlgCod (𝟙ᶜ {B}) ! !-η

  module _ {X : hSet ℓ} (a b : SAᴰ.ob[ 𝒱 , X ]) where
    private
      π₁ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        (_×Cod_ a b) a
      π₁ = (ı tt , λ z → z .snd .fst .fst)
        , λ i → ı tt , λ z → z .snd .fst .snd i
      π₂ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        (_×Cod_ a b) b
      π₂ = (ı tt , λ z → z .snd .snd .fst)
        , λ i → ı tt , λ z → z .snd .snd .snd i

      pair : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , X) ]}
        → Tᴰ.Hom[ k ][ c , a ] → Tᴰ.Hom[ k ][ c , b ]
        → Tᴰ.Hom[ k ][ c , _×Cod_ a b ]
      pair {𝒱 , W} {k = _ , k} g₁ g₂ =
        (ı tt , λ z → k (z .fst)
          , (g₁ .fst .snd z , λ i → g₁ .snd i .snd z)
          , (g₂ .fst .snd z , λ i → g₂ .snd i .snd z)) , refl
      pair {𝒞 , W} {k = ı () , _}

      pair-β : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , X) ]}
        (φ : Tᴰ.Hom[ k ][ c , a ] × Tᴰ.Hom[ k ][ c , b ])
        → ( ChosenReind.reind⟨_⟩ StateAlgCodReind (Category.⋆IdR ∫SA k)
                (pair (φ .fst) (φ .snd) Tᴰ.⋆ᴰ π₁)
            , ChosenReind.reind⟨_⟩ StateAlgCodReind (Category.⋆IdR ∫SA k)
                (pair (φ .fst) (φ .snd) Tᴰ.⋆ᴰ π₂))
          ≡ φ
      pair-β {𝒱 , W} {k = _ , k} _ =
        ≡-× (Codomain≡ ∫SA refl refl) (Codomain≡ ∫SA refl refl)
      pair-β {𝒞 , W} {k = ı () , _}

      pair-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , X) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , _×Cod_ a b ])
        → pair (ChosenReind.reind⟨_⟩ StateAlgCodReind (Category.⋆IdR ∫SA k)
              (hᴰ Tᴰ.⋆ᴰ π₁))
            (ChosenReind.reind⟨_⟩ StateAlgCodReind (Category.⋆IdR ∫SA k)
              (hᴰ Tᴰ.⋆ᴰ π₂))
          ≡ hᴰ
      pair-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z)
            , ΣPathP (FibPathP ℓ _ refl , FibPathP ℓ _ refl))))
      pair-η {𝒞 , W} {k = ı () , _}

    StateAlgCodValueProductⱽ : BinProductⱽ StateAlgCod a b
    StateAlgCodValueProductⱽ =
      mkBinProductⱽ StateAlgCod (_×Cod_ a b) π₁ π₂ pair pair-β pair-η

  module _ {X : hSet ℓ} (a b : SAᴰ.ob[ 𝒱 , X ]) where
    private
      σ₁ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        a (_+Cod_ a b)
      σ₁ = (ı tt , λ z → z .fst , inl (z .snd)) , refl
      σ₂ : Tᴰ.Hom[_][_,_] {x = 𝒱 , X} {y = 𝒱 , X} (ı tt , λ x → x)
        b (_+Cod_ a b)
      σ₂ = (ı tt , λ z → z .fst , inr (z .snd)) , refl

      case : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ (𝒱 , X) , w ]}
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

    StateAlgCodValueCoProductⱽ : BinCoProductⱽ StateAlgCod a b
    StateAlgCodValueCoProductⱽ =
      mkBinProductⱽ (StateAlgCod ^opᴰ) (_+Cod_ a b) σ₁ σ₂ case
        (λ { {𝒱 , W} _ → ≡-× (Codomain≡ ∫SA refl refl) (Codomain≡ ∫SA refl refl)
           ; {𝒞 , W} _ → ≡-× (Codomain≡ ∫SA refl refl) (Codomain≡ ∫SA refl refl) })
        (λ { {𝒱 , W} hᴰ → Codomain≡ ∫SA refl (ΣPathP (refl ,
               funExt λ { (x , inl p) → refl ; (x , inr q) → refl }))
           ; {𝒞 , W} hᴰ → Codomain≡ ∫SA refl (ΣPathP (refl ,
               funExt λ { (x , inl p) → refl ; (x , inr q) → refl })) })

  module _ {B : StateAlgebra ℓ} (a b : SAᴰ.ob[ 𝒞 , B ]) where
    private
      isSetB = B .fst .snd

      π₁ : Tᴰ.Hom[_][_,_] {x = 𝒞 , B} {y = 𝒞 , B} (ı tt , (λ x → x) , idHomo)
        (a ×ᶜ b) a
      π₁ .fst = ı tt , (λ z → z .snd .fst .fst) , H
        where
        H : Homo (λ z → z .snd .fst .fst) (∫Alg (a ×ᶜ b) .snd) (∫Alg a .snd)
        H .Homo.rd-hom _ _ _ p = cong (λ z → z .snd .fst .fst) p
        H .Homo.wt-hom _ _ _ p = cong (λ z → z .snd .fst .fst) p
      π₁ .snd = ΣPathP (refl , ∫Homo≡ _ _ isSetB λ i z → z .snd .fst .snd i)

      π₂ : Tᴰ.Hom[_][_,_] {x = 𝒞 , B} {y = 𝒞 , B} (ı tt , (λ x → x) , idHomo)
        (a ×ᶜ b) b
      π₂ .fst = ı tt , (λ z → z .snd .snd .fst) , H
        where
        H : Homo (λ z → z .snd .snd .fst) (∫Alg (a ×ᶜ b) .snd) (∫Alg b .snd)
        H .Homo.rd-hom _ _ _ p = cong (λ z → z .snd .snd .fst) p
        H .Homo.wt-hom _ _ _ p = cong (λ z → z .snd .snd .fst) p
      π₂ .snd = ΣPathP (refl , ∫Homo≡ _ _ isSetB λ i z → z .snd .snd .snd i)

      pair : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ][ c , a ] → Tᴰ.Hom[ k ][ c , b ]
        → Tᴰ.Hom[ k ][ c , a ×ᶜ b ]
      pair {𝒱 , W} {k = _ , k} g₁ g₂ =
        (ı tt , λ z → k (z .fst)
          , (g₁ .fst .snd z , λ i → g₁ .snd i .snd z)
          , (g₂ .fst .snd z , λ i → g₂ .snd i .snd z)) , refl
      pair {𝒞 , W} {c} {_ , k} g₁ g₂ .fst = ı tt , m , mH
        where
        m : ⟨ ∫Alg c .fst ⟩ → ⟨ ∫Alg (a ×ᶜ b) .fst ⟩
        m z = k .fst (z .fst)
          , (g₁ .fst .snd .fst z , λ i → g₁ .snd i .snd .fst z)
          , (g₂ .fst .snd .fst z , λ i → g₂ .snd i .snd .fst z)
        mH : Homo m (∫Alg c .snd) (∫Alg (a ×ᶜ b) .snd)
        mH .Homo.rd-hom _ _ _ p =
          ΣPathP (Homo.rd-hom (k .snd) _ _ _ (cong fst p)
            , ΣPathP
              ( ΣPathP (Homo.rd-hom (g₁ .fst .snd .snd) _ _ _ p
                , isProp→PathP (λ i → isSetB _ _) _ _)
              , ΣPathP (Homo.rd-hom (g₂ .fst .snd .snd) _ _ _ p
                , isProp→PathP (λ i → isSetB _ _) _ _)))
        mH .Homo.wt-hom _ _ _ p =
          ΣPathP (Homo.wt-hom (k .snd) _ _ _ (cong fst p)
            , ΣPathP
              ( ΣPathP (Homo.wt-hom (g₁ .fst .snd .snd) _ _ _ p
                , isProp→PathP (λ i → isSetB _ _) _ _)
              , ΣPathP (Homo.wt-hom (g₂ .fst .snd .snd) _ _ _ p
                , isProp→PathP (λ i → isSetB _ _) _ _)))
      pair {𝒞 , W} {k = _ , k} g₁ g₂ .snd =
        ΣPathP (refl , ∫Homo≡ _ _ isSetB refl)

    StateAlgCodComputationProductⱽ : BinProductⱽ StateAlgCod a b
    StateAlgCodComputationProductⱽ =
      mkBinProductⱽ StateAlgCod (a ×ᶜ b) π₁ π₂ pair
        (λ { {𝒱 , W} {g = _ , k} _ →
               ≡-× (Codomain≡ ∫SA refl refl) (Codomain≡ ∫SA refl refl)
           ; {𝒞 , W} {g = _ , k} _ → ≡-×
               (Codomain≡ ∫SA refl
                 (ΣPathP (refl , ∫Homo≡ _ _ (∫Alg a .fst .snd) refl)))
               (Codomain≡ ∫SA refl
                 (ΣPathP (refl , ∫Homo≡ _ _ (∫Alg b .fst .snd) refl))) })
        (λ { {𝒱 , W} {g = _ , k} hᴰ →
               Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
                 ΣPathP ((λ i → hᴰ .snd (~ i) .snd z)
                   , ΣPathP (FibPathP ℓ _ refl , FibPathP ℓ _ refl))))
           ; {𝒞 , W} {g = _ , k} hᴰ →
               Codomain≡ ∫SA refl (ΣPathP (refl ,
                 ∫Homo≡ _ _ (∫Alg (a ×ᶜ b) .fst .snd)
                   (funExt λ z → ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z)
                     , ΣPathP (FibPathP ℓ _ refl , FibPathP ℓ _ refl))))) })

  module _ {A A' : hSet ℓ} (f : ⟨ A ⟩ → ⟨ A' ⟩) (P : SAᴰ.ob[ 𝒱 , A' ]) where
    private
      fⱽ : ∫SA [ (𝒱 , A) , (𝒱 , A') ]
      fⱽ = ı tt , f

    Pullⱽ : SAᴰ.ob[ 𝒱 , A ]
    Pullⱽ a = Fibᴰ ℓ P (f a)

    pullⱽπ : Tᴰ.Hom[ fⱽ ][ Pullⱽ , P ]
    pullⱽπ .fst = ı tt , λ z → z .snd .fst
    pullⱽπ .snd i = ı tt , λ z → z .snd .snd i

    private
      intro : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fⱽ ][ c , P ] → Tᴰ.Hom[ k ][ c , Pullⱽ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {k = ı () , _}

      intro-β : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fⱽ ][ c , P ])
        → intro gᴰ Tᴰ.⋆ᴰ pullⱽπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl refl
      intro-β {𝒞 , W} {k = ı () , _}

      intro-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒱 , A) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullⱽ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullⱽπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → A' .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = ı () , _}

    StateAlgCodValueCartesianLift : CartesianLift StateAlgCod fⱽ P
    StateAlgCodValueCartesianLift =
      mkCartesianLift StateAlgCod pullⱽπ intro intro-β intro-η

  module _ {A A' : hSet ℓ} (f : ⟨ A ⟩ → ⟨ A' ⟩) (P : SAᴰ.ob[ 𝒱 , A ]) where
    private
      fⱽ : (∫SA ^op) [ (𝒱 , A') , (𝒱 , A) ]
      fⱽ = ı tt , f

    Pushⱽ : SAᴰ.ob[ 𝒱 , A' ]
    Pushⱽ y .fst = Σ[ z ∈ Σ ⟨ A ⟩ (λ a → ⟨ P a ⟩) ] f (z .fst) ≡ y
    Pushⱽ y .snd = isSetΣ (isSetΣ (A .snd) λ a → P a .snd)
      λ _ → isProp→isSet (A' .snd _ _)

    pushⱽσ : Tᴰ^op.Hom[ fⱽ ][ Pushⱽ , P ]
    pushⱽσ .fst = ı tt , λ z → f (z .fst) , z , refl
    pushⱽσ .snd = refl

    private
      intro : ∀ {w} {c : SAᴰ.ob[ w ]} {k : (∫SA ^op) [ w , (𝒱 , A') ]}
        → Tᴰ^op.Hom[ k ⋆⟨ ∫SA ^op ⟩ fⱽ ][ c , P ]
        → Tᴰ^op.Hom[ k ][ c , Pushⱽ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst =
        ı tt , λ w → gᴰ .fst .snd (w .snd .fst)
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = ΣPathP (refl , funExt λ w →
        (λ i → gᴰ .snd i .snd (w .snd .fst)) ∙ cong k (w .snd .snd))
      intro {𝒞 , W} {k = _ , k} gᴰ .fst =
        ı tt , λ w → gᴰ .fst .snd (w .snd .fst)
      intro {𝒞 , W} {k = _ , k} gᴰ .snd = ΣPathP (refl , funExt λ w →
        (λ i → gᴰ .snd i .snd (w .snd .fst)) ∙ cong k (w .snd .snd))

      intro-β : ∀ {w} {c : SAᴰ.ob[ w ]} {k : (∫SA ^op) [ w , (𝒱 , A') ]}
        (gᴰ : Tᴰ^op.Hom[ k ⋆⟨ ∫SA ^op ⟩ fⱽ ][ c , P ])
        → intro gᴰ Tᴰ^op.⋆ᴰ pushⱽσ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl refl
      intro-β {𝒞 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl refl

      intro-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : (∫SA ^op) [ w , (𝒱 , A') ]}
        (hᴰ : Tᴰ^op.Hom[ k ][ c , Pushⱽ ])
        → intro (hᴰ Tᴰ^op.⋆ᴰ pushⱽσ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ w →
          cong (hᴰ .fst .snd) (λ i →
            w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j))))
      intro-η {𝒞 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ w →
          cong (hᴰ .fst .snd) (λ i →
            w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j))))

    StateAlgCodValueOpcartesianLift : CartesianLift (StateAlgCod ^opᴰ) fⱽ P
    StateAlgCodValueOpcartesianLift =
      mkCartesianLift (StateAlgCod ^opᴰ) pushⱽσ intro intro-β intro-η

  module _ {B B' : StateAlgebra ℓ} (ϕ : StateAlgHom B B')
    (Bᴰ : SAᴰ.ob[ 𝒞 , B' ]) where
    private
      module B = StateAlg (B .snd)
      module ϕ = Homo (ϕ .snd)

      fᶜ : ∫SA [ (𝒞 , B) , (𝒞 , B') ]
      fᶜ = ı tt , ϕ

      reindFib : ∀ {y y'} → y ≡ y' → Fib ℓ (Bᴰ .fst) y → Fib ℓ (Bᴰ .fst) y'
      reindFib p u = u .fst , u .snd ∙ p

    Pullᶜ : SAᴰ.ob[ 𝒞 , B ]
    Pullᶜ .fst b = Fibᴰ ℓ (Bᴰ .fst) (ϕ .fst b)
    Pullᶜ .snd = reindexStateAlgᴰ (ϕ .snd) (FibAlg Bᴰ) (B' .fst .snd)
      ⦃ record
        { reind⟨_⟩ = reindFib
        ; reind-filler = λ p u i → p i , u .fst , compPath-filler (u .snd) p i
        } ⦄

    pullᶜπ : Tᴰ.Hom[ fᶜ ][ Pullᶜ , Bᴰ ]
    pullᶜπ .fst = ı tt , (λ z → z .snd .fst) , πH
      where
      πH : Homo (λ z → z .snd .fst) (∫Alg Pullᶜ .snd) (∫Alg Bᴰ .snd)
      πH .Homo.rd-hom _ _ _ p = cong (λ z → z .snd .fst) p
      πH .Homo.wt-hom _ _ _ p = cong (λ z → z .snd .fst) p
    pullᶜπ .snd = ΣPathP (refl ,
      ∫Homo≡ _ _ (B' .fst .snd) λ i z → z .snd .snd i)

    private
      intro : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        → Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fᶜ ][ c , Bᴰ ] → Tᴰ.Hom[ k ][ c , Pullᶜ ]
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .fst = ı tt
      intro {𝒱 , W} {k = _ , k} gᴰ .fst .snd z =
        k (z .fst) , gᴰ .fst .snd z , λ i → gᴰ .snd i .snd z
      intro {𝒱 , W} {k = _ , k} gᴰ .snd = refl
      intro {𝒞 , W} {c} {_ , k} gᴰ .fst = ı tt , m , mH
        where
        module k = Homo (k .snd)
        m : ⟨ ∫Alg c .fst ⟩ → ⟨ ∫Alg Pullᶜ .fst ⟩
        m z = k .fst (z .fst) , gᴰ .fst .snd .fst z
          , λ i → gᴰ .snd i .snd .fst z
        mH : Homo m (∫Alg c .snd) (∫Alg Pullᶜ .snd)
        mH .Homo.rd-hom _ _ _ p = ΣPathP (k.rd-hom _ _ _ (cong fst p) ,
          ΣPathP (Homo.rd-hom (gᴰ .fst .snd .snd) _ _ _ p
            , isProp→PathP (λ i → B' .fst .snd _ _) _ _))
        mH .Homo.wt-hom _ _ _ p = ΣPathP (k.wt-hom _ _ _ (cong fst p) ,
          ΣPathP (Homo.wt-hom (gᴰ .fst .snd .snd) _ _ _ p
            , isProp→PathP (λ i → B' .fst .snd _ _) _ _))
      intro {𝒞 , W} {k = _ , k} gᴰ .snd = ΣPathP (refl ,
        ∫Homo≡ _ _ (B .fst .snd) refl)

      intro-β : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        (gᴰ : Tᴰ.Hom[ k ⋆⟨ ∫SA ⟩ fᶜ ][ c , Bᴰ ])
        → intro gᴰ Tᴰ.⋆ᴰ pullᶜπ ≡ gᴰ
      intro-β {𝒱 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl refl
      intro-β {𝒞 , W} {k = _ , k} gᴰ = Codomain≡ ∫SA refl (ΣPathP (refl ,
        ∫Homo≡ _ _ (∫Alg Bᴰ .fst .snd) refl))

      intro-η : ∀ {w} {c : SAᴰ.ob[ w ]} {k : ∫SA [ w , (𝒞 , B) ]}
        (hᴰ : Tᴰ.Hom[ k ][ c , Pullᶜ ])
        → intro (hᴰ Tᴰ.⋆ᴰ pullᶜπ) ≡ hᴰ
      intro-η {𝒱 , W} {k = _ , k} hᴰ =
        Codomain≡ ∫SA refl (ΣPathP (refl , funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd z) , ΣPathP (refl ,
            isProp→PathP (λ i → B' .fst .snd _ _) _ _))))
      intro-η {𝒞 , W} {k = _ , k} hᴰ = Codomain≡ ∫SA refl (ΣPathP (refl ,
        ∫Homo≡ _ _ (∫Alg Pullᶜ .fst .snd) (funExt λ z →
          ΣPathP ((λ i → hᴰ .snd (~ i) .snd .fst z) , ΣPathP (refl ,
            isProp→PathP (λ i → B' .fst .snd _ _) _ _)))))

    StateAlgCodComputationCartesianLift : CartesianLift StateAlgCod fᶜ Bᴰ
    StateAlgCodComputationCartesianLift =
      mkCartesianLift StateAlgCod pullᶜπ intro intro-β intro-η

  StateAlgCodAddⱽ : AddCBPVCatⱽ (StateAlgCBPV {ℓ = ℓ} .fst) (ℓ-suc ℓ) ℓ
  StateAlgCodAddⱽ .fst = StateAlgCodⱽ
  StateAlgCodAddⱽ .snd .fst = StateAlgCodValueTerminalⱽ
  StateAlgCodAddⱽ .snd .snd .fst = StateAlgCodValueProductⱽ
  StateAlgCodAddⱽ .snd .snd .snd .fst f = StateAlgCodValueCartesianLift f
  StateAlgCodAddⱽ .snd .snd .snd .snd .fst = StateAlgCodValueInitialⱽ
  StateAlgCodAddⱽ .snd .snd .snd .snd .snd .fst = StateAlgCodValueCoProductⱽ
  StateAlgCodAddⱽ .snd .snd .snd .snd .snd .snd .fst f =
    StateAlgCodValueOpcartesianLift f
  StateAlgCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .fst =
    StateAlgCodComputationTerminalⱽ
  StateAlgCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst =
    StateAlgCodComputationProductⱽ
  StateAlgCodAddⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd f =
    StateAlgCodComputationCartesianLift f
