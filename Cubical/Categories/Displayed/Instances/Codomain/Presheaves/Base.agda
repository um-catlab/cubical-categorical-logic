{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Instances.ChangeOfObjects
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
  hiding (ΣPsh)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.Codomain.Base

private
  variable
    ℓC ℓC' : Level

open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} (ℓ : Level) where
  private
    module C = Category C

  PSH : Category _ _
  PSH = PresheafCategory C ℓ

  module _ {P : Presheaf C ℓ} (Pᴰ : Presheafᴰ P (Unitᴰ C) ℓ) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation (Unitᴰ C) P Pᴰ

    ∫ᴾ : Presheaf C ℓ
    ∫ᴾ .F-ob x .fst = Σ[ p ∈ P.p[ x ] ] Pᴰ.p[ p ][ tt ]
    ∫ᴾ .F-ob x .snd = isSetΣ P.isSetPsh (λ _ → Pᴰ.isSetPshᴰ)
    ∫ᴾ .F-hom f (p , pᴰ) = (f P.⋆ p) , (tt Pᴰ.⋆ᴰ pᴰ)
    ∫ᴾ .F-id = funExt λ _ → Pᴰ.⋆IdLᴰ _
    ∫ᴾ .F-seq _ _ = funExt λ _ → Pᴰ.⋆Assocᴰ tt tt _

    πᴾ : NatTrans ∫ᴾ P
    πᴾ .N-ob x = fst
    πᴾ .N-hom f = refl

  ΣPsh : ∀ {P} → Presheafᴰ P (Unitᴰ C) ℓ → Categoryᴰ.ob[ Codomain PSH ] P
  ΣPsh Pᴰ = ∫ᴾ Pᴰ , πᴾ Pᴰ

  PSHCod : Categoryᴰ PSH _ _
  PSHCod = ChangeOfObjectsᴰ (Codomain PSH) ΣPsh

  PSHCodReind : ChosenReind PSHCod
  PSHCodReind = ChangeOfObjectsReind (Codomain PSH) ΣPsh (CodomainReind PSH)

  private
    module PSHCod = Categoryᴰ PSHCod

  module _ {X : Presheaf C ℓ} where
    private
      module X = PresheafNotation X

    FibPsh : Presheafᴰ X (Unitᴰ C) ℓ → (Γ : C.ob) → X.p[ Γ ] → Type ℓ
    FibPsh a Γ x = Σ[ w ∈ ⟨ ∫ᴾ a .F-ob Γ ⟩ ] (w .fst ≡ x)

    isSetFibPsh : (a : Presheafᴰ X (Unitᴰ C) ℓ) (Γ : C.ob) (x : X.p[ Γ ]) →
      isSet (FibPsh a Γ x)
    isSetFibPsh a Γ x =
      isSetΣ (∫ᴾ a .F-ob Γ .snd) λ w → isProp→isSet (X.isSetPsh (w .fst) x)

    FibᴰPsh : Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ X (Unitᴰ C) ℓ
    FibᴰPsh a .F-ob (Γ , _ , x) = FibPsh a Γ x , isSetFibPsh a Γ x
    FibᴰPsh a .F-hom (ρ , _ , e) (w , p) =
      ∫ᴾ a .F-hom ρ w , cong (ρ X.⋆_) p ∙ e
    FibᴰPsh a .F-id = funExt λ u →
      ΣPathPProp (λ _ → X.isSetPsh _ _) (funExt⁻ (∫ᴾ a .F-id) (u .fst))
    FibᴰPsh a .F-seq f g = funExt λ u →
      ΣPathPProp (λ _ → X.isSetPsh _ _)
        (funExt⁻ (∫ᴾ a .F-seq (f .fst) (g .fst)) (u .fst))

    FibPathPPsh : ∀ {Γ} {x x' : X.p[ Γ ]} (r : x ≡ x') {a : Presheafᴰ X (Unitᴰ
      C) ℓ}
      {u : FibPsh a Γ x} {u' : FibPsh a Γ x'} → u .fst ≡ u' .fst
      → PathP (λ i → FibPsh a Γ (r i)) u u'
    FibPathPPsh r {u = u} {u'} p i .fst = p i
    FibPathPPsh r {u = u} {u'} p i .snd =
      isProp→PathP (λ i → X.isSetPsh (p i .fst) (r i)) (u .snd) (u' .snd) i

  PointwisePsh : {X Y : Presheaf C ℓ} (h : PSH [ X , Y ]) (P : Presheafᴰ X
    (Unitᴰ C) ℓ)
    (Q : Presheafᴰ Y (Unitᴰ C) ℓ) → Type _
  PointwisePsh h P Q =
    Σ[ g ∈ (∀ Γ (z : ⟨ ∫ᴾ P .F-ob Γ ⟩) → FibPsh Q Γ (h .N-ob Γ (z .fst))) ]
      N-hom-Type (∫ᴾ P) (∫ᴾ Q) (λ Γ z → g Γ z .fst)

  module _ {X Y : Presheaf C ℓ} {h : PSH [ X , Y ]} {P : Presheafᴰ X (Unitᴰ C)
    ℓ}
    {Q : Presheafᴰ Y (Unitᴰ C) ℓ} where
    ptPsh : PSHCod.Hom[ h ][ P , Q ] → PointwisePsh h P Q
    ptPsh φ .fst Γ z .fst = φ .fst .N-ob Γ z
    ptPsh φ .fst Γ z .snd i = φ .snd i .N-ob Γ z
    ptPsh φ .snd = φ .fst .N-hom

    mkPsh : PointwisePsh h P Q → PSHCod.Hom[ h ][ P , Q ]
    mkPsh g .fst .N-ob Γ z = g .fst Γ z .fst
    mkPsh g .fst .N-hom = g .snd
    mkPsh g .snd = makeNatTransPath λ i Γ z → g .fst Γ z .snd i

  _ : {X Y Z : Presheaf C ℓ} {f : PSH [ X , Y ]} {g : PSH [ Y , Z ]}
    {P : Presheafᴰ X (Unitᴰ C) ℓ} {Q : Presheafᴰ Y (Unitᴰ C) ℓ} {R : Presheafᴰ Z
      (Unitᴰ C) ℓ}
    (φ : PSHCod.Hom[ f ][ P , Q ]) (ψ : PSHCod.Hom[ g ][ Q , R ])
    (Γ : C.ob) (z : ⟨ ∫ᴾ P .F-ob Γ ⟩)
    → ptPsh (φ PSHCod.⋆ᴰ ψ) .fst Γ z .fst ≡ ψ .fst .N-ob Γ (φ .fst .N-ob Γ z)
  _ = λ φ ψ Γ z → refl

  _ : {X Y : Presheaf C ℓ} {f g : PSH [ X , Y ]} {P : Presheafᴰ X (Unitᴰ C) ℓ}
    {Q : Presheafᴰ Y (Unitᴰ C) ℓ} (e : f ≡ g) (φ : PSHCod.Hom[ f ][ P , Q ])
    → ChosenReind.reind⟨_⟩ PSHCodReind e φ .fst ≡ φ .fst
  _ = λ e φ → refl

  module _ {X Y : Presheaf C ℓ} {f : PSH [ X , Y ]} {P : Presheafᴰ X (Unitᴰ C)
    ℓ}
    {Q : Presheafᴰ Y (Unitᴰ C) ℓ} (φ : PSHCod.Hom[ f ][ P , Q ])
    (N : ∀ Γ → ⟨ ∫ᴾ P .F-ob Γ ⟩ → ⟨ ∫ᴾ Q .F-ob Γ ⟩)
    (p : φ .fst .N-ob ≡ N) where
    improvePsh : PSHCod.Hom[ f ][ P , Q ]
    improvePsh .fst .N-ob = N
    improvePsh .fst .N-hom = subst (N-hom-Type (∫ᴾ P) (∫ᴾ Q)) p (φ .fst .N-hom)
    improvePsh .snd = makeNatTransPath
      (cong (λ M Γ z → M Γ z .fst) (sym p) ∙ cong N-ob (φ .snd))

    improveᴾ≡ : φ ≡ improvePsh
    improveᴾ≡ = Codomain≡ PSH refl (makeNatTransPath p)

instance
  PSHCodReindInst : ∀ {ℓC ℓC' ℓ} {C : Category ℓC ℓC'}
    → ChosenReind (PSHCod {C = C} ℓ)
  PSHCodReindInst = PSHCodReind _

module _ {C : Category ℓC ℓC'} {ℓ : Level} where
  private
    module C = Category C
    module PSH = Category (PSH {C = C} ℓ)
    module PSHCod = Categoryᴰ (PSHCod {C = C} ℓ)
    module F = Fibers (PSHCod {C = C} ℓ)

  reind-fstPsh : ∀ {X Y : Presheaf C ℓ} {f g : PSH {C = C} ℓ [ X , Y ]}
    {P : Presheafᴰ X (Unitᴰ C) ℓ} {Q : Presheafᴰ Y (Unitᴰ C) ℓ} (e : f ≡ g)
    (φ : PSHCod.Hom[ f ][ P , Q ])
    → F.reind {aᴰ = P} {bᴰ = Q} e φ .fst .N-ob ≡ φ .fst .N-ob
  reind-fstPsh {P = P} {Q} e φ =
    cong (λ z → z .snd .fst .N-ob) (sym (F.reind-filler {aᴰ = P} {bᴰ = Q} e))

  module _ {X : Presheaf C ℓ} where
    𝟙ᴾ : Presheafᴰ X (Unitᴰ C) ℓ
    𝟙ᴾ .F-ob _ = Unit* , isSetUnit*
    𝟙ᴾ .F-hom _ _ = tt*
    𝟙ᴾ .F-id = refl
    𝟙ᴾ .F-seq _ _ = refl

    infixr 6 _×ᴾ_

    _×ᴾ_ : Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ X
      (Unitᴰ C) ℓ
    (a ×ᴾ b) .F-ob (Γ , _ , x) = (FibPsh ℓ a Γ x × FibPsh ℓ b Γ x)
      , isSet× (isSetFibPsh ℓ a Γ x) (isSetFibPsh ℓ b Γ x)
    (a ×ᴾ b) .F-hom f (u , v) = FibᴰPsh ℓ a .F-hom f u , FibᴰPsh ℓ b .F-hom f v
    (a ×ᴾ b) .F-id = funExt λ uv →
      ≡-× (funExt⁻ (FibᴰPsh ℓ a .F-id) (uv .fst))
        (funExt⁻ (FibᴰPsh ℓ b .F-id) (uv .snd))
    (a ×ᴾ b) .F-seq f g = funExt λ uv →
      ≡-× (funExt⁻ (FibᴰPsh ℓ a .F-seq f g) (uv .fst))
        (funExt⁻ (FibᴰPsh ℓ b .F-seq f g) (uv .snd))

  module _ {X W : Presheaf C ℓ} {k : PSH {C = C} ℓ [ W , X ]}
    {c : Presheafᴰ W (Unitᴰ C) ℓ} where
    !ᴾ : PSHCod.Hom[ k ][ c , 𝟙ᴾ {X} ]
    !ᴾ = mkPsh ℓ
      ( (λ Γ z → (k .N-ob Γ (z .fst) , tt*) , refl)
      , λ ρ → funExt λ z → ΣPathP (funExt⁻ (k .N-hom ρ) (z .fst) , refl))

    !ᴾ-η : (hᴰ : PSHCod.Hom[ k ][ c , 𝟙ᴾ {X} ]) → !ᴾ ≡ hᴰ
    !ᴾ-η hᴰ = Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath λ i Γ z →
      hᴰ .snd (~ i) .N-ob Γ z , tt*)

    module _ (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
      ×ᴾ-intro : PSHCod.Hom[ k ][ c , a ] × PSHCod.Hom[ k ][ c , b ]
        → PSHCod.Hom[ k ][ c , a ×ᴾ b ]
      ×ᴾ-intro g = mkPsh ℓ
        ( (λ Γ z →
            (k .N-ob Γ (z .fst)
            , ptPsh ℓ (g .fst) .fst Γ z , ptPsh ℓ (g .snd) .fst Γ z)
            , refl)
        , λ ρ → funExt λ z → ΣPathP
            ( funExt⁻ (k .N-hom ρ) (z .fst)
            , ΣPathP
              ( FibPathPPsh ℓ (funExt⁻ (k .N-hom ρ) (z .fst))
                  (funExt⁻ (g .fst .fst .N-hom ρ) z)
              , FibPathPPsh ℓ (funExt⁻ (k .N-hom ρ) (z .fst))
                  (funExt⁻ (g .snd .fst .N-hom ρ) z))))

  module _ {X : Presheaf C ℓ} (a b : Presheafᴰ X (Unitᴰ C) ℓ) where
    ×ᴾπ₁ : PSHCod.Hom[ PSH.id ][ a ×ᴾ b , a ]
    ×ᴾπ₁ = mkPsh ℓ {P = a ×ᴾ b} {Q = a} ((λ Γ z → z .snd .fst) , λ ρ → refl)

    ×ᴾπ₂ : PSHCod.Hom[ PSH.id ][ a ×ᴾ b , b ]
    ×ᴾπ₂ = mkPsh ℓ {P = a ×ᴾ b} {Q = b} ((λ Γ z → z .snd .snd) , λ ρ → refl)

  private
    reindCod = ChosenReind.reind⟨_⟩ (PSHCodReind {C = C} ℓ)

  open UniversalElementⱽ'

  TerminalⱽPSHCod : (X : Presheaf C ℓ)
    → UniversalElementⱽ' (PSHCod ℓ) X UnitPshᴰ
  TerminalⱽPSHCod X .vertexⱽ = 𝟙ᴾ
  TerminalⱽPSHCod X .elementⱽ = tt
  TerminalⱽPSHCod X .universalⱽ _ .fst _ = !ᴾ
  TerminalⱽPSHCod X .universalⱽ _ .snd .fst _ = refl
  TerminalⱽPSHCod X .universalⱽ _ .snd .snd = !ᴾ-η

  TerminalsⱽPSHCod : Terminalsⱽ (PSHCod ℓ)
  TerminalsⱽPSHCod X = REPRⱽ (TerminalⱽPSHCod X)

  BinProductⱽPSHCod : {X : Presheaf C ℓ} (a b : Presheafᴰ X (Unitᴰ C) ℓ)
    → UniversalElementⱽ' (PSHCod ℓ) X (BinProductⱽSpec (PSHCod ℓ) a b)
  BinProductⱽPSHCod a b .vertexⱽ = a ×ᴾ b
  BinProductⱽPSHCod a b .elementⱽ = ×ᴾπ₁ a b , ×ᴾπ₂ a b
  BinProductⱽPSHCod a b .universalⱽ _ .fst = ×ᴾ-intro a b
  BinProductⱽPSHCod a b .universalⱽ _ .snd .fst g = ΣPathP
    ( Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _))
    , Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _)))
  BinProductⱽPSHCod a b .universalⱽ _ .snd .snd hᴰ =
    Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (funExt λ Γ → funExt λ z →
      ΣPathP (base Γ z
      , ΣPathP
        ( FibPathPPsh ℓ (base Γ z)
            (funExt⁻ (funExt⁻ (reind-fstPsh _ (hᴰ PSHCod.⋆ᴰ ×ᴾπ₁ a b)) Γ) z)
        , FibPathPPsh ℓ (base Γ z)
            (funExt⁻ (funExt⁻ (reind-fstPsh _ (hᴰ PSHCod.⋆ᴰ ×ᴾπ₂ a b)) Γ) z)))))
    where
    base : ∀ Γ z → _ ≡ hᴰ .fst .N-ob Γ z .fst
    base Γ z i = hᴰ .snd (~ i) .N-ob Γ z

  BinProductsⱽPSHCod : BinProductsⱽ (PSHCod ℓ)
  BinProductsⱽPSHCod a b .fst = a ×ᴾ b
  BinProductsⱽPSHCod a b .snd =
    improvePshIso (REPRⱽ (BinProductⱽPSHCod a b) .snd)
      ( (λ (_ , _ , k) hᴰ →
          reindCod (PSH.⋆IdR k) (hᴰ PSHCod.⋆ᴰ ×ᴾπ₁ a b)
          , reindCod (PSH.⋆IdR k) (hᴰ PSHCod.⋆ᴰ ×ᴾπ₂ a b))
      , funExt λ _ → funExt λ hᴰ → ΣPathP
          ( Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _))
          , Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _))))
      ((λ _ → ×ᴾ-intro a b) , refl)

  _ : ∀ {X W : Presheaf C ℓ} {a b : Presheafᴰ X (Unitᴰ C) ℓ} {k : PSH {C = C} ℓ
    [ W , X ]}
    {c : Presheafᴰ W (Unitᴰ C) ℓ} (hᴰ : PSHCod.Hom[ k ][ c , a ×ᴾ b ]) Γ z
    → BinProductsⱽPSHCod a b .snd .PshIso.trans .PshHom.N-ob (W , c , k) hᴰ
      .fst .fst .N-ob Γ z
      ≡ hᴰ .fst .N-ob Γ z .snd .fst .fst
  _ = λ hᴰ Γ z → refl

  module _ {X Y : Presheaf C ℓ} (f : PSH {C = C} ℓ [ Y , X ]) where
    private
      module X = PresheafNotation X

    Pull : Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ Y (Unitᴰ C) ℓ
    Pull Q .F-ob (Γ , _ , y) = FibPsh ℓ Q Γ (f .N-ob Γ y) , isSetFibPsh ℓ Q Γ _
    Pull Q .F-hom {x = Γ , _ , y} {y = Δ , _ , _} (ρ , _ , e) (w , p) =
      ∫ᴾ ℓ Q .F-hom ρ w
      , cong (ρ X.⋆_) p ∙ sym (funExt⁻ (f .N-hom ρ) y) ∙ cong (f .N-ob Δ) e
    Pull Q .F-id = funExt λ u →
      ΣPathPProp (λ _ → X.isSetPsh _ _) (funExt⁻ (∫ᴾ ℓ Q .F-id) (u .fst))
    Pull Q .F-seq g g' = funExt λ u →
      ΣPathPProp (λ _ → X.isSetPsh _ _)
        (funExt⁻ (∫ᴾ ℓ Q .F-seq (g .fst) (g' .fst)) (u .fst))

    module _ (Q : Presheafᴰ X (Unitᴰ C) ℓ) where
      pullπ : PSHCod.Hom[ PSH.id PSH.⋆ f ][ Pull Q , Q ]
      pullπ = mkPsh ℓ {P = Pull Q} {Q = Q} ((λ Γ z → z .snd) , λ ρ → refl)

      pullIntro : ∀ {W} {g : PSH {C = C} ℓ [ W , Y ]} {c : Presheafᴰ W (Unitᴰ C)
        ℓ}
        → PSHCod.Hom[ g PSH.⋆ f ][ c , Q ] → PSHCod.Hom[ g ][ c , Pull Q ]
      pullIntro {g = g} φ = mkPsh ℓ
        ( (λ Γ z → (g .N-ob Γ (z .fst) , ptPsh ℓ φ .fst Γ z) , refl)
        , λ ρ → funExt λ z →
            ΣPathP
              ( funExt⁻ (g .N-hom ρ) (z .fst)
              , FibPathPPsh ℓ (cong (f .N-ob _) (funExt⁻ (g .N-hom ρ) (z .fst)))
                  (funExt⁻ (φ .fst .N-hom ρ) z)))

      CartesianLiftPSHCod : UniversalElementⱽ' (PSHCod ℓ) Y
        (CartesianLiftPshSpec (PSH {C = C} ℓ [-, X ]) (PSHCod ℓ)
          (PSHCod ℓ [-][-, Q ]) f)
      CartesianLiftPSHCod .vertexⱽ = Pull Q
      CartesianLiftPSHCod .elementⱽ = pullπ
      CartesianLiftPSHCod .universalⱽ _ .fst = pullIntro
      CartesianLiftPSHCod .universalⱽ _ .snd .fst φ =
        Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _))
      CartesianLiftPSHCod .universalⱽ _ .snd .snd ψ =
        Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (funExt λ Γ → funExt λ z →
          ΣPathP (base Γ z
          , FibPathPPsh ℓ (cong (f .N-ob Γ) (base Γ z))
              (funExt⁻ (funExt⁻ (reind-fstPsh _ (ψ PSHCod.⋆ᴰ pullπ)) Γ) z))))
        where
        base : ∀ Γ z → _ ≡ ψ .fst .N-ob Γ z .fst
        base Γ z i = ψ .snd (~ i) .N-ob Γ z

  isFibrationPSHCod : isFibration (PSHCod {C = C} ℓ)
  isFibrationPSHCod Q Y f .fst = Pull f Q
  isFibrationPSHCod Q Y f .snd =
    improvePshIso (REPRⱽ (CartesianLiftPSHCod f Q) .snd)
      ( (λ _ hᴰ → reindCod (makeNatTransPath refl) (hᴰ PSHCod.⋆ᴰ pullπ f Q))
      , funExt λ _ → funExt λ hᴰ →
          Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind-fstPsh _ _)))
      ((λ _ → pullIntro f Q) , refl)

  _ : ∀ {X Y W : Presheaf C ℓ} {Q : Presheafᴰ X (Unitᴰ C) ℓ} {f : PSH {C = C} ℓ
    [ Y , X ]}
    {g : PSH {C = C} ℓ [ W , Y ]} {c : Presheafᴰ W (Unitᴰ C) ℓ}
    (hᴰ : PSHCod.Hom[ g ][ c , Pull f Q ]) Γ z
    → isFibrationPSHCod Q Y f .snd .PshIso.trans .PshHom.N-ob (W , c , g) hᴰ
      .fst .N-ob Γ z
      ≡ hᴰ .fst .N-ob Γ z .snd .fst
  _ = λ hᴰ Γ z → refl

  private
    module F^op = Fibers (PSHCod {C = C} ℓ ^opᴰ)

  reind^op-fstPsh : ∀ {X Y : Presheaf C ℓ} {f g : PSH {C = C} ℓ [ X , Y ]}
    {P : Presheafᴰ Y (Unitᴰ C) ℓ} {Q : Presheafᴰ X (Unitᴰ C) ℓ} (e : f ≡ g)
    (φ : PSHCod.Hom[ f ][ Q , P ])
    → F^op.reind {aᴰ = P} {bᴰ = Q} e φ .fst .N-ob ≡ φ .fst .N-ob
  reind^op-fstPsh {P = P} {Q} e φ =
    cong (λ z → z .snd .fst .N-ob)
      (sym (F^op.reind-filler {aᴰ = P} {bᴰ = Q} e))

  module _ {X Y : Presheaf C ℓ} (f : PSH {C = C} ℓ [ X , Y ]) where
    private
      module Y = PresheafNotation Y

    Push : Presheafᴰ X (Unitᴰ C) ℓ → Presheafᴰ Y (Unitᴰ C) ℓ
    Push P .F-ob (Γ , _ , y) =
      (Σ[ z ∈ ⟨ ∫ᴾ ℓ P .F-ob Γ ⟩ ] (f .N-ob Γ (z .fst) ≡ y))
      , isSetΣ (∫ᴾ ℓ P .F-ob Γ .snd) λ _ → isProp→isSet (Y.isSetPsh _ _)
    Push P .F-hom (ρ , _ , e) (z , p) =
      ∫ᴾ ℓ P .F-hom ρ z
      , funExt⁻ (f .N-hom ρ) (z .fst) ∙ cong (ρ Y.⋆_) p ∙ e
    Push P .F-id = funExt λ u →
      ΣPathPProp (λ _ → Y.isSetPsh _ _) (funExt⁻ (∫ᴾ ℓ P .F-id) (u .fst))
    Push P .F-seq g g' = funExt λ u →
      ΣPathPProp (λ _ → Y.isSetPsh _ _)
        (funExt⁻ (∫ᴾ ℓ P .F-seq (g .fst) (g' .fst)) (u .fst))

    module _ (P : Presheafᴰ X (Unitᴰ C) ℓ) where
      pushσ : PSHCod.Hom[ f PSH.⋆ PSH.id ][ P , Push P ]
      pushσ = mkPsh ℓ {P = P} {Q = Push P}
        ( (λ Γ z → (f .N-ob Γ (z .fst) , z , refl) , refl)
        , λ ρ → funExt λ z → ΣPathP
            ( funExt⁻ (f .N-hom ρ) (z .fst)
            , ΣPathPProp (λ _ → Y.isSetPsh _ _) refl))

      pushElim : ∀ {W} {g : PSH {C = C} ℓ [ Y , W ]} {c : Presheafᴰ W (Unitᴰ C)
        ℓ}
        → PSHCod.Hom[ f PSH.⋆ g ][ P , c ] → PSHCod.Hom[ g ][ Push P , c ]
      pushElim φ .fst .N-ob Γ w = φ .fst .N-ob Γ (w .snd .fst)
      pushElim φ .fst .N-hom ρ = funExt λ w →
        funExt⁻ (φ .fst .N-hom ρ) (w .snd .fst)
      pushElim {g = g} φ .snd = makeNatTransPath (funExt λ Γ → funExt λ w →
        (λ i → φ .snd i .N-ob Γ (w .snd .fst))
        ∙ cong (g .N-ob Γ) (w .snd .snd))

      OpcartesianLiftPSHCod : UniversalElementⱽ' (PSHCod ℓ ^opᴰ) Y
        (CartesianLiftPshSpec ((PSH {C = C} ℓ ^op) [-, X ]) (PSHCod ℓ ^opᴰ)
          ((PSHCod ℓ ^opᴰ) [-][-, P ]) f)
      OpcartesianLiftPSHCod .vertexⱽ = Push P
      OpcartesianLiftPSHCod .elementⱽ = pushσ
      OpcartesianLiftPSHCod .universalⱽ _ .fst = pushElim
      OpcartesianLiftPSHCod .universalⱽ _ .snd .fst φ =
        Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind^op-fstPsh _ _))
      OpcartesianLiftPSHCod .universalⱽ _ .snd .snd ψ =
        Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (funExt λ Γ → funExt λ w →
          funExt⁻ (funExt⁻ (reind^op-fstPsh _ (pushσ PSHCod.⋆ᴰ ψ)) Γ) (w .snd
            .fst)
          ∙ cong (ψ .fst .N-ob Γ) (λ i →
              w .snd .snd i , w .snd .fst , λ j → w .snd .snd (i ∧ j))))

  isOpfibrationPSHCod : isFibration (PSHCod {C = C} ℓ ^opᴰ)
  isOpfibrationPSHCod P Y f .fst = Push f P
  isOpfibrationPSHCod P Y f .snd =
    improvePshIso (REPRⱽ (OpcartesianLiftPSHCod f P) .snd)
      ( (λ _ hᴰ → reindCod (makeNatTransPath refl) (pushσ f P PSHCod.⋆ᴰ hᴰ))
      , funExt λ _ → funExt λ hᴰ →
          Codomain≡ (PSH {C = C} ℓ) refl (makeNatTransPath (reind^op-fstPsh _ _)))
      ((λ _ → pushElim f P) , refl)

  _ : ∀ {X Y W : Presheaf C ℓ} {P : Presheafᴰ X (Unitᴰ C) ℓ} {f : PSH {C = C} ℓ
    [ X , Y ]}
    {g : PSH {C = C} ℓ [ Y , W ]} {c : Presheafᴰ W (Unitᴰ C) ℓ}
    (hᴰ : PSHCod.Hom[ g ][ Push f P , c ]) Γ z
    → isOpfibrationPSHCod P Y f .snd .PshIso.trans .PshHom.N-ob (W , c , g) hᴰ
      .fst .N-ob Γ z
      ≡ hᴰ .fst .N-ob Γ (f .N-ob Γ (z .fst) , z , refl)
  _ = λ hᴰ Γ z → refl

module _ {C : Category ℓC ℓC'} {ℓ : Level} where
  PSHCodCCⱽ : CartesianCategoryⱽ (PSH {C = C} ℓ) _ _
  PSHCodCCⱽ = cartesiancategoryⱽ (PSHCod ℓ) TerminalsⱽPSHCod BinProductsⱽPSHCod
    isFibrationPSHCod
