{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.ωSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.ωSet hiding (next)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More using (Idᴰ)
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.FixedPoint
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.ChangeOfObjects
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Instances.Codomain.Base hiding (Δ)

open Functor
open Functorᴰ

module _ {ℓ : Level} where
  ωHom≡ : {X : ωType ℓ} {Y : ωSet ℓ} {f g : ωHom X (Y .fst)}
    → f .fst ≡ g .fst → f ≡ g
  ωHom≡ {Y = Y} =
    ΣPathPProp (λ _ → isPropΠ4 λ n _ _ _ → Y .snd n _ _)

module _ (ℓ : Level) where
  ΔF : Functor (SET ℓ) (ωSET ℓ)
  ΔF .F-ob X = Δ ⟨ X ⟩ , λ _ → X .snd
  ΔF .F-hom f = (λ _ → f) , λ _ x x' e → cong f e
  ΔF .F-id = refl
  ΔF .F-seq f g = refl

  ωFam : hSet ℓ → Type (ℓ-suc ℓ)
  ωFam X = ⟨ X ⟩ → ωSet ℓ

  module _ {X : hSet ℓ} (P : ωFam X) where
    ∫ωT : ωType ℓ
    ∫ωT .fst n = Σ[ x ∈ ⟨ X ⟩ ] P x .fst .fst n
    ∫ωT .snd n z = z .fst , P (z .fst) .fst .snd n (z .snd)

    ∫ω : ωSet ℓ
    ∫ω = ∫ωT , λ n → isSetΣ (X .snd) λ x → P x .snd n

    πω : ωHom ∫ωT (Δ ⟨ X ⟩)
    πω .fst n = fst
    πω .snd n z z' e = cong fst e

  Σω : {X : hSet ℓ} → ωFam X → Categoryᴰ.ob[ Codomain (ωSET ℓ) ] (ΔF ⟅ X ⟆)
  Σω P = ∫ω P , πω P

  ωSETCod : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ
  ωSETCod = ChangeOfObjectsᴰ
    (reindexChosenReind (Codomain (ωSET ℓ)) ΔF ⦃ CodomainReind (ωSET ℓ) ⦄) Σω

  ωSETCodReind : ChosenReind ωSETCod
  ωSETCodReind = ChangeOfObjectsReind _ Σω
    (reindexReind (Codomain (ωSET ℓ)) ΔF ⦃ CodomainReind (ωSET ℓ) ⦄)

  private
    module ωSETCod = Categoryᴰ ωSETCod

  module _ {Y : hSet ℓ} (Q : ωFam Y) (y : ⟨ Y ⟩) where
    FibωT : ωType ℓ
    FibωT .fst n = Σ[ w ∈ ∫ωT Q .fst n ] (w .fst ≡ y)
    FibωT .snd n u = ∫ωT Q .snd n (u .fst) , u .snd

    Fibω : ωSet ℓ
    Fibω = FibωT , λ n →
      isSetΣ (∫ω Q .snd n) λ w → isProp→isSet (Y .snd _ _)

  FibωPathP : {Y : hSet ℓ} {Q : ωFam Y} {y y' : ⟨ Y ⟩} (r : y ≡ y') {n : ℕ}
    {u : FibωT Q y .fst n} {u' : FibωT Q y' .fst n} → u .fst ≡ u' .fst
    → PathP (λ i → FibωT Q (r i) .fst n) u u'
  FibωPathP {Y = Y} r {u = u} {u'} p i .fst = p i
  FibωPathP {Y = Y} r {u = u} {u'} p i .snd =
    isProp→PathP (λ i → Y .snd (p i .fst) (r i)) (u .snd) (u' .snd) i

  Pointwiseω : {X Y : hSet ℓ} (h : ⟨ X ⟩ → ⟨ Y ⟩) (P : ωFam X) (Q : ωFam Y)
    → Type ℓ
  Pointwiseω h P Q =
    Σ[ g ∈ (∀ n (z : ∫ωT P .fst n) → FibωT Q (h (z .fst)) .fst n) ]
      (∀ n z z' → ∫ωT P .snd n z ≡ z'
        → ∫ωT Q .snd n (g (suc n) z .fst) ≡ g n z' .fst)

  module _ {X Y : hSet ℓ} {h : ⟨ X ⟩ → ⟨ Y ⟩} {P : ωFam X} {Q : ωFam Y} where
    mkω : Pointwiseω h P Q → ωSETCod.Hom[ h ][ P , Q ]
    mkω g .fst .fst n z = g .fst n z .fst
    mkω g .fst .snd = g .snd
    mkω g .snd = ωHom≡ {Y = ΔF ⟅ Y ⟆} λ i n z → g .fst n z .snd i

    ptω : ωSETCod.Hom[ h ][ P , Q ] → Pointwiseω h P Q
    ptω φ .fst n z .fst = φ .fst .fst n z
    ptω φ .fst n z .snd i = φ .snd i .fst n z
    ptω φ .snd = φ .fst .snd

  module _ {X Y : hSet ℓ} {h h' : ⟨ X ⟩ → ⟨ Y ⟩} {P : ωFam X} {Q : ωFam Y}
    where
    ωSETCodHom≡ : (q : h ≡ h') {φ : ωSETCod.Hom[ h ][ P , Q ]}
      {ψ : ωSETCod.Hom[ h' ][ P , Q ]}
      → φ .fst .fst ≡ ψ .fst .fst
      → PathP (λ i → ωSETCod.Hom[ q i ][ P , Q ]) φ ψ
    ωSETCodHom≡ q p = Codomain≡ (ωSET ℓ) (cong (ΔF .F-hom) q) (ωHom≡ {Y = ∫ω Q} p)

  _ : {X Y Z : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {g : ⟨ Y ⟩ → ⟨ Z ⟩}
    {P : ωFam X} {Q : ωFam Y} {R : ωFam Z}
    (φ : ωSETCod.Hom[ f ][ P , Q ]) (ψ : ωSETCod.Hom[ g ][ Q , R ])
    → ∀ n z → (φ ωSETCod.⋆ᴰ ψ) .fst .fst n z ≡ ψ .fst .fst n (φ .fst .fst n z)
  _ = λ φ ψ n z → refl

  _ : {X Y : hSet ℓ} {f g : ⟨ X ⟩ → ⟨ Y ⟩} {P : ωFam X} {Q : ωFam Y}
    (e : f ≡ g) (φ : ωSETCod.Hom[ f ][ P , Q ])
    → ChosenReind.reind⟨_⟩ ωSETCodReind e φ .fst ≡ φ .fst
  _ = λ e φ → refl

instance
  ωSETCodReindInst : ∀ {ℓ} → ChosenReind (ωSETCod ℓ)
  ωSETCodReindInst = ωSETCodReind _

module _ {ℓ : Level} where
  private
    module ωSETCod = Categoryᴰ (ωSETCod ℓ)
    module F = Fibers (ωSETCod ℓ)

  reind-fstω : ∀ {X Y : hSet ℓ} {f g : ⟨ X ⟩ → ⟨ Y ⟩}
    {P : ωFam ℓ X} {Q : ωFam ℓ Y} (e : f ≡ g)
    (φ : ωSETCod.Hom[ f ][ P , Q ])
    → F.reind {aᴰ = P} {bᴰ = Q} e φ .fst .fst ≡ φ .fst .fst
  reind-fstω {P = P} {Q} e φ =
    cong (λ z → z .snd .fst .fst) (sym (F.reind-filler {aᴰ = P} {bᴰ = Q} e))

  module _ {X : hSet ℓ} where
    𝟙ω : ωFam ℓ X
    𝟙ω x = ωUnit* , λ _ → isSetUnit*

  module _ {X W : hSet ℓ} {k : ⟨ W ⟩ → ⟨ X ⟩} {c : ωFam ℓ W} where
    !ω : ωSETCod.Hom[ k ][ c , 𝟙ω {X} ]
    !ω = mkω ℓ ((λ n z → (k (z .fst) , tt*) , refl)
      , λ n z z' e → cong (λ z → k (z .fst) , tt*) e)

    !ω-η : (hᴰ : ωSETCod.Hom[ k ][ c , 𝟙ω {X} ]) → !ω ≡ hᴰ
    !ω-η hᴰ = ωSETCodHom≡ ℓ refl λ i n z → hᴰ .snd (~ i) .fst n z , tt*

  open UniversalElementⱽ'

  TerminalⱽωSETCod : (X : hSet ℓ) → UniversalElementⱽ' (ωSETCod ℓ) X UnitPshᴰ
  TerminalⱽωSETCod X .vertexⱽ = 𝟙ω
  TerminalⱽωSETCod X .elementⱽ = tt
  TerminalⱽωSETCod X .universalⱽ _ .fst _ = !ω
  TerminalⱽωSETCod X .universalⱽ _ .snd .fst _ = refl
  TerminalⱽωSETCod X .universalⱽ _ .snd .snd = !ω-η

  TerminalsⱽωSETCod : Terminalsⱽ (ωSETCod ℓ)
  TerminalsⱽωSETCod X = REPRⱽ (TerminalⱽωSETCod X)

  module _ {X Y : hSet ℓ} (f : ⟨ X ⟩ → ⟨ Y ⟩) where
    Pullω : ωFam ℓ Y → ωFam ℓ X
    Pullω Q x = Fibω ℓ Q (f x)

    pullωπ : (Q : ωFam ℓ Y) → ωSETCod.Hom[ f ][ Pullω Q , Q ]
    pullωπ Q = mkω ℓ ((λ n z → z .snd) , λ n z z' e i → e i .snd .fst)

  module _ {X Y : hSet ℓ} (f : ⟨ Y ⟩ → ⟨ X ⟩) (Q : ωFam ℓ X) where
    pullωIntro : ∀ {W} {g : ⟨ W ⟩ → ⟨ Y ⟩} {c : ωFam ℓ W}
      → ωSETCod.Hom[ (λ w → f (g w)) ][ c , Q ]
      → ωSETCod.Hom[ g ][ c , Pullω f Q ]
    pullωIntro {g = g} φ = mkω ℓ
      ( (λ n z → (g (z .fst) , ptω ℓ φ .fst n z) , refl)
      , λ n z z' e → ΣPathP
          ( cong (λ z → g (z .fst)) e
          , FibωPathP ℓ (cong (λ z → f (g (z .fst))) e)
              (φ .fst .snd n z z' e)))

    CartesianLiftωSETCod : UniversalElementⱽ' (ωSETCod ℓ) Y
      (CartesianLiftPshSpec (SET ℓ [-, X ]) (ωSETCod ℓ) (ωSETCod ℓ [-][-, Q ]) f)
    CartesianLiftωSETCod .vertexⱽ = Pullω f Q
    CartesianLiftωSETCod .elementⱽ = pullωπ f Q
    CartesianLiftωSETCod .universalⱽ _ .fst = pullωIntro
    CartesianLiftωSETCod .universalⱽ _ .snd .fst φ =
      ωSETCodHom≡ ℓ refl (reind-fstω _ _)
    CartesianLiftωSETCod .universalⱽ _ .snd .snd ψ =
      ωSETCodHom≡ ℓ refl (funExt λ n → funExt λ z →
        ΣPathP (base n z
        , FibωPathP ℓ (cong f (base n z))
            (funExt⁻ (funExt⁻ (reind-fstω _ (ψ ωSETCod.⋆ᴰ pullωπ f Q)) n) z)))
      where
      base : ∀ n z → _ ≡ ψ .fst .fst n z .fst
      base n z i = ψ .snd (~ i) .fst n z

  isFibrationωSETCod : isFibration (ωSETCod ℓ)
  isFibrationωSETCod Q Y f .fst = Pullω f Q
  isFibrationωSETCod Q Y f .snd =
    improvePshIso (REPRⱽ (CartesianLiftωSETCod f Q) .snd)
      ( (λ _ hᴰ → hᴰ ωSETCod.⋆ᴰ pullωπ f Q)
      , funExt λ _ → funExt λ hᴰ → ωSETCodHom≡ ℓ refl (reind-fstω _ _))
      ((λ _ → pullωIntro f Q) , refl)

module _ {ℓ : Level} where
  private
    module ωSETCod = Categoryᴰ (ωSETCod ℓ)
    module F = Fibers (ωSETCod ℓ)

  module _ {X : hSet ℓ} (P : ωFam ℓ X) where
    ▷ω : ωFam ℓ X
    ▷ω x = ▷ωSet (Fibω ℓ P x)

  module _ {X Y : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {P : ωFam ℓ X} {Q : ωFam ℓ Y}
    (φ : ωSETCod.Hom[ f ][ P , Q ]) where
    ▷ωHom-pt : ∀ n (z : ∫ωT ℓ (▷ω P) .fst n)
      → FibωT ℓ (▷ω Q) (f (z .fst)) .fst n
    ▷ωHom-pt zero z = (f (z .fst) , tt*) , refl
    ▷ωHom-pt (suc n) (x , w , e) =
      (f x , ptω ℓ φ .fst n w .fst , ptω ℓ φ .fst n w .snd ∙ cong f e) , refl

    ▷ωHom-nat : ∀ n z z' → ∫ωT ℓ (▷ω P) .snd n z ≡ z'
      → ∫ωT ℓ (▷ω Q) .snd n (▷ωHom-pt (suc n) z .fst) ≡ ▷ωHom-pt n z' .fst
    ▷ωHom-nat zero z z' p i = f (p i .fst) , tt*
    ▷ωHom-nat (suc n) z z' p = ΣPathP
      ( (λ i → f (p i .fst))
      , FibωPathP ℓ (λ i → f (p i .fst))
          (φ .fst .snd n (z .snd .fst) (z' .snd .fst) λ i → p i .snd .fst))

    ▷ωHom : ωSETCod.Hom[ f ][ ▷ω P , ▷ω Q ]
    ▷ωHom = mkω ℓ (▷ωHom-pt , ▷ωHom-nat)

  module _ {X : hSet ℓ} {P : ωFam ℓ X} where
    ▷ωHom-id-pt : ∀ n (z : ∫ωT ℓ (▷ω P) .fst n)
      → ▷ωHom-pt (ωSETCod.idᴰ {p = P}) n z .fst ≡ z
    ▷ωHom-id-pt zero z = refl
    ▷ωHom-id-pt (suc n) z = ΣPathP (refl , FibωPathP ℓ refl refl)

  module _ {X Y Z : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {g : ⟨ Y ⟩ → ⟨ Z ⟩}
    {P : ωFam ℓ X} {Q : ωFam ℓ Y} {R : ωFam ℓ Z}
    (φ : ωSETCod.Hom[ f ][ P , Q ]) (ψ : ωSETCod.Hom[ g ][ Q , R ]) where
    ▷ωHom-seq-pt : ∀ n (z : ∫ωT ℓ (▷ω P) .fst n)
      → ▷ωHom-pt (φ ωSETCod.⋆ᴰ ψ) n z .fst
        ≡ ▷ωHom-pt ψ n (▷ωHom-pt φ n z .fst) .fst
    ▷ωHom-seq-pt zero z = refl
    ▷ωHom-seq-pt (suc n) z = ΣPathP (refl , FibωPathP ℓ refl refl)

  ▷ⱽω : Functorⱽ (ωSETCod ℓ) (ωSETCod ℓ)
  ▷ⱽω .F-obᴰ = ▷ω
  ▷ⱽω .F-homᴰ = ▷ωHom
  ▷ⱽω .F-idᴰ = ωSETCodHom≡ ℓ refl (funExt λ n → funExt (▷ωHom-id-pt n))
  ▷ⱽω .F-seqᴰ φ ψ =
    ωSETCodHom≡ ℓ refl (funExt λ n → funExt (▷ωHom-seq-pt φ ψ n))

  module _ {X : hSet ℓ} (P : ωFam ℓ X) where
    nextω-pt : ∀ n (z : ∫ωT ℓ P .fst n) → FibωT ℓ (▷ω P) (z .fst) .fst n
    nextω-pt zero z = (z .fst , tt*) , refl
    nextω-pt (suc n) (x , p) = (x , (x , P x .fst .snd n p) , refl) , refl

    nextω-nat : ∀ n z z' → ∫ωT ℓ P .snd n z ≡ z'
      → ∫ωT ℓ (▷ω P) .snd n (nextω-pt (suc n) z .fst) ≡ nextω-pt n z' .fst
    nextω-nat zero z z' e i = e i .fst , tt*
    nextω-nat (suc n) z z' e i =
      e i .fst , (e i .fst , P (e i .fst) .fst .snd n (e i .snd)) , refl

    nextω : ωSETCod.Hom[ (λ x → x) ][ P , ▷ω P ]
    nextω = mkω ℓ (nextω-pt , nextω-nat)

  module _ {X Y : hSet ℓ} {f : ⟨ X ⟩ → ⟨ Y ⟩} {P : ωFam ℓ X} {Q : ωFam ℓ Y}
    (fᴰ : ωSETCod.Hom[ f ][ P , Q ]) where
    nextω-natural-pt : ∀ n (z : ∫ωT ℓ P .fst n)
      → nextω-pt Q n (fᴰ .fst .fst n z) .fst
        ≡ ▷ωHom-pt fᴰ n (nextω-pt P n z .fst) .fst
    nextω-natural-pt zero z i = ptω ℓ fᴰ .fst 0 z .snd i , tt*
    nextω-natural-pt (suc n) z = ΣPathP
      ( ptω ℓ fᴰ .fst (suc n) z .snd
      , FibωPathP ℓ (ptω ℓ fᴰ .fst (suc n) z .snd)
          (fᴰ .fst .snd n z (z .fst , P (z .fst) .fst .snd n (z .snd)) refl))

  nextⱽω : NatTransᴰ (idTrans Id) Idᴰ ▷ⱽω
  nextⱽω .NatTransᴰ.N-obᴰ = nextω
  nextⱽω .NatTransᴰ.N-homᴰ {f = f} fᴰ =
    ωSETCodHom≡ ℓ (idTrans (Id {C = SET ℓ}) .NatTrans.N-hom f)
      (funExt λ n → funExt (nextω-natural-pt fᴰ n))

  module _ {X : hSet ℓ} {A : ωFam ℓ X}
    (f : ωSETCod.Hom[ (λ x → x) ][ ▷ω A , A ]) where
    gfixω-it : ∀ n x → FibωT ℓ A x .fst n
    gfixω-it zero x = ptω ℓ f .fst zero (x , tt*)
    gfixω-it (suc n) x = ptω ℓ f .fst (suc n) (x , gfixω-it n x)

    gfixω-nat : ∀ n x
      → ∫ωT ℓ A .snd n (gfixω-it (suc n) x .fst) ≡ gfixω-it n x .fst
    gfixω-nat zero x = f .fst .snd zero (x , gfixω-it zero x) (x , tt*) refl
    gfixω-nat (suc n) x = f .fst .snd (suc n) (x , gfixω-it (suc n) x)
      (x , gfixω-it n x) (cong (x ,_) (FibωPathP ℓ refl (gfixω-nat n x)))

    gfixω : ωSETCod.Hom[ (λ x → x) ][ 𝟙ω , A ]
    gfixω = mkω ℓ
      ( (λ n z → gfixω-it n (z .fst))
      , λ n z z' e → gfixω-nat n (z .fst)
          ∙ cong (λ x → gfixω-it n x .fst) (cong fst e))

    gfixω-fixed-pt : ∀ n (z : ∫ωT ℓ (𝟙ω {X = X}) .fst n)
      → f .fst .fst n (nextω-pt A n (gfixω-it n (z .fst) .fst) .fst)
        ≡ gfixω-it n (z .fst) .fst
    gfixω-fixed-pt zero (x , _) =
      cong (λ y → gfixω-it zero y .fst) (gfixω-it zero x .snd)
    gfixω-fixed-pt (suc n) (x , _) =
      cong (λ z → f .fst .fst (suc n) z)
        (ΣPathP (gfixω-it (suc n) x .snd
          , FibωPathP ℓ (gfixω-it (suc n) x .snd) (gfixω-nat n x)))

    gfixω-fixed : gfixω F.⋆ⱽ (nextω A F.⋆ⱽ f) ≡ gfixω
    gfixω-fixed = ωSETCodHom≡ ℓ refl
      (reind-fstω _ _
      ∙ cong (λ k n z → k n (gfixω-it n (z .fst) .fst)) (reind-fstω _ _)
      ∙ funExt λ n → funExt (gfixω-fixed-pt n))

  open GuardedLogic

  ωSETCod-Guarded : GuardedLogic (SET ℓ) (ℓ-suc ℓ) ℓ
  ωSETCod-Guarded .Cᴰ = ωSETCod ℓ
  ωSETCod-Guarded .▷ⱽ = ▷ⱽω
  ωSETCod-Guarded .next = nextⱽω
  ωSETCod-Guarded .isFibCᴰ = isFibrationωSETCod
  ωSETCod-Guarded .termⱽ = TerminalsⱽωSETCod
  ωSETCod-Guarded .gfpⱽ f .fst = gfixω f
  ωSETCod-Guarded .gfpⱽ f .snd = gfixω-fixed f
