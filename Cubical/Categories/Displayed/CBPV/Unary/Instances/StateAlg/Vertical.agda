-- Vertical multiplicative structure for the displayed model of state algebras.
--
-- The most interesting observation here is that the Fⱽ universal
-- property is naturally defined as a composition of Fⱽ for [ret] with
-- a general pushforward for homomorphisms.
--
-- The two opcartesian lifts have a lot of reinds, despite the use of
-- strictly unital and associative homomorphisms. TODO: experiment
-- with Eq-Fiber version.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Vertical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base

private
  variable
    ℓ : Level

  StateAlgCBPVIdR : ∀ ℓ → EqPsh.EqIdR
    (∫C (StateAlgCBPV {ℓ = ℓ} .fst))
  StateAlgCBPVIdR ℓ {x = 𝒱 , A} {y = 𝒱 , B} f = Eq.refl
  StateAlgCBPVIdR ℓ {x = 𝒱 , A} {y = 𝓒 , B} f = Eq.pathToEq
    (Category.⋆IdR (∫C (StateAlgCBPV {ℓ = ℓ} .fst)) f)
  StateAlgCBPVIdR ℓ {x = 𝓒 , A} {y = 𝒱 , B} ()
  StateAlgCBPVIdR ℓ {x = 𝓒 , A} {y = 𝓒 , B} f = Eq.refl

  StateAlgCBPVAssoc : ∀ ℓ → EqPsh.ReprEqAssoc
    (∫C (StateAlgCBPV {ℓ = ℓ} .fst))
  StateAlgCBPVAssoc ℓ (𝒱 , A)
    {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ (𝓒 , B)
    {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ x f g p f⋆g e = Eq.pathToEq
    (sym (C.⋆Assoc f g p) ∙ cong (λ fg → fg C.⋆ p) (Eq.eqToPath e))
    where module C = Category (∫C (StateAlgCBPV {ℓ = ℓ} .fst))

StateAlgCBPVHasUⱽ : (ℓ : Level) → Type _
StateAlgCBPVHasUⱽ ℓ = hasUⱽ (StateAlgCBPVᴰ ℓ ℓ)

StateAlgCBPVHasFⱽ : (ℓ : Level) → Type _
StateAlgCBPVHasFⱽ ℓ = hasFⱽ (StateAlgCBPVᴰ ℓ ℓ)

-- The U lift is the usual reindexing of a family along the underlying
-- function.
module _ {A : hSet ℓ} {B : StateAlgebra ℓ}
  (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
  (Bᴰ :
    Σ[ Xᴰ ∈ (⟨ B .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (B .snd) (λ y → ⟨ Xᴰ y ⟩))
  where

  StateAlgCBPV-U-obⱽ : ⟨ A ⟩ → hSet ℓ
  StateAlgCBPV-U-obⱽ x = Bᴰ .fst (f x)

  StateAlgCBPV-forceⱽ :
    ∀ x → ⟨ StateAlgCBPV-U-obⱽ x ⟩ → ⟨ Bᴰ .fst (f x) ⟩
  StateAlgCBPV-forceⱽ _ xᴰ = xᴰ

private
  StateAlgCBPV-U-base : ∀ {ℓ} {A : hSet ℓ} {B : StateAlgebra ℓ} →
    (⟨ A ⟩ → ⟨ B .fst ⟩) →
    (∫C (StateAlgCBPV {ℓ = ℓ} .fst)) [ (𝒱 , A) , (𝓒 , B) ]
  StateAlgCBPV-U-base f = _ , f

  StateAlgCBPV-U-EqLift : ∀ {ℓ} {A : hSet ℓ} {B : StateAlgebra ℓ}
    (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
    (Bᴰ : Σ[ Xᴰ ∈ (⟨ B .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (B .snd) (λ y → ⟨ Xᴰ y ⟩))
    → EqPsh.CartesianLift (StateAlgCBPVᴰ ℓ ℓ)
        (StateAlgCBPVAssoc ℓ) (StateAlgCBPV-U-base f) Bᴰ
  StateAlgCBPV-U-EqLift {ℓ} {A} {B} f Bᴰ =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue
    where
    ue : EqPsh.CartesianLiftUE (StateAlgCBPVᴰ ℓ ℓ)
      (StateAlgCBPVAssoc ℓ) (StateAlgCBPVIdR ℓ)
      (StateAlgCBPV-U-base f) Bᴰ
    ue .EqPsh.UEⱽ.v = StateAlgCBPV-U-obⱽ f Bᴰ
    ue .EqPsh.UEⱽ.e = StateAlgCBPV-forceⱽ f Bᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .fst = λ z → z
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , Z) , Zᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , Z) , Zᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , Z) , Zᴰ , ()) .snd .snd

StateAlgCBPV-Uⱽ : {ℓ : Level} → StateAlgCBPVHasUⱽ ℓ
StateAlgCBPV-Uⱽ {ℓ} {A = A} {B = B} f Bᴰ =
  EqCartesianLift→CartesianLift
    (StateAlgCBPVAssoc ℓ) (StateAlgCBPVᴰ ℓ ℓ) Bᴰ (𝒱 , A)
    (StateAlgCBPV-U-base f)
    (StateAlgCBPV-U-EqLift f Bᴰ)
module _ {A : hSet ℓ} (Aᴰ : ⟨ A ⟩ → hSet ℓ) where
  FreeStateAlgebraᴰ :
    Σ[ Xᴰ ∈ (⟨ FreeStateAlgebra A .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (FreeStateAlgebra A .snd) (λ s → ⟨ Xᴰ s ⟩)
  FreeStateAlgebraᴰ .fst s .fst = ∀ b → ⟨ Aᴰ (s b .snd) ⟩
  FreeStateAlgebraᴰ .fst s .snd = isSetΠ (λ b → Aᴰ (s b .snd) .snd)
  FreeStateAlgebraᴰ .snd = FreeStateAlgᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩)

StateAlgCBPV-η-lift : ∀ {A : hSet ℓ} (Aᴰ : ⟨ A ⟩ → hSet ℓ)
  → CartesianLift ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
      (_ , η ⟨ A ⟩) Aᴰ
StateAlgCBPV-η-lift {ℓ = ℓ} {A = A} Aᴰ = UniversalElementⱽ'.REPRⱽ η-ue
  where
  module C = Category (∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ))
  module Cᴰ = Fibers ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
  module Dᴰ = Fibers (STATEALGᴰ ℓ ℓ)

  η-ue : UniversalElementⱽ' ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
    (𝓒 , FreeStateAlgebra A)
    (CartesianLiftPshSpec
      ((∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ)) [-, (𝒱 , A) ])
      ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
      (((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ) [-][-, Aᴰ ])
      (_ , η ⟨ A ⟩))

  recHom≡ : ∀ (Z : StateAlgebra ℓ) (ϕ : StateAlgHom (FreeStateAlgebra A) Z)
    → ( recFSA-f ⟨ A ⟩ (Z .snd) (ϕ .fst ∘ η ⟨ A ⟩)
      , recFSA ⟨ A ⟩ (Z .snd) (ϕ .fst ∘ η ⟨ A ⟩)) ≡ ϕ
  recHom≡ Z ϕ = StateAlgHom≡ _ ϕ
    (funExt (recFSA-η ⟨ A ⟩ (Z .snd) (ϕ .snd)))

  η-ue .UniversalElementⱽ'.vertexⱽ = FreeStateAlgebraᴰ Aᴰ
  η-ue .UniversalElementⱽ'.elementⱽ = ηᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩)
  η-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ϕ) .fst γᴰ =
    Dᴰ.reind (recHom≡ Z (ϕ .snd))
      ( recFSAᴰ-f {Xᴰ = λ x → ⟨ Aᴰ x ⟩} (Zᴰ .snd)
          (ϕ .snd .fst ∘ η ⟨ A ⟩) γᴰ (Z .fst .snd)
      , recFSAᴰ {Xᴰ = λ x → ⟨ Aᴰ x ⟩} (Zᴰ .snd)
          (ϕ .snd .fst ∘ η ⟨ A ⟩) γᴰ (Z .fst .snd))
  η-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ϕ) .snd .fst γᴰ =
    -- Yikes, all of this just to apply recFSAᴰ-β
    -- TODO: improve the Spec so this is just recFSAᴰ-β
    Cᴰ.rectifyOut {e' = refl} $
      Cᴰ.reind-filler⁻ _
      ∙ Cᴰ.≡in {pth = refl} (funExt λ x → funExt λ xᴰ →
        hSetReasoning.rectifyOut (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩) $
          cong
            (λ q →
              q .fst .fst (η ⟨ A ⟩ x) ,
              q .snd .fst (η ⟨ A ⟩ x) (λ _ → xᴰ))
            (Dᴰ.reind-filler⁻
              {p =
                ( recFSAᴰ-f {Xᴰ = λ x → ⟨ Aᴰ x ⟩} (Zᴰ .snd)
                    (ϕ .snd .fst ∘ η ⟨ A ⟩) γᴰ (Z .fst .snd)
                , recFSAᴰ {Xᴰ = λ x → ⟨ Aᴰ x ⟩} (Zᴰ .snd)
                    (ϕ .snd .fst ∘ η ⟨ A ⟩) γᴰ (Z .fst .snd))}
              (recHom≡ Z (ϕ .snd)))
          ∙ StateAlgᴰ.≡in (Zᴰ .snd)
              (recFSAᴰ-β {Xᴰ = λ x → ⟨ Aᴰ x ⟩} (Zᴰ .snd)
                (ϕ .snd .fst ∘ η ⟨ A ⟩) γᴰ (Z .fst .snd) x xᴰ))
  η-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ϕ) .snd .snd ψᴰ =
    cong (η-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ϕ) .fst)
      (Cᴰ.rectifyOut {e' = refl} (Cᴰ.reind-filler⁻ _))
    ∙ (Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.reind-filler⁻ (recHom≡ Z (ϕ .snd))
        ∙ Dᴰ.≡in {pth = recHom≡ Z (ϕ .snd)}
          (ΣPathPProp
            (λ fᴰ → isPropHomoᴰ (λ z → Zᴰ .fst z .snd))
            (funExt λ s → funExt λ sᴰ →
              recFSAᴰ-η (λ x → ⟨ Aᴰ x ⟩) (Zᴰ .snd)
                (ψᴰ .fst) (ϕ .snd .snd) (ψᴰ .snd)
                (Z .fst .snd) s sᴰ)))

module _ {B B' : StateAlgebra ℓ} (ϕ : StateAlgHom B B')
  (Bᴰ : Σ[ Xᴰ ∈ (⟨ B .fst ⟩ → hSet ℓ) ]
    StateAlgᴰ (B .snd) (λ x → ⟨ Xᴰ x ⟩)) where

  StateAlgCBPV-push-obᴰ :
    Σ[ Xᴰ ∈ (⟨ B' .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (B' .snd) (λ x → ⟨ Xᴰ x ⟩)
  StateAlgCBPV-push-obᴰ .fst x .fst =
    push-Xᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) x
  StateAlgCBPV-push-obᴰ .fst x .snd = isSetΣ
    (isSetΣ (B .fst .snd) (λ _ → isProp→isSet (B' .fst .snd _ _)))
    (λ b → Bᴰ .fst (b .fst) .snd)
  StateAlgCBPV-push-obᴰ .snd = push (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)

StateAlgCBPV-push-lift :
  ∀ {B B' : StateAlgebra ℓ} (ϕ : StateAlgHom B B')
    (Bᴰ : Σ[ Xᴰ ∈ (⟨ B .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (B .snd) (λ x → ⟨ Xᴰ x ⟩))
  → CartesianLift ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ) (_ , ϕ) Bᴰ
StateAlgCBPV-push-lift {ℓ = ℓ} {B = B} {B' = B'} ϕ Bᴰ =
  UniversalElementⱽ'.REPRⱽ push-ue
  where
  module C = Category (∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ))
  module Cᴰ = Fibers ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
  module Dᴰ = Fibers (STATEALGᴰ ℓ ℓ)

  pushBase : (∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ))
    [ (𝓒 , B') , (𝓒 , B) ]
  pushBase = _ , ϕ

  push-ue : UniversalElementⱽ' ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
    (𝓒 , B')
    (CartesianLiftPshSpec
      ((∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ)) [-, (𝓒 , B) ])
      ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
      (((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ) [-][-, Bᴰ ]) pushBase)

  canonical-fᴰ : ∀ {Z : StateAlgebra ℓ}
    (ψ : StateAlgHom B' Z)
    (Zᴰ : Σ[ Xᴰ ∈ (⟨ Z .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (Z .snd) (λ z → ⟨ Xᴰ z ⟩))
    (χᴰ : Σ[ fᴰ ∈ (∀ b' → ⟨ StateAlgCBPV-push-obᴰ ϕ Bᴰ .fst b' ⟩
      → ⟨ Zᴰ .fst (ψ .fst b') ⟩) ]
      Homoᴰ fᴰ (ψ .snd) (StateAlgCBPV-push-obᴰ ϕ Bᴰ .snd) (Zᴰ .snd))
    → ∀ b → ⟨ Bᴰ .fst b ⟩ → ⟨ Zᴰ .fst (ψ .fst (ϕ .fst b)) ⟩
  canonical-fᴰ ψ Zᴰ χᴰ b bᴰ =
    χᴰ .fst (ϕ .fst b)
      (σ-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) b bᴰ)

  canonical-homᴰ : ∀ {Z : StateAlgebra ℓ}
    (ψ : StateAlgHom B' Z)
    (Zᴰ : Σ[ Xᴰ ∈ (⟨ Z .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (Z .snd) (λ z → ⟨ Xᴰ z ⟩))
    (χᴰ : Σ[ fᴰ ∈ (∀ b' → ⟨ StateAlgCBPV-push-obᴰ ϕ Bᴰ .fst b' ⟩
      → ⟨ Zᴰ .fst (ψ .fst b') ⟩) ]
      Homoᴰ fᴰ (ψ .snd) (StateAlgCBPV-push-obᴰ ϕ Bᴰ .snd) (Zᴰ .snd))
    → Homoᴰ (canonical-fᴰ ψ Zᴰ χᴰ) ((ϕ .snd) ⋆Homo (ψ .snd))
        (Bᴰ .snd) (Zᴰ .snd)
  canonical-homᴰ {Z = Z} ψ Zᴰ χᴰ =
    σ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) ⋆Homoᴰ χᴰ .snd

  push-path : ∀ b bᴰ {b'} (p : ϕ .fst b ≡ b')
    → Path
        (Σ ⟨ B' .fst ⟩
          (push-Xᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)))
        (ϕ .fst b , σ-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) b bᴰ)
        (b' , (b , p) , bᴰ)
  push-path b bᴰ p = ΣPathP
    ( p
    , ΣPathP
        ( ΣPathPProp (λ _ → B' .fst .snd _ _) refl
        , refl))

  recPush-η-fᴰ : ∀ {Z : StateAlgebra ℓ}
    (ψ : StateAlgHom B' Z)
    (Zᴰ : Σ[ Xᴰ ∈ (⟨ Z .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (Z .snd) (λ z → ⟨ Xᴰ z ⟩))
    (χᴰ : Σ[ fᴰ ∈ (∀ b' → ⟨ StateAlgCBPV-push-obᴰ ϕ Bᴰ .fst b' ⟩
      → ⟨ Zᴰ .fst (ψ .fst b') ⟩) ]
      Homoᴰ fᴰ (ψ .snd) (StateAlgCBPV-push-obᴰ ϕ Bᴰ .snd) (Zᴰ .snd))
    b' x
    → recPush-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)
        (Z .fst .snd) (ψ .snd) (Zᴰ .snd)
        (canonical-fᴰ ψ Zᴰ χᴰ) (canonical-homᴰ ψ Zᴰ χᴰ) b' x
      ≡ χᴰ .fst b' x
  recPush-η-fᴰ {Z = Z} ψ Zᴰ χᴰ b' ((b , p) , bᴰ) =
    hSetReasoning.rectifyOut (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩) $
      StateAlgᴰ.reind-filler⁻ (Zᴰ .snd) (cong (ψ .fst) p)
      ∙ cong {B = λ _ → Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩)}
          (λ q → ψ .fst (q .fst) , χᴰ .fst (q .fst) (q .snd))
          (push-path b bᴰ p)
  push-ue .UniversalElementⱽ'.vertexⱽ = StateAlgCBPV-push-obᴰ ϕ Bᴰ
  push-ue .UniversalElementⱽ'.elementⱽ .fst =
    σ-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)
  push-ue .UniversalElementⱽ'.elementⱽ .snd =
    subst
      (λ h → Homoᴰ (σ-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)) h
        (Bᴰ .snd) (StateAlgCBPV-push-obᴰ ϕ Bᴰ .snd))
      (isPropHomo (B' .fst .snd) (ϕ .snd)
        ((C.id {x = (𝓒 , B')} C.⋆ pushBase) .snd .snd))
      (σ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd))
  push-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ψ) .fst γᴰ =
    recPush-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)
      (Z .fst .snd) (ψ .snd .snd) (Zᴰ .snd) (γᴰ .fst) (γᴰ .snd) ,
    recPush (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)
      (Z .fst .snd) (ψ .snd .snd) (Zᴰ .snd) (γᴰ .fst) (γᴰ .snd)
  push-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ψ) .snd .fst γᴰ =
    Cᴰ.rectifyOut {a = (𝓒 , Z)} {b = (𝓒 , B)}
      {aᴰ = Zᴰ} {bᴰ = Bᴰ} {e' = refl} $
      Cᴰ.reind-filler⁻ {a = (𝓒 , Z)} {b = (𝓒 , B)}
        {aᴰ = Zᴰ} {bᴰ = Bᴰ} _
      ∙ Cᴰ.≡in {pth = ΣPathP (refl , StateAlgHom≡ _ _ refl)}
        (ΣPathP
          ( (funExt λ x → funExt λ xᴰ →
              hSetReasoning.Prectify (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩) $
                recPush-β (ϕ .snd) (Bᴰ .snd) (B' .fst .snd)
                  (Z .fst .snd) (ψ .snd .snd) (Zᴰ .snd)
                  (γᴰ .fst) (γᴰ .snd) x xᴰ)
          , isProp→PathP (λ i → isPropHomoᴰ (λ z → Zᴰ .fst z .snd)) _ _ ))
  push-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ψ) .snd .snd χᴰ =
    cong (push-ue .UniversalElementⱽ'.universalⱽ ((𝓒 , Z) , Zᴰ , ψ) .fst)
      (Cᴰ.rectifyOut {e' = refl} $
        Cᴰ.reind-filler⁻ _
        ∙ Cᴰ.≡in {pth = ΣPathP (refl , StateAlgHom≡ _ _ refl)}
          (ΣPathP
            ( funExt (λ x → funExt (λ xᴰ → refl))
            , isProp→PathP
                (λ i → isPropHomoᴰ (λ z → Zᴰ .fst z .snd)) _
                (subst
                  (λ h → Homoᴰ
                    (λ x xᴰ → χᴰ .fst (ϕ .fst x)
                      (σ-fᴰ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) x xᴰ))
                    h (Bᴰ .snd) (Zᴰ .snd))
                  (isPropHomo (Z .fst .snd)
                    ((ϕ .snd) ⋆Homo (ψ .snd .snd))
                    _)
                  (σ (ϕ .snd) (Bᴰ .snd) (B' .fst .snd) ⋆Homoᴰ χᴰ .snd)))))
    ∙ (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.≡in
      {pth = StateAlgHom≡ _ _ refl}
      (ΣPathP
        ( (funExt λ b' → funExt λ x →
            recPush-η-fᴰ (ψ .snd) Zᴰ χᴰ b' x)
        , isProp→PathP (λ i → isPropHomoᴰ (λ z → Zᴰ .fst z .snd)) _ _ )))

-- The F lift has FreeStateAlgⱽ as its intended vertex; its unit is the
-- heterogeneous composite described at the end of Instances.StateAlg.Base.
module _ {A : hSet ℓ} {B : StateAlgebra ℓ}
  (f : ⟨ A ⟩ → ⟨ B .fst ⟩)
  (Aᴰ : ⟨ A ⟩ → hSet ℓ)
  where

  StateAlgCBPV-F-obⱽ :
    Σ[ Bᴰ ∈ (⟨ B .fst ⟩ → hSet ℓ) ]
      StateAlgᴰ (B .snd) (λ y → ⟨ Bᴰ y ⟩)
  StateAlgCBPV-F-obⱽ .fst y .fst =
    FreeStateAlgⱽ-Xᴰ (λ x → ⟨ Aᴰ x ⟩) (B .snd) f (B .fst .snd) y
  StateAlgCBPV-F-obⱽ .fst y .snd =
    isSetΣ
      (isSetΣ
        (isSetΠ (λ _ → isSet× isSetBool (A .snd)))
        (λ _ → isProp→isSet (B .fst .snd _ _)))
      (λ s → isSetΠ (λ b → Aᴰ (s .fst b .snd) .snd))
  StateAlgCBPV-F-obⱽ .snd = FreeStateAlgⱽ (λ x → ⟨ Aᴰ x ⟩) (B .snd) f (B .fst .snd)

  StateAlgCBPV-retⱽ :
    ∀ x → ⟨ Aᴰ x ⟩ → ⟨ StateAlgCBPV-F-obⱽ .fst (f x) ⟩
  StateAlgCBPV-retⱽ x xᴰ .fst .fst = η ⟨ A ⟩ x
  StateAlgCBPV-retⱽ x xᴰ .fst .snd = recFSA-β ⟨ A ⟩ (B .snd) f x
  StateAlgCBPV-retⱽ x xᴰ .snd _ = xᴰ

StateAlgCBPV-Fⱽ : {ℓ : Level} → StateAlgCBPVHasFⱽ ℓ
StateAlgCBPV-Fⱽ {ℓ = ℓ} {A = A} {B = B} f Aᴰ =
  transportCartesianLift ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ) factor≡f composite
  where
  module C = Category (∫C (StateAlgCBPV { ℓ = ℓ } .fst ^opᴰ))

  recf : StateAlgHom (FreeStateAlgebra A) B
  recf = recFSA-f ⟨ A ⟩ (B .snd) f , recFSA ⟨ A ⟩ (B .snd) f

  η-lift = StateAlgCBPV-η-lift Aᴰ
  push-lift = StateAlgCBPV-push-lift recf (FreeStateAlgebraᴰ Aᴰ)

  composite = composeCartesianLifts ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰᴰ)
    η-lift push-lift

  factor≡f : ((_ , recf) C.⋆ (_ , η ⟨ A ⟩)) ≡ (_ , f)
  factor≡f = ΣPathP
    ( refl
    , funExt (recFSA-β ⟨ A ⟩ (B .snd) f))

StateAlgCBPV-F-vertex : ∀ {ℓ} {A : hSet ℓ} {B : StateAlgebra ℓ}
  (f : ⟨ A ⟩ → ⟨ B .fst ⟩) (Aᴰ : ⟨ A ⟩ → hSet ℓ)
  → StateAlgCBPV-Fⱽ {A = A} {B = B} f Aᴰ .fst
    ≡ StateAlgCBPV-F-obⱽ {A = A} {B = B} f Aᴰ
StateAlgCBPV-F-vertex f Aᴰ = refl

StateAlgCBPVⱽ :
  MultCBPVCatⱽ (StateAlgCBPV { ℓ = ℓ } .fst)
    (ℓ-suc ℓ) ℓ
StateAlgCBPVⱽ .fst = StateAlgCBPVᴰ _ _
StateAlgCBPVⱽ .snd .fst = StateAlgCBPV-Uⱽ
StateAlgCBPVⱽ .snd .snd = StateAlgCBPV-Fⱽ
