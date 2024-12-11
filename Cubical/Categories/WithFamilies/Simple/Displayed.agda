{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Presheaf.CartesianLift as Presheafᴰ

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
open UniversalElementᴰ
open isIsoOver
open Iso

SCwFᴰ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFᴰ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ Cᴰ (Tm A) ℓTᴰ') ]
  Terminalᴰ Cᴰ (terminalToUniversalElement term) ×
  (∀ {Γ A} (Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Tyᴰ A) →
    UniversalElementᴰ Cᴰ
      (PshProdᴰ (Cᴰ [-][-, Γᴰ ]) (Tmᴰ Aᴰ))
      (comprehension Γ A))

SCwFⱽ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
SCwFⱽ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
  Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
  let module Cᴰ = Categoryᴰ Cᴰ in
  Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
  Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ Cᴰ (Tm A) ℓTᴰ') ]
  hasAllTerminalⱽ Cᴰ ×
  isFibration Cᴰ ×
  hasAllBinProductⱽ Cᴰ ×
  (∀ {Γ A}(M : ⟨ Tm A ⟅ Γ ⟆ ⟩)(Aᴰ : Tyᴰ A)
    → Presheafᴰ.CartesianLift M (Tmᴰ Aᴰ))

SCwFⱽ→SCwFᴰ : ∀ (C : SCwF ℓC ℓC' ℓT ℓT')
  → SCwFⱽ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
  → SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ'
SCwFⱽ→SCwFᴰ
  (C , Ty , Tm , term , comprehension)
  (Cᴰ , Tyᴰ , Tmᴰ , termⱽ , Cᴰ-lifts , bpⱽ , Tmᴰ-lifts) =
  Cᴰ , Tyᴰ , Tmᴰ
  , Terminalⱽ→Terminalᴰ Cᴰ (termⱽ _)
  , λ {Γ}{A} Γᴰ Aᴰ →
    BinProductⱽ→UnivPshProdᴰ
      (comprehension Γ A)
      (Presheafᴰ.fibLift→PshᴰLift (Cᴰ-lifts Γᴰ (comprehension Γ A .element .fst)))      
      (Tmᴰ-lifts (comprehension Γ A .element .snd) Aᴰ)
      (bpⱽ ( Cᴰ-lifts Γᴰ (comprehension Γ A .element .fst) .CartesianLift.f*yᴰ
           , Tmᴰ-lifts (comprehension Γ A .element .snd) Aᴰ .Presheafᴰ.CartesianLift.p*Pᴰ))

∫SCwF : ∀ (C : SCwF ℓC ℓC' ℓT ℓT') (Cᴰ : SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
  → SCwF (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ') (ℓ-max ℓT ℓTᴰ) (ℓ-max ℓT' ℓTᴰ')
∫SCwF (C , Ty , Tm , term , comprehension)
      (Cᴰ , Tyᴰ , Tmᴰ , termᴰ , comprehensionᴰ) =
  ∫C Cᴰ , Σ Ty Tyᴰ , (λ (A , Aᴰ) → ∫P (Tmᴰ Aᴰ))
  , ∫term Cᴰ term termᴰ
  , λ (Γ , Γᴰ) (A , Aᴰ) →
    -- TODO: find a good place for this construction
    let Γ×A = comprehension Γ A
        Γᴰ×ᴰAᴰ = comprehensionᴰ Γᴰ Aᴰ
    in
    record
    { vertex = (Γ×A .vertex) , Γᴰ×ᴰAᴰ .vertexᴰ
    ; element =
      (Γ×A .element .fst , Γᴰ×ᴰAᴰ .elementᴰ .fst)
     , (Γ×A .element .snd , Γᴰ×ᴰAᴰ .elementᴰ .snd)
    ; universal = λ (Δ , Δᴰ) →
      let universal' = equivToIso (_ , (Γ×A .universal Δ)) in
      isIsoToIsEquiv
      ( (λ ((γ , γᴰ) , (M , Mᴰ)) → Γ×A .universal Δ .equiv-proof (γ , M) .fst .fst  , Γᴰ×ᴰAᴰ .universalᴰ .inv (γ , M) (γᴰ , Mᴰ))
      , (λ ((γ , γᴰ) , (M , Mᴰ)) → ΣPathP
        ( ΣPathP ((cong fst $ universal' .rightInv (γ , M)) , (congP (λ _ → fst) $ Γᴰ×ᴰAᴰ .universalᴰ .rightInv  (γ , M) (γᴰ , Mᴰ))) 
        , ΣPathP (((cong snd $ universal' .rightInv (γ , M))) , ((congP (λ _ → snd) $ Γᴰ×ᴰAᴰ .universalᴰ .rightInv  (γ , M) (γᴰ , Mᴰ))))))
      , λ (γ,M , γᴰ,Mᴰ) → ΣPathP (universal' .leftInv γ,M , Γᴰ×ᴰAᴰ .universalᴰ .leftInv γ,M γᴰ,Mᴰ))
    }
