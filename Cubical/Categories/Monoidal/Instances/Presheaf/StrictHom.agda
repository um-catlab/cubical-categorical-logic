module Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Closed
open import Cubical.Categories.Presheaf.Representable using (UniversalElement)
open import Cubical.Functions.FunExtEquiv using (funExt₂)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.StrictHom.Bifunctor
open import Cubical.Categories.Presheaf.Constructions hiding (π₁;π₂)
open import Cubical.Categories.Presheaf.Morphism.Alt

open Bifunctor
open BinProduct
open Category
open Functor
open MonoidalCategory renaming (C to Cat)
open MonoidalStr
open NatIso
open NatTrans
open TensorStr

private
  variable
    ℓ ℓ' : Level

module PshMon (C : Category ℓ ℓ')(ℓS : Level) where
  ℓm = ℓ-max ℓ' (ℓ-max ℓ ℓS)
  𝓟 = PRESHEAF C (ℓm)

  ⨂' : Bifunctor 𝓟 𝓟 𝓟
  ⨂' = PshProdStrict {ℓ}{ℓ'}{C}{ℓm}{ℓm}

  ⨂ : Functor (𝓟 ×C 𝓟) 𝓟
  ⨂ = PshProd'Strict

  𝟙 : ob 𝓟
  𝟙 = LiftPsh UnitPsh ℓm

  𝓟Ten :  TensorStr 𝓟
  𝓟Ten . ─⊗─ = ⨂
  𝓟Ten .unit = 𝟙

  _^_ : ob 𝓟 → ob 𝓟 → ob 𝓟
  _^_ B A = A ⇒PshLargeStrict B

  eval : {P Q : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh P , Q ]
  eval {P}{Q} = appPshHomStrict P Q

  π₁p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , P ]
  π₁p {P}{Q} = (π₁ P Q)

  π₂p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ]
  π₂p {P}{Q} = (π₂ P Q)

  idl : ⨂ ∘F rinj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
  idl .trans = natTrans (λ P → π₂p) λ _ → refl
  idl .nIso P =
    isiso
      (pshhom (λ x Px → tt* , Px) λ _ _ _ _ _ p≡ → cong₂ _,_ refl p≡)
      (makePshHomStrictPath refl)
      (makePshHomStrictPath refl)

  idr : ⨂ ∘F linj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
  idr .trans = natTrans (λ P → π₁p) λ _ → refl
  idr .nIso P =
    isiso
      (pshhom (λ x Px → Px , tt*) λ _ _ _ _ _ p≡ → cong₂ _,_ p≡ refl)
      (makePshHomStrictPath refl)
      (makePshHomStrictPath refl)

  assoc : {P Q R : ob 𝓟} → 𝓟 [ P ×Psh (Q ×Psh R) , (P ×Psh Q ) ×Psh R ]
  assoc .PshHomStrict.N-ob c = Iso.inv Σ-assoc-Iso
  assoc .PshHomStrict.N-hom _ _ _ _ _ = cong (Iso.inv Σ-assoc-Iso)

  𝓟Mon' : MonoidalStr 𝓟
  𝓟Mon' .tenstr = 𝓟Ten
  𝓟Mon' .α =
    record {
      trans =
        natTrans
          (λ {(P , (Q , R)) → assoc})
          λ _ → refl ;
      nIso = λ{ (P , Q , R) →
        isiso
          (pshhom (λ _ → Iso.fun Σ-assoc-Iso) λ _ _ _ _ _ e → cong (Iso.fun Σ-assoc-Iso) e)
          (makePshHomStrictPath refl)
          (makePshHomStrictPath refl) }}
  𝓟Mon' .η = idl
  𝓟Mon' .ρ = idr
  𝓟Mon' .pentagon P Q R S = refl
  𝓟Mon' .triangle P Q = refl

  𝓟Mon : MonoidalCategory (ℓ-suc ℓm) (ℓm)
  𝓟Mon .Cat = 𝓟
  𝓟Mon .monstr = 𝓟Mon'

  private
    swap : {P Q : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ×Psh P ]
    swap = ×PshIntroStrict π₂p π₁p

    module _ {P Q R : ob 𝓟} where
      private
        module R = PresheafNotation R

      λ-η : (α : PshHomStrict R (Q ^ P)) (γ : PshHomStrict (R ×Psh P) Q)
        → (∀ c r → γ .PshHomStrict.N-ob c r ≡ α .PshHomStrict.N-ob (c) (r .fst) .PshHomStrict.N-ob c (C .id , r .snd))
        → λPshHomStrict P Q γ ≡ α
      λ-η α γ p = makePshHomStrictPath (funExt₂ λ c r → makePshHomStrictPath
        (funExt₂ λ d (f , q) →
          p d (f R.⋆ r , q)
          ∙ sym (cong (λ x → α .PshHomStrict.N-ob c r .PshHomStrict.N-ob d (x , q)) (sym (⋆IdL C f))
          ∙ funExt⁻ (funExt⁻ (cong PshHomStrict.N-ob (α .PshHomStrict.N-hom d c f r (f R.⋆ r) refl)) d) (C .id , q))))

  𝓟LeftClosed : LeftClosed 𝓟Mon
  𝓟LeftClosed P Q .UniversalElement.vertex = Q ^ P
  𝓟LeftClosed P Q .UniversalElement.element = swap ⋆PshHomStrict eval
  𝓟LeftClosed P Q .UniversalElement.universal R = isoToIsEquiv transpose
    where
    module R = PresheafNotation R
    transpose : Iso (PshHomStrict R (Q ^ P)) (PshHomStrict (P ×Psh R) Q)
    transpose .Iso.fun α = ⨂ .F-hom (idPshHomStrict , α) ⋆PshHomStrict (swap ⋆PshHomStrict eval)
    transpose .Iso.inv γ = λPshHomStrict P Q (swap ⋆PshHomStrict γ)
    transpose .Iso.sec γ = makePshHomStrictPath
      (funExt₂ λ c (p , r) → cong (λ x → γ .PshHomStrict.N-ob c (p , x)) (R.⋆IdL r))
    transpose .Iso.ret α = λ-η α (swap ⋆PshHomStrict transpose .Iso.fun α) (λ c r → refl)

  𝓟RightClosed : RightClosed 𝓟Mon
  𝓟RightClosed P Q .UniversalElement.vertex = Q ^ P
  𝓟RightClosed P Q .UniversalElement.element = eval
  𝓟RightClosed P Q .UniversalElement.universal R = isoToIsEquiv transpose
    where
    module R = PresheafNotation R
    transpose : Iso (PshHomStrict R (Q ^ P)) (PshHomStrict (R ×Psh P) Q)
    transpose .Iso.fun α = ⨂ .F-hom (α , idPshHomStrict) ⋆PshHomStrict eval
    transpose .Iso.inv = λPshHomStrict P Q
    transpose .Iso.sec γ = makePshHomStrictPath
      (funExt₂ λ c (r , p) → cong (λ x → γ .PshHomStrict.N-ob c (x , p)) (R.⋆IdL r))
    transpose .Iso.ret α = λ-η α (transpose .Iso.fun α) (λ c r → refl)
