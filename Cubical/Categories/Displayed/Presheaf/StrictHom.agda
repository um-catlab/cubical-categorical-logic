{-
  Strict displayed presheaf homomorphisms.

  Defines PshHomStrictᴰ α Pᴰ Qᴰ as a displayed analogue of PshHomStrict P Q
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.StrictHom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓPᴰ ℓQᴰ ℓRᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Functor
open Functorᴰ
open Categoryᴰ
open PshHomStrict

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  PshHomStrictᴰN-obTy : Type _
  PshHomStrictᴰN-obTy =
    ∀ (Γ : C.ob)(Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ Γ ])
    → Pᴰ.p[ p ][ Γᴰ ] → Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ]

  PshHomStrictᴰN-homTy : PshHomStrictᴰN-obTy → Type _
  PshHomStrictᴰN-homTy N-obᴰ =
    ∀ (Δ Γ : C.ob)(Δᴰ : Cᴰ.ob[ Δ ])(Γᴰ : Cᴰ.ob[ Γ ])
    (f : C [ Δ , Γ ])(p' : P.p[ Γ ])(p : P.p[ Δ ])
    (fᴰ : Cᴰ [ f ][ Δᴰ , Γᴰ ])
    (pᴰ' : Pᴰ.p[ p' ][ Γᴰ ])(pᴰ : Pᴰ.p[ p ][ Δᴰ ])
    (e : (f P.⋆ p') ≡ p)
    (eᴰ : PathP (λ i → Pᴰ.p[ e i ][ Δᴰ ]) (fᴰ Pᴰ.⋆ᴰ pᴰ') pᴰ)
    → PathP (λ i → Qᴰ.p[ α .N-hom Δ Γ f p' p e i ][ Δᴰ ])
        (fᴰ Qᴰ.⋆ᴰ N-obᴰ Γ Γᴰ p' pᴰ') (N-obᴰ Δ Δᴰ p pᴰ)

  record PshHomStrictᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
                  (ℓ-max (ℓ-max ℓP ℓPᴰ) ℓQᴰ))
    where
    constructor pshhomᴰ
    field
      N-obᴰ : PshHomStrictᴰN-obTy
      N-homᴰ : PshHomStrictᴰN-homTy N-obᴰ

  PshHomStrictᴰΣ : Type _
  PshHomStrictᴰΣ = Σ PshHomStrictᴰN-obTy PshHomStrictᴰN-homTy

  isPropN-homᴰ : (N-obᴰ : PshHomStrictᴰN-obTy)
    → isProp (PshHomStrictᴰN-homTy N-obᴰ)
  isPropN-homᴰ N-obᴰ =
    isPropΠ λ Δ → isPropΠ λ Γ → isPropΠ λ Δᴰ → isPropΠ λ Γᴰ →
    isPropΠ λ f → isPropΠ λ p' → isPropΠ λ p →
    isPropΠ λ fᴰ → isPropΠ λ pᴰ' → isPropΠ λ pᴰ →
    isPropΠ λ e → isPropΠ λ eᴰ →
      isOfHLevelPathP' 1 Qᴰ.isSetPshᴰ _ _

  isSetPshHomStrictᴰΣ : isSet PshHomStrictᴰΣ
  isSetPshHomStrictᴰΣ =
    isSetΣ (isSetΠ λ Γ → isSetΠ λ Γᴰ → isSetΠ λ p → isSet→ Qᴰ.isSetPshᴰ)
           λ N-obᴰ → isProp→isSet (isPropN-homᴰ N-obᴰ)

  PshHomStrictᴰΣIso : Iso PshHomStrictᴰ PshHomStrictᴰΣ
  PshHomStrictᴰΣIso .Iso.fun αᴰ = αᴰ .PshHomStrictᴰ.N-obᴰ , αᴰ .PshHomStrictᴰ.N-homᴰ
  PshHomStrictᴰΣIso .Iso.inv (a , b) .PshHomStrictᴰ.N-obᴰ = a
  PshHomStrictᴰΣIso .Iso.inv (a , b) .PshHomStrictᴰ.N-homᴰ = b
  PshHomStrictᴰΣIso .Iso.sec _ = refl
  PshHomStrictᴰΣIso .Iso.ret _ = refl

  isSetPshHomStrictᴰ : isSet PshHomStrictᴰ
  isSetPshHomStrictᴰ =
    isOfHLevelRetractFromIso 2 PshHomStrictᴰΣIso isSetPshHomStrictᴰΣ

open PshHomStrictᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHomStrict P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  makePshHomStrictᴰPath : ∀ {αᴰ βᴰ : PshHomStrictᴰ α Pᴰ Qᴰ}
    → αᴰ .N-obᴰ ≡ βᴰ .N-obᴰ
    → αᴰ ≡ βᴰ
  makePshHomStrictᴰPath {αᴰ}{βᴰ} N-obᴰ≡ i .N-obᴰ = N-obᴰ≡ i
  makePshHomStrictᴰPath {αᴰ}{βᴰ} N-obᴰ≡ i .N-homᴰ =
    isProp→PathP (λ j → isPropN-homᴰ α Pᴰ Qᴰ (N-obᴰ≡ j))
      (αᴰ .N-homᴰ) (βᴰ .N-homᴰ) i

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  makePshHomStrictᴰPathP : ∀ {α β : PshHomStrict P Q} {α≡β : α ≡ β}
    {αᴰ : PshHomStrictᴰ α Pᴰ Qᴰ}{βᴰ : PshHomStrictᴰ β Pᴰ Qᴰ}
    → PathP (λ i → PshHomStrictᴰN-obTy (α≡β i) Pᴰ Qᴰ) (αᴰ .N-obᴰ) (βᴰ .N-obᴰ)
    → PathP (λ i → PshHomStrictᴰ (α≡β i) Pᴰ Qᴰ) αᴰ βᴰ
  makePshHomStrictᴰPathP {αᴰ = αᴰ}{βᴰ = βᴰ} N-obᴰ≡ i .N-obᴰ = N-obᴰ≡ i
  makePshHomStrictᴰPathP {α≡β = α≡β}{αᴰ = αᴰ}{βᴰ = βᴰ} N-obᴰ≡ i .N-homᴰ =
    isProp→PathP (λ j → isPropN-homᴰ (α≡β j) Pᴰ Qᴰ (N-obᴰ≡ j))
      (αᴰ .N-homᴰ) (βᴰ .N-homᴰ) i

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  idPshHomStrictᴰ : PshHomStrictᴰ idPshHomStrict Pᴰ Pᴰ
  idPshHomStrictᴰ .N-obᴰ Γ Γᴰ p pᴰ = pᴰ
  idPshHomStrictᴰ .N-homᴰ Δ Γ Δᴰ Γᴰ f p' p fᴰ pᴰ' pᴰ e eᴰ = eᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}{β : PshHomStrict Q R}
  where
  _⋆PshHomStrictᴰ_ : PshHomStrictᴰ α Pᴰ Qᴰ → PshHomStrictᴰ β Qᴰ Rᴰ
    → PshHomStrictᴰ (α ⋆PshHomStrict β) Pᴰ Rᴰ
  (αᴰ ⋆PshHomStrictᴰ βᴰ) .N-obᴰ Γ Γᴰ p pᴰ =
    βᴰ .N-obᴰ Γ Γᴰ _ (αᴰ .N-obᴰ Γ Γᴰ p pᴰ)
  (αᴰ ⋆PshHomStrictᴰ βᴰ) .N-homᴰ Δ Γ Δᴰ Γᴰ f p' p fᴰ pᴰ' pᴰ e eᴰ =
    βᴰ .N-homᴰ Δ Γ Δᴰ Γᴰ f _ _ fᴰ
      (αᴰ .N-obᴰ Γ Γᴰ p' pᴰ')
      (αᴰ .N-obᴰ Δ Δᴰ p pᴰ)
      (α .N-hom Δ Γ f p' p e)
      (αᴰ .N-homᴰ Δ Γ Δᴰ Γᴰ f p' p fᴰ pᴰ' pᴰ e eᴰ)
  infixr 9 _⋆PshHomStrictᴰ_

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓP : Level)(ℓPᴰ : Level)
  where
  PRESHEAFᴰStrict : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰStrict .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰStrict .Hom[_][_,_] α Pᴰ Qᴰ = PshHomStrictᴰ α Pᴰ Qᴰ
  PRESHEAFᴰStrict .idᴰ = idPshHomStrictᴰ
  PRESHEAFᴰStrict ._⋆ᴰ_ = _⋆PshHomStrictᴰ_
  PRESHEAFᴰStrict .⋆IdLᴰ _ = refl
  PRESHEAFᴰStrict .⋆IdRᴰ _ = refl
  PRESHEAFᴰStrict .⋆Assocᴰ _ _ _ = refl
  PRESHEAFᴰStrict .isSetHomᴰ = isSetPshHomStrictᴰ _ _ _

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Cᴰf = Fibers Cᴰ

  YOStrictᴰ : Functorᴰ (YOStrict {C = C}) Cᴰ (PRESHEAFᴰStrict Cᴰ ℓC' ℓCᴰ')
  YOStrictᴰ .F-obᴰ xᴰ = Cᴰ [-][-, xᴰ ]
  YOStrictᴰ .F-homᴰ hᴰ .N-obᴰ Γ Γᴰ g gᴰ = gᴰ Cᴰ.⋆ᴰ hᴰ
  YOStrictᴰ .F-homᴰ hᴰ .N-homᴰ Δ Γ Δᴰ Γᴰ f p' p fᴰ p'ᴰ pᴰ e eᴰ =
    Cᴰf.rectifyOut $
      sym (Cᴰf.≡in (Cᴰf.⋆Assocᴰ fᴰ p'ᴰ hᴰ))
      ∙ Cᴰf.⟨ Cᴰf.≡in eᴰ ⟩⋆⟨ refl ⟩
  YOStrictᴰ .F-idᴰ =
    makePshHomStrictᴰPathP (funExt λ _ → funExt λ _ → funExt λ _ → funExt λ _ →
      Cᴰf.rectifyOut (Cᴰf.≡in $ Cᴰf.⋆IdRᴰ _))
  YOStrictᴰ .F-seqᴰ h₁ᴰ h₂ᴰ =
    makePshHomStrictᴰPathP (funExt λ _ → funExt λ _ → funExt λ _ → funExt λ _ →
      Cᴰf.rectifyOut (sym $ Cᴰf.≡in $ Cᴰf.⋆Assocᴰ _ _ _))

  isFullyFaithfulYOStrictᴰ : FullyFaithfulᴰ YOStrictᴰ
  isFullyFaithfulYOStrictᴰ {x = x} {y = y} f xᴰ yᴰ = bwd , sec , ret
    where
      bwd : PshHomStrictᴰ (YOStrict .F-hom f) (Cᴰ [-][-, xᴰ ]) (Cᴰ [-][-, yᴰ ])
            → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
      bwd αᴰ = Cᴰf.reind (C.⋆IdL f) (αᴰ .N-obᴰ x xᴰ C.id Cᴰ.idᴰ)

      sec : ∀ αᴰ → YOStrictᴰ .F-homᴰ (bwd αᴰ) ≡ αᴰ
      sec αᴰ = makePshHomStrictᴰPath
        (funExt λ Γ → funExt λ Γᴰ → funExt λ g → funExt λ gᴰ →
          Cᴰf.rectifyOut $
            Cᴰf.⟨ refl ⟩⋆⟨ Cᴰf.reind-filler⁻ (C.⋆IdL f) ⟩
            ∙ Cᴰf.≡in
                (αᴰ .N-homᴰ Γ x Γᴰ xᴰ g C.id g gᴰ Cᴰ.idᴰ gᴰ
                  (C.⋆IdR g) (Cᴰ.⋆IdRᴰ gᴰ)))

      ret : ∀ hᴰ → bwd (YOStrictᴰ .F-homᴰ hᴰ) ≡ hᴰ
      ret hᴰ = Cᴰf.rectifyOut $
        Cᴰf.reind-filler⁻ (C.⋆IdL f) ∙ Cᴰf.≡in (Cᴰ.⋆IdLᴰ hᴰ)
