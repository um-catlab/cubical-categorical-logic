{-

  Any profunctor C → D can be extend to a functor Psh C → Psh D that agrees with the original on representables.
  This is part of the fact that Psh C is a free cocompletion of C

  This is also the extension part of a 2-monad structure on Psh

-}
module Cubical.Categories.Profunctor.Constructions.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure


open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Category
open Bifunctor
open Functor
open NatTrans
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  module ext-⊗ {ℓP}{ℓQ} (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf C ℓQ){d} =
    Tensor (CurryBifunctor P ⟅ d ⟆) Q

  -- TODO: make this a bifunctor
  ext : D o-[ ℓP ]-* C
    → Functor (PresheafCategory C ℓ)
              (PresheafCategory D (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓ))
  ext P = CurryBifunctor $ Sym $ ⊗-Bif ∘Fl CurryBifunctor P
  private
    test-ext : ∀ (P : D o-[ ℓP ]-* C) (Q : Presheaf C ℓQ) d
      → ⟨ (ext P ⟅ Q ⟆) .F-ob d ⟩ ≡ ((CurryBifunctor P ⟅ d ⟆) ⊗ Q)
    test-ext P Q d = refl

  ext-HomR :
    {Q : Presheaf C ℓQ}
    {R : Presheaf C ℓR}
    (P : D o-[ ℓP ]-* C)
    (α : PshHom Q R)
    → PshHom (ext P ⟅ Q ⟆) (ext P ⟅ R ⟆)
  ext-HomR {Q = Q} {R = R} P α .N-ob d = idPshHom ⊗Hom α
  ext-HomR {Q = Q} {R = R} P α .N-hom d d' f =
    P⊗Q.ind (λ _ → P⊗R.isSet⊗ _ _) (λ _ _ → refl)
    where
      module P⊗Q = ext-⊗ P Q
      module P⊗R = ext-⊗ P R

  ext-HomL : ∀
    {P : D o-[ ℓP ]-* C}
    {Q : D o-[ ℓQ ]-* C}
    (α : RelatorHom P Q)
    (R : Presheaf C ℓR)
    → PshHom (ext P ⟅ R ⟆) (ext Q ⟅ R ⟆)
  ext-HomL {P = P}{Q = Q} α R .N-ob d =
    (appL-Hom α d) ⊗Hom idPshHom
  ext-HomL {P = P}{Q = Q} α R .N-hom d d' f =
      P⊗R.ind (λ _ → Q⊗R.isSet⊗ _ _) (λ p r → cong (Q⊗R._,⊗ _)
        (appR-Hom α _ .N-hom _ _ _ _))
    where
      module P⊗R = ext-⊗ P R using (ind)
      module Q⊗R = ext-⊗ Q R using (isSet⊗; _,⊗_)

  ext-IsoL : ∀
    {P : D o-[ ℓP ]-* C}
    {Q : D o-[ ℓQ ]-* C}
    (α : RelatorIso P Q)
    (R : Presheaf C ℓR)
    → PshIso (ext P ⟅ R ⟆) (ext Q ⟅ R ⟆)
  ext-IsoL {P = P}{Q = Q} α R =
    Isos→PshIso (λ d → appL-Iso α d ⊗Iso idPshIso) (ext-HomL (α .trans) R .N-hom)

  -- TODO: make this natural in Q
  CoContinuous : {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓP ℓ)))
    → Typeω
  CoContinuous P = ∀ {ℓ} (Q : Presheaf C ℓ)
    → PshIso (P ⟅ Q ⟆) (ext (CurriedToBifunctorL (P ∘F CurryBifunctorL (HomBif C))) ⟅ Q ⟆)

module _ {C : Category ℓC ℓC'} where
  private
    test-ext' : ∀ (Q : Presheaf C ℓQ) →
      ext (HomBif C) ⟅ Q ⟆ ≡ ◇ Q
    test-ext' Q = refl
