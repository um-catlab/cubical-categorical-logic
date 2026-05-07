module Cubical.Categories.Instances.Strictify where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom

private
  variable ℓ ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C

  YonedaStrictify : Category ℓC (ℓ-max ℓC ℓC')
  YonedaStrictify .ob = C.ob
  YonedaStrictify .Hom[_,_] c d = PshHomStrict (C [-, c ]) (C [-, d ])
  YonedaStrictify .id = idPshHomStrict
  YonedaStrictify ._⋆_ = _⋆PshHomStrict_
  YonedaStrictify .⋆IdL = λ _ → refl
  YonedaStrictify .⋆IdR = λ _ → refl
  YonedaStrictify .⋆Assoc = λ _ _ _ → refl
  YonedaStrictify .isSetHom = isSetPshHomStrict _ _

  -- The path fields below (F-id, F-seq, to-from .N-hom) use copatterns
  -- rather than makePshHomStrictPath so that .N-ob projections reduce.
  -- The displayed versions in Displayed/Instances/Strictify rely on this
  -- to apply makePshHomStrictᴰPathP without inlining their own copatterns.
  toYonedaStrictify : Functor C YonedaStrictify
  toYonedaStrictify .F-ob = λ z → z
  toYonedaStrictify .F-hom f .PshHomStrict.N-ob = λ c z → z C.⋆ f
  toYonedaStrictify .F-hom f .PshHomStrict.N-hom _ _ _ _ _ e =
    (sym $ C.⋆Assoc _ _ _) ∙ C.⟨ e ⟩⋆⟨ refl ⟩
  toYonedaStrictify .F-id {x = x} i .PshHomStrict.N-ob Γ p = C.⋆IdR p i
  toYonedaStrictify .F-id {x = x} i .PshHomStrict.N-hom =
    isProp→PathP (λ j → isPropN-hom (C [-, x ]) (C [-, x ]) (λ Γ p → C.⋆IdR p j))
      (toYonedaStrictify .F-hom C.id .PshHomStrict.N-hom)
      (idPshHomStrict {P = C [-, x ]} .PshHomStrict.N-hom) i
  toYonedaStrictify .F-seq {x = x} {z = z} f g i .PshHomStrict.N-ob Γ p =
    sym (C.⋆Assoc p f g) i
  toYonedaStrictify .F-seq {x = x} {z = z} f g i .PshHomStrict.N-hom =
    isProp→PathP
      (λ j → isPropN-hom (C [-, x ]) (C [-, z ]) (λ Γ p → sym (C.⋆Assoc p f g) j))
      (toYonedaStrictify .F-hom (f C.⋆ g) .PshHomStrict.N-hom)
      ((toYonedaStrictify .F-hom f ⋆PshHomStrict toYonedaStrictify .F-hom g)
        .PshHomStrict.N-hom) i

  fromYonedaStrictify : Functor YonedaStrictify C
  fromYonedaStrictify .F-ob = λ z → z
  fromYonedaStrictify .F-hom = λ z → z .PshHomStrict.N-ob _ C.id
  fromYonedaStrictify .F-id = refl
  fromYonedaStrictify .F-seq f g = sym $ g .PshHomStrict.N-hom _ _ _ C.id _
    (C.⋆IdR (fromYonedaStrictify .F-hom f))

  to-from-YonedaStrictify : NatIso (toYonedaStrictify ∘F fromYonedaStrictify) Id
  to-from-YonedaStrictify .NatIso.trans .NatTrans.N-ob = λ _ → idPshHomStrict
  to-from-YonedaStrictify .NatIso.trans .NatTrans.N-hom {x = x}{y = y} f i .PshHomStrict.N-ob Γ p =
    f .PshHomStrict.N-hom _ _ _ _ _ (C.⋆IdR p) i
  to-from-YonedaStrictify .NatIso.trans .NatTrans.N-hom {x = x}{y = y} f i .PshHomStrict.N-hom =
    isProp→PathP
      (λ j → isPropN-hom (C [-, x ]) (C [-, y ])
        (λ Γ p → f .PshHomStrict.N-hom _ _ _ _ _ (C.⋆IdR p) j))
      ((toYonedaStrictify .F-hom (fromYonedaStrictify .F-hom f) ⋆PshHomStrict idPshHomStrict)
        .PshHomStrict.N-hom)
      ((idPshHomStrict ⋆PshHomStrict f) .PshHomStrict.N-hom) i
  to-from-YonedaStrictify .NatIso.nIso c .isIso.inv = idPshHomStrict
  to-from-YonedaStrictify .NatIso.nIso c .isIso.sec = refl
  to-from-YonedaStrictify .NatIso.nIso c .isIso.ret = refl

  from-to-YonedaStrictify : NatIso (fromYonedaStrictify ∘F toYonedaStrictify) Id
  from-to-YonedaStrictify .NatIso.trans = natTrans (λ x → C.id) (λ _ → C.⋆IdR _)
  from-to-YonedaStrictify .NatIso.nIso = λ _ → isiso C.id (C.⋆IdL _) (C.⋆IdL _)
