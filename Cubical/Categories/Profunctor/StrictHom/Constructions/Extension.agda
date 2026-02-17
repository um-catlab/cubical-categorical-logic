{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.StrictHom.Constructions.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_ ; PshIso)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Profunctor.StrictHom.Base
open import Cubical.Categories.Yoneda.More

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Category
open Bifunctor
open Functor
open NatTrans
open PshHomStrict
open PshIsoStrict

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{ℓP : Level} where
  -- It frustrating that PRESHEAF isn't literally a functor category
  -- As a middle ground, it would be nice if we had COPRESHEAF as a primitive, and
  -- then derived PRESHEAF as copresheaves on the opposite category
  -- This should avoid some OpOp nonsense
  CurryBifunctor' : Bifunctor C (D ^op) (SET ℓP) → Functor C (PRESHEAF D ℓP)
  CurryBifunctor' F .F-ob c = appL F c
  CurryBifunctor' F .F-hom f .N-ob d = Bifunctor.Bif-homL F f d
  CurryBifunctor' F .F-hom f .N-hom c c' g p p' e =
    sym (funExt⁻ (Bif-RL-commute F f g) p) ∙ cong (Bifunctor.Bif-homL F f c) e
  CurryBifunctor' F .F-id = makePshHomStrictPath (funExt λ _ → F .Bifunctor.Bif-L-id)
  CurryBifunctor' F .F-seq f g = makePshHomStrictPath (funExt λ _ → F .Bifunctor.Bif-L-seq f g)

  CurryBifunctorL' : Bifunctor (C ^op) D (SET ℓP) → Functor D (PRESHEAF C ℓP)
  CurryBifunctorL' F .F-ob = appR F
  CurryBifunctorL' F .F-hom f .N-ob c = appL F c ⟪ f ⟫
  CurryBifunctorL' F .F-hom f .N-hom c c' g p p' e =
    funExt⁻ (Bif-RL-commute F g f) _
    ∙ cong (Bif-homR F c f) e
  CurryBifunctorL' F .F-id = makePshHomStrictPath (funExt λ _ → F .Bif-R-id)
  CurryBifunctorL' F .F-seq _ _ = makePshHomStrictPath (funExt λ _ → F .Bif-R-seq _ _)

  CurriedToBifunctorLStrict : Functor C (PRESHEAF D ℓP) → Bifunctor (D ^op) C (SET ℓP)
  CurriedToBifunctorLStrict F = mkBifunctorSep G
    where
    G : BifunctorSep _ _ _
    G .BifunctorSep.Bif-ob d c = F ⟅ c ⟆ ⟅ d ⟆
    G .BifunctorSep.Bif-homL g c = F ⟅ c ⟆ ⟪ g ⟫
    G .BifunctorSep.Bif-homR d f = F .F-hom f .N-ob d
    G .BifunctorSep.Bif-L-id = F .F-ob _ .F-id
    G .BifunctorSep.Bif-L-seq g g' = F .F-ob _ .F-seq g g'
    G .BifunctorSep.Bif-R-id = cong (λ α → α .N-ob _) (F .F-id)
    G .BifunctorSep.Bif-R-seq f f' = cong (λ α → α .N-ob _) (F .F-seq f f')
    G .BifunctorSep.SepBif-RL-commute g f =
      funExt λ p → ((F ⟪ f ⟫) .N-hom _ _ g p (F-hom (F ⟅ _ ⟆) g p) refl)

module _ {C : Category ℓC ℓC'} where
  module _ {P : Functor C (SET ℓP)} {Q : Functor (C ^op) (SET ℓQ)} {ℓP' ℓQ'}
           {P' : Functor C (SET ℓP')} {Q' : Functor (C ^op) (SET ℓQ')}
           (α : PshHomStrict (P ∘F fromOpOp) (P' ∘F fromOpOp)) (β : PshHomStrict Q Q')
           where
    private
      module P⊗Q = Tensor P Q
      module P'⊗Q' = Tensor P' Q'
    _⊗PshHomStrict_ : P ⊗ Q → P' ⊗ Q'
    _⊗PshHomStrict_ = P⊗Q.rec P'⊗Q'.isSet⊗ (λ {x} p q → α .N-ob x p P'⊗Q'.,⊗ β .N-ob x q)
      λ p f r → cong (_ P'⊗Q'.,⊗_) (sym (β .N-hom _ _ f r (F-hom Q f $ r) refl))
                ∙ P'⊗Q'.swap _ f _
                ∙ cong (P'⊗Q'._,⊗ _) (α .N-hom _ _ f p (F-hom P f $ p) refl)

  module _ {P : Functor C (SET ℓP)} {Q : Functor (C ^op) (SET ℓQ)} {ℓP' ℓQ'}
           {P' : Functor C (SET ℓP')} {Q' : Functor (C ^op) (SET ℓQ')}
           (α : PshIsoStrict (P ∘F fromOpOp) (P' ∘F fromOpOp))
           (β : PshIsoStrict Q Q') where

    private
      module P⊗Q = Tensor P Q
      module P'⊗Q' = Tensor P' Q'
    _⊗PshIsoStrict_ : Iso (P ⊗ Q) (P' ⊗ Q')
    _⊗PshIsoStrict_ .Iso.fun = α .trans ⊗PshHomStrict β .trans
    _⊗PshIsoStrict_ .Iso.inv =
      invPshIsoStrict α .trans ⊗PshHomStrict invPshIsoStrict β .trans
    _⊗PshIsoStrict_ .Iso.sec =
      P'⊗Q'.ind (λ _ → P'⊗Q'.isSet⊗ _ _)
        (λ _ _ → cong₂ P'⊗Q'._,⊗_
          (nIso α _ .snd .fst _)
          (nIso β _ .snd .fst _))
    _⊗PshIsoStrict_ .Iso.ret =
      P⊗Q.ind (λ _ → P⊗Q.isSet⊗ _ _)
        (λ _ _ → cong₂ P⊗Q._,⊗_
          (nIso α _ .snd .snd _)
          (nIso β _ .snd .snd _))

module _ {C : Category ℓC ℓC'} {ℓP ℓQ} where
  ⊗-BifStrict : Bifunctor (PRESHEAF (C ^op) ℓP) (PRESHEAF C ℓQ) (SET _)
  ⊗-BifStrict = mkBifunctorPar ⊗-ParBifStrict
    where
    ⊗-ParBifStrict : BifunctorPar _ _ _
    ⊗-ParBifStrict .BifunctorPar.Bif-ob P Q = (P ∘F toOpOp) ⊗ Q , isSet⊗
    ⊗-ParBifStrict .BifunctorPar.Bif-hom× α β =
      pshhom (α .N-ob) (α .N-hom) ⊗PshHomStrict β
    ⊗-ParBifStrict .BifunctorPar.Bif-×-id {c = S}{d = R} =
      funExt (ind (S ∘F toOpOp) R (λ pq → isSet⊗ _ _) λ _ _ → refl)
    ⊗-ParBifStrict .BifunctorPar.Bif-×-seq {c = S} {d = R} _ _ _ _ =
      funExt (ind (S ∘F toOpOp) R (λ pq → isSet⊗ _ _) λ _ _ → refl)

module _ {C : Category ℓC ℓC'} {ℓP} where
  ◇FStrict : Functor (PRESHEAF C ℓP) (PRESHEAF C (ℓ-max (ℓ-max ℓC ℓC') ℓP))
  ◇FStrict =
    CurryBifunctor' $ Sym $
      ⊗-BifStrict ∘Fl CurryBifunctor' (HomBif C ∘Fr fromOpOp)

  ◇Strict : Presheaf C ℓP → Presheaf C (ℓ-max (ℓ-max ℓC ℓC') ℓP)
  ◇Strict = ◇FStrict .F-ob

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D
  module ext-⊗ {ℓP}{ℓQ} (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf C ℓQ){d} =
    Tensor (F-ob (CurryBifunctor' (compR P fromOpOp)) d ∘F toOpOp) Q

  extStrict : D o-[ ℓP ]-* C
    → Functor (PRESHEAF C ℓ)
              (PRESHEAF D (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓ))
  extStrict P = CurryBifunctor' $ Sym $ ⊗-BifStrict ∘Fl CurryBifunctor' (P ∘Fr fromOpOp)
  private
    -- Less nice than with PresheafCategory becaues of OpOp stuff
    test-ext : ∀ (P : D o-[ ℓP ]-* C) (Q : Presheaf C ℓQ) d
      → ⟨ (extStrict P ⟅ Q ⟆) .F-ob d ⟩ ≡
        ((F-ob (CurryBifunctor' (compR P fromOpOp)) d ∘F toOpOp) ⊗ Q)
    test-ext P Q d = refl

  extStrict-HomR :
    {Q : Presheaf C ℓQ}
    {R : Presheaf C ℓR}
    (P : D o-[ ℓP ]-* C)
    (α : PshHomStrict Q R)
    → PshHomStrict (extStrict P ⟅ Q ⟆) (extStrict P ⟅ R ⟆)
  extStrict-HomR {Q = Q} {R = R} P α .N-ob _ = idPshHomStrict ⊗PshHomStrict α
  extStrict-HomR {Q = Q} {R = R} P α .N-hom c c' f p p' e =
    P⊗Q.ind
      {A = λ p → F-ob (extStrict P) R .F-hom f
        ((idPshHomStrict ⊗PshHomStrict α) p)
        ≡
        (idPshHomStrict ⊗PshHomStrict α)
        (F-ob (extStrict P) Q .F-hom f p)}
      (λ _ → P⊗R.isSet⊗ _ _)
      (λ _ _ → refl)
      p

    ∙ cong (idPshHomStrict ⊗PshHomStrict α) e
    where
      module P⊗Q = ext-⊗ P Q
      module P⊗R = ext-⊗ P R

  extStrict-HomL : ∀
    {P : D o-[ ℓP ]-* C}
    {Q : D o-[ ℓQ ]-* C}
    (α : RelatorHomStrict P Q)
    (R : Presheaf C ℓR)
    → PshHomStrict (extStrict P ⟅ R ⟆) (extStrict Q ⟅ R ⟆)
  extStrict-HomL α R .N-ob d =
    pshhom (appL-HomStrict α d .N-ob) (appL-HomStrict α d .N-hom)
      ⊗PshHomStrict idPshHomStrict
  extStrict-HomL {P = P}{Q = Q} α R .N-hom d d' f =
    P⊗R.ind (λ _ → isPropΠ2 λ _ _ → Q⊗R.isSet⊗ _ _)
      λ p r ⊗ e →
        cong (Q⊗R._,⊗ _) (appR-HomStrict α _ .N-hom _ _ _ _ _ refl)
        ∙ cong (extStrict-HomL α R .N-ob d) e
    where
      module P⊗R = ext-⊗ P R
      module Q⊗R = ext-⊗ Q R

  ext-IsoL : ∀
    {P : D o-[ ℓP ]-* C}
    {Q : D o-[ ℓQ ]-* C}
    (α : RelatorIsoStrict P Q)
    (R : Presheaf C ℓR)
    → PshIsoStrict (extStrict P ⟅ R ⟆) (extStrict Q ⟅ R ⟆)
  ext-IsoL {P = P}{Q = Q} α R =
    Isos→PshIsoStrict
      (λ d → pshiso (pshhom (appL-HomStrict (α .trans) d .N-ob)
                            (appL-HomStrict (α .trans) d .N-hom))
                    (λ x → nIso α (d , x))
             ⊗PshIsoStrict pshiso idPshHomStrict λ _ → IsoToIsIso idIso)
      λ x y f → P⊗R.ind (λ _ → Q⊗R.isSet⊗ _ _)
        λ p r → cong₂ Q⊗R._,⊗_
          ((sym $ α .trans .N-hom _ _ (f , C.id) p _
            (funExt⁻ (sym $ Bif-L×-agree P f) p))
          ∙ (sym $ funExt⁻ (Bif-L×-agree Q f) _ ))
          refl
      where
      module P⊗R = ext-⊗ P R
      module Q⊗R = ext-⊗ Q R

  CoContinuous : {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PRESHEAF C ℓ) (PRESHEAF D (ℓP ℓ)))
    → Typeω
  CoContinuous P = ∀ {ℓ} (Q : Presheaf C ℓ)
    → PshIsoStrict (P ⟅ Q ⟆)
        (extStrict (CurriedToBifunctorLStrict (P ∘F CurryBifunctorL' (HomBif C))) .F-ob Q)

module _ {C : Category ℓC ℓC'} where
  private
    test-ext' : ∀ (Q : Presheaf C ℓQ) →
      extStrict (HomBif C) ⟅ Q ⟆ ≡ ◇Strict Q
    test-ext' Q = refl

  module _ (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
      module ◇P = PresheafNotation (◇Strict P)
      module ◇P⊗ = ext-⊗ (HomBif C) P
    CoYonedaStrict : PshIsoStrict P (◇Strict P)
    CoYonedaStrict .trans .N-ob x p = id C ◇P⊗.,⊗ p
    CoYonedaStrict .trans .N-hom c c' f p' p e =
      cong₂ ◇P⊗._,⊗_ (C .⋆IdR _ ∙ (sym $ C .⋆IdL _)) refl
      ∙ (sym $ ◇P⊗.swap (id C) f p')
      ∙ cong₂ ◇P⊗._,⊗_ refl e
    CoYonedaStrict .nIso x = ◇P→P , ◇P-rt , P.⋆IdL
      where
        ◇P→P : ◇P.p[ x ] → P.p[ x ]
        ◇P→P = ◇P⊗.rec P.isSetPsh P._⋆_ λ f g q → sym $ P.⋆Assoc f g q

        ◇P-rt : section (λ p → C .id ◇P⊗.,⊗ p) ◇P→P
        ◇P-rt = ◇P⊗.ind (λ f⊗p → isSet⊗ _ _)
          λ f p → ◇P⊗.swap _ _ _ ∙ cong (◇P⊗._,⊗ p) (C .⋆IdL f)

module _ {B : Category ℓ ℓ'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _ (F : Functor B C) (P : C o-[ ℓP ]-* D) (Q : Presheaf D ℓQ) where
    private
      F*P = CurriedToBifunctorLStrict (reindPshFStrict F ∘F CurryBifunctorL' P)
      module P⊗Q {b} = ext-⊗ P Q {F .F-ob b}
      module F*P⊗Q {b} = ext-⊗ F*P Q {b}
    reindPsh-⊗Strict :
      PshIsoStrict (reindPsh F (extStrict P ⟅ Q ⟆)) (extStrict F*P ⟅ Q ⟆)
    reindPsh-⊗Strict .trans .N-ob b =
      P⊗Q.rec F*P⊗Q.isSet⊗ F*P⊗Q._,⊗_ F*P⊗Q.swap
    reindPsh-⊗Strict .trans .N-hom b b' f p p' e =
      P⊗Q.ind {A = λ p' →
        (extStrict F*P ⟅ Q ⟆ PresheafNotation.⋆ f)
         (trans reindPsh-⊗Strict .N-ob b' p')
         ≡ trans reindPsh-⊗Strict .N-ob b
           ((reindPsh F (extStrict P ⟅ Q ⟆) PresheafNotation.⋆ f) p')}
      (λ _ → F*P⊗Q.isSet⊗ _ _)
      (λ pp q → refl)
      p
      ∙ cong (P⊗Q.rec F*P⊗Q.isSet⊗ F*P⊗Q._,⊗_ F*P⊗Q.swap) e
    reindPsh-⊗Strict .nIso b =
      F*P⊗Q.rec P⊗Q.isSet⊗ P⊗Q._,⊗_ P⊗Q.swap
      , F*P⊗Q.ind (λ _ → F*P⊗Q.isSet⊗ _ _) (λ _ _ → refl)
      , P⊗Q.ind (λ _ → P⊗Q.isSet⊗ _ _) (λ _ _ → refl)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  reindPshFStrict-cocont : (F : Functor C D) → CoContinuous (reindPshFStrict F)
  reindPshFStrict-cocont F Q =
    reindPshFStrict F ⟅ Q ⟆
      PshIsoStrict⟨ reindPshIsoStrict F (CoYonedaStrict Q) ⟩
    reindPshFStrict F ⟅ ◇Strict Q ⟆
      PshIsoStrict⟨ reindPsh-⊗Strict F (HomBif D) Q ⟩
    extStrict _ ⟅ Q ⟆
    ∎PshIsoStrict
