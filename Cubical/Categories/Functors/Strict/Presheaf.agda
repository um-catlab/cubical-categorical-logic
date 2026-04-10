-- Strict presheaves, strict natural transformations, and SPshHom
-- Written by Claude
module Cubical.Categories.Functors.Strict.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Constructions.Tensor
  using (◇; CoYoneda)
open import Cubical.Categories.Presheaf.Morphism.Alt as PshMor
  using (PshHom; PshIso; isPshIso)

open import Cubical.Categories.Functors.Strict.Base
open StrictFunctor

private
  variable
    ℓc ℓc' ℓd ℓd' : Level

module _  (C : Category ℓc ℓc') where
  StrictPresheaf : (ℓ : Level) → Type _
  StrictPresheaf ℓ = StrictFunctor (C ^op) (SET ℓ)

module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  private
    module C = Category C
    module D = Category D

  Strict-N-ob-Type : (F G : StrictFunctor C D) → Type _
  Strict-N-ob-Type F G = (x : C.ob) → D.Hom[ F .F-ob x , G .F-ob x ]

  Strict-N-hom-Type : (F G : StrictFunctor C D) → Strict-N-ob-Type F G → Type _
  Strict-N-hom-Type F G ϕ = {x y : C.ob} (f : C [ x , y ])
    → (g : D [ F .F-ob x , G .F-ob y ])
    → (ϕ x D.⋆ G .F-hom f) ≡ g
    → F .F-hom f D.⋆ ϕ y ≡ g


  record StrictNatTrans (F G : StrictFunctor C D) : Type (ℓ-max (ℓ-max ℓc ℓc') ℓd') where
    constructor natTrans
    field
      N-ob : Strict-N-ob-Type F G
      N-hom :  Strict-N-hom-Type F G N-ob

  record StrictNatIso (F G : StrictFunctor C D): Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    field
      trans : StrictNatTrans F G
    open StrictNatTrans trans

    field
      Strict-nIso : ∀ (x : C.ob) → isIsoC D (N-ob x)

  open StrictNatTrans

  idStrictTrans : (F : StrictFunctor C D) → StrictNatTrans F F
  idStrictTrans F .N-ob x = D.id
  idStrictTrans F .N-hom f g p = D.⋆IdR _ ∙ (sym $ D.⋆IdL _) ∙ p

  seqStrictTrans : {F G H : StrictFunctor C D}
    (α : StrictNatTrans F G)
    (β : StrictNatTrans G H) → StrictNatTrans F H
  seqStrictTrans α β .N-ob x = (α .N-ob x) D.⋆ (β .N-ob x)
  seqStrictTrans α β .N-hom f g p = compSq D (N-hom α f _ refl) (N-hom β f _ refl) ∙ p

  makeStrictNatTransPath : {F G : StrictFunctor C D}
    {α β : StrictNatTrans F G} →
    α .N-ob ≡ β .N-ob → α ≡ β
  makeStrictNatTransPath p i .N-ob = p i
  makeStrictNatTransPath {F = F}{G = G}{α = α}{β = β} p i .N-hom f g q = help i q
    where
    help : PathP
      (λ i → p i _ D.⋆ G .F-hom f ≡ g → F .F-hom f D.⋆ p i _ ≡ g)
      (α .N-hom f g) (β .N-hom f g)
    help = toPathP (funExt λ r → D .Category.isSetHom _ _ _ _)


  module _ {F G : StrictFunctor C D} (α : StrictNatTrans F G) where
    private
      testStrictTrans-lUnit : seqStrictTrans (idStrictTrans F) α ≡ α
      testStrictTrans-lUnit = makeStrictNatTransPath (funExt (λ _ → D.⋆IdL _))

module _ {C : Category ℓc ℓc'} {ℓ} {P Q : StrictPresheaf C ℓ}
  (α : StrictNatTrans P Q) where
  private
    module C = Category C

    testStrictTrans-lUnit : seqStrictTrans (idStrictTrans P) α ≡ α
    testStrictTrans-lUnit = makeStrictNatTransPath refl

-- ===== Strict presheaf homomorphisms =====
-- PshHomStrict between StrictPresheaves.  N-ob is a plain function
-- (not a D.Hom), so identity is (λ z → z) and composition is
-- function composition — both definitionally unital and associative.

module _ {C : Category ℓc ℓc'} where
  private
    module C = Category C

  module _ {ℓp ℓq} (P : StrictPresheaf C ℓp) (Q : StrictPresheaf C ℓq) where
    SPshHom-N-ob-Type : Type _
    SPshHom-N-ob-Type = ∀ (c : C.ob) → ⟨ P .F-ob c ⟩ → ⟨ Q .F-ob c ⟩

    SPshHom-N-hom-Type : SPshHom-N-ob-Type → Type _
    SPshHom-N-hom-Type ϕ =
      ∀ c c' (f : C [ c , c' ]) (p' : ⟨ P .F-ob c' ⟩) p
        → P .F-hom f p' ≡ p
        → Q .F-hom f (ϕ c' p') ≡ ϕ c p

    record SPshHom : Type (ℓc ⊔ℓ ℓc' ⊔ℓ ℓp ⊔ℓ ℓq) where
      constructor spshhom
      field
        N-ob  : SPshHom-N-ob-Type
        N-hom : SPshHom-N-hom-Type N-ob

    isPropSPshHom-N-hom : (ϕ : SPshHom-N-ob-Type)
      → isProp (SPshHom-N-hom-Type ϕ)
    isPropSPshHom-N-hom ϕ = isPropΠ6
      (λ c _ _ _ _ _ → (Q .F-ob c) .snd _ _)

    SPshHomΣ : Type _
    SPshHomΣ = Σ SPshHom-N-ob-Type SPshHom-N-hom-Type

    isSetSPshHomΣ : isSet SPshHomΣ
    isSetSPshHomΣ = isSetΣ
      (isSetΠ λ c → isSet→ ((Q .F-ob c) .snd))
      (λ _ → isProp→isSet (isPropSPshHom-N-hom _))

    SPshHomΣIso : Iso SPshHom SPshHomΣ
    SPshHomΣIso .Iso.fun α = α .SPshHom.N-ob , α .SPshHom.N-hom
    SPshHomΣIso .Iso.inv (ϕ , h) = spshhom ϕ h
    SPshHomΣIso .Iso.sec _ = refl
    SPshHomΣIso .Iso.ret _ = refl

    isSetSPshHom : isSet SPshHom
    isSetSPshHom = isOfHLevelRetractFromIso 2 SPshHomΣIso isSetSPshHomΣ

  open SPshHom

  module _ {P Q : StrictPresheaf C ℓc} where
    makeSPshHomΣPath : ∀ {α β : SPshHomΣ P Q} → α .fst ≡ β .fst
      → α ≡ β
    makeSPshHomΣPath = Σ≡Prop (isPropSPshHom-N-hom P Q)

    makeSPshHomPath : ∀ {α β : SPshHom P Q} → α .N-ob ≡ β .N-ob
      → α ≡ β
    makeSPshHomPath {α} {β} p =
      isoFunInjective (SPshHomΣIso P Q) α β (makeSPshHomΣPath p)

  -- Identity and composition
  idSPshHom : {P : StrictPresheaf C ℓc} → SPshHom P P
  idSPshHom .N-ob c p = p
  idSPshHom .N-hom c c' f p' p eq = eq

  _⋆SPshHom_ : {P : StrictPresheaf C ℓc}
    {Q : StrictPresheaf C ℓc}
    {R : StrictPresheaf C ℓc}
    → SPshHom P Q → SPshHom Q R → SPshHom P R
  (α ⋆SPshHom β) .N-ob c p = β .N-ob c (α .N-ob c p)
  (α ⋆SPshHom β) .N-hom c c' f p' p eq =
    β .N-hom c c' f (α .N-ob c' p') (α .N-ob c p) (α .N-hom c c' f p' p eq)
  infixr 9 _⋆SPshHom_

  -- Definitional unit and associativity
  module _ {P Q : StrictPresheaf C ℓc} (α : SPshHom P Q) where
    private
      test-⋆SPshHomIdL : idSPshHom ⋆SPshHom α ≡ α
      test-⋆SPshHomIdL = refl

      test-⋆SPshHomIdR : α ⋆SPshHom idSPshHom ≡ α
      test-⋆SPshHomIdR = refl

  module _ {P Q R S : StrictPresheaf C ℓc}
    (α : SPshHom P Q)(β : SPshHom Q R)(γ : SPshHom R S) where
    private
      test-⋆SPshHomAssoc :
        (α ⋆SPshHom β) ⋆SPshHom γ ≡ α ⋆SPshHom (β ⋆SPshHom γ)
      test-⋆SPshHomAssoc = refl

  -- Iso variant
  record SPshIso (P Q : StrictPresheaf C ℓc) : Type (ℓ-max (ℓ-max ℓc ℓc') ℓc) where
    field
      trans : SPshHom P Q
      nIso  : ∀ x → isIso (trans .N-ob x)

  open SPshIso

  module _ {P Q : StrictPresheaf C ℓc} where
    invSPshIso : SPshIso P Q → SPshIso Q P
    invSPshIso α .trans .N-ob c = α .nIso c .fst
    invSPshIso α .trans .N-hom c c' f q' q eq =
      sym (α .nIso c .snd .snd _)
      ∙ cong (α .nIso c .fst)
        (sym (α .trans .N-hom c c' f _ _ refl)
        ∙ cong (Q .F-hom f) (α .nIso c' .snd .fst q')
        ∙ eq)
    invSPshIso α .nIso x .fst = α .trans .N-ob x
    invSPshIso α .nIso x .snd .fst = α .nIso x .snd .snd
    invSPshIso α .nIso x .snd .snd = α .nIso x .snd .fst

  idSPshIso : {P : StrictPresheaf C ℓc} → SPshIso P P
  idSPshIso .trans = idSPshHom
  idSPshIso .nIso _ = IsoToIsIso idIso

-- ===== Strict ◇ and CoYoneda =====

-- Convert a PshHom between the underlying functors of two strict
-- presheaves to an SPshHom (witness-passing form).
PshHom→SPshHom : ∀ {C : Category ℓc ℓc'} {ℓp ℓq}
  → {P : StrictPresheaf C ℓp}{Q : StrictPresheaf C ℓq}
  → PshHom (Strict→Fun P) (Strict→Fun Q)
  → SPshHom P Q
PshHom→SPshHom α .SPshHom.N-ob = α .PshHom.N-ob
PshHom→SPshHom α .SPshHom.N-hom c c' f p' p eq =
  sym (α .PshHom.N-hom c c' f p') ∙ cong (α .PshHom.N-ob c) eq

module _ {C : Category ℓc ℓc'} where
  -- Strict ◇: wrap the non-strict ◇ via Fun→Strict.
  ◇S : ∀ {ℓP} → StrictPresheaf C ℓP
     → StrictPresheaf C (ℓ-max (ℓ-max ℓc ℓc') ℓP)
  ◇S P = Fun→Strict (◇ (Strict→Fun P))

  -- Strict CoYoneda: forward direction as an SPshHom, defined
  -- directly to avoid Functor F-id mismatch from Fun→Strict roundtrip.
  CoYonedaSHom : ∀ {ℓP} (P : StrictPresheaf C ℓP)
    → SPshHom P (◇S P)
  CoYonedaSHom P .SPshHom.N-ob x p =
    CoYoneda (Strict→Fun P) .PshIso.trans .PshHom.N-ob x p
  CoYonedaSHom P .SPshHom.N-hom c c' f p' p eq =
    sym (CoYoneda (Strict→Fun P) .PshIso.trans .PshHom.N-hom c c' f p')
    ∙ cong (CoYoneda (Strict→Fun P) .PshIso.trans .PshHom.N-ob c) eq

  -- Strict CoYoneda: inverse direction as an SPshHom.
  CoYonedaSInv : ∀ {ℓP} (P : StrictPresheaf C ℓP)
    → SPshHom (◇S P) P
  CoYonedaSInv P .SPshHom.N-ob x =
    CoYoneda (Strict→Fun P) .PshIso.nIso x .fst
  CoYonedaSInv {ℓP = ℓP} P .SPshHom.N-hom c c' f p' p eq =
    let P'   = Strict→Fun P
        α    = CoYoneda P'
        tr   : ∀ x → ⟨ P' .Functor.F-ob x ⟩ → ⟨ ◇ P' .Functor.F-ob x ⟩
        tr x = α .PshIso.trans .PshHom.N-ob x
        inv  : ∀ x → ⟨ ◇ P' .Functor.F-ob x ⟩ → ⟨ P' .Functor.F-ob x ⟩
        inv x = α .PshIso.nIso x .fst
        sec  : ∀ x q → tr x (inv x q) ≡ q
        sec x = α .PshIso.nIso x .snd .fst
        ret  : ∀ x q → inv x (tr x q) ≡ q
        ret x = α .PshIso.nIso x .snd .snd
        step : tr c (P' .Functor.F-hom f (inv c' p')) ≡ p
        step = α .PshIso.trans .PshHom.N-hom c c' f (inv c' p')
             ∙ cong (◇ P' .Functor.F-hom f) (sec c' p')
             ∙ eq
    in sym (ret c (P' .Functor.F-hom f (inv c' p')))
       ∙ cong (inv c) step

  -- Section/retraction witnesses.
  CoYonedaSSec : ∀ {ℓP} (P : StrictPresheaf C ℓP)
    → ∀ x p → CoYonedaSInv P .SPshHom.N-ob x
              (CoYonedaSHom P .SPshHom.N-ob x p) ≡ p
  CoYonedaSSec P x = CoYoneda (Strict→Fun P) .PshIso.nIso x .snd .snd

  CoYonedaSRet : ∀ {ℓP} (P : StrictPresheaf C ℓP)
    → ∀ x p → CoYonedaSHom P .SPshHom.N-ob x
              (CoYonedaSInv P .SPshHom.N-ob x p) ≡ p
  CoYonedaSRet P x = CoYoneda (Strict→Fun P) .PshIso.nIso x .snd .fst
