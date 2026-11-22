module Cubical.Categories.Presheaf.Constructions.Tensor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More


open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓR ℓS : Level

open Category
open Bifunctor
open Functor
open NatTrans
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'} where
  module Tensor (P : Functor C (SET ℓP)) (Q : Functor (C ^op) (SET ℓQ)) where
    private
      |P| : C .ob → Type ℓP
      |P| c = ⟨ P ⟅ c ⟆ ⟩

      |Q| : C .ob → Type ℓQ
      |Q| c = ⟨ Q ⟅ c ⟆ ⟩
    data _⊗_ : Type (ℓ-max ℓ $ ℓ-max ℓ' $ ℓ-max ℓP ℓQ) where
      _,⊗_ : ∀ {x} (p : |P| x) (q : |Q| x) → _⊗_
      swap : ∀ {x y} (p : |P| x)(f : C [ x , y ])(q : |Q| y)
        → (p ,⊗ (Q ⟪ f ⟫ $ q)) ≡ ((P ⟪ f ⟫ $ p) ,⊗ q)
      isSet⊗ : isSet _⊗_

    elim : ∀ (A : _⊗_ → hSet ℓA)
      (case-,⊗ : ∀ {x} → (p : |P| x)(q : |Q| x) → ⟨ A (p ,⊗ q) ⟩)
      (case-swap : ∀ {x y} p (f : C [ x , y ]) q
       → case-,⊗ p (Q ⟪ f ⟫ $ q) ≡[ (λ i → ⟨ A (swap p f q i) ⟩) ] case-,⊗ (P ⟪ f ⟫ $ p) q)
      pq → ⟨ A pq ⟩
    elim A case-,⊗ case-swap (p ,⊗ q) = case-,⊗ p q
    elim A case-,⊗ case-swap (swap p f q i) = case-swap p f q i
    elim A case-,⊗ case-swap (isSet⊗ pq pq' path path' i j) =
      isSet→isSetDep (λ a → A a .snd)
        (elim A case-,⊗ case-swap pq)
        (elim A case-,⊗ case-swap pq')
        (λ i → elim A case-,⊗ case-swap (path i))
        (λ i → elim A case-,⊗ case-swap (path' i))
        (isSet⊗ pq pq' path path')
        i j

    rec : ∀ {A : Type ℓA}
      → isSet A
      → (case-,⊗ : ∀ {x} → (p : |P| x)(q : |Q| x) → A)
      → (∀ {x y} p (f : C [ x , y ]) q → case-,⊗ p (Q ⟪ f ⟫ $ q) ≡ case-,⊗ (P ⟪ f ⟫ $ p) q)
      → _⊗_ → A
    rec {_}{A} isSetA case-,⊗ case-swap = elim (λ _ → (A , isSetA)) case-,⊗ case-swap

    opaque
      ind : ∀ {A : _⊗_ → Type ℓA}
        (isPropA : ∀ pq → isProp (A pq))
        (case-,⊗ : ∀ {x} → (p : |P| x)(q : |Q| x) → A (p ,⊗ q))
        pq → A pq
      ind isPropA case-,⊗ = elim (λ _ → _ , isProp→isSet (isPropA _)) case-,⊗
        λ p f q → isProp→PathP (λ i → isPropA (swap p f q i)) (case-,⊗ p (F-hom Q f $ q)) (case-,⊗ (F-hom P f $ p) q)

  open Tensor using (_⊗_; isSet⊗; elim; rec; ind) public
  _⊗NT_ : ∀ {P P' : (Functor C (SET ℓP))}{Q Q' : (Functor (C ^op) (SET ℓQ))}
    (α : NatTrans P' P) (β : NatTrans Q' Q)
    → P' ⊗ Q' → P ⊗ Q
  _⊗NT_ {_}{_}{P}{P'}{Q}{Q'} α β =
    rec P' Q' isSet⊗ (λ {x} p q → N-ob α x p P⊗Q.,⊗ N-ob β x q)
        (λ p f q →
          cong (_ P⊗Q.,⊗_) (funExt⁻ (β .N-hom f) _)
          ∙ P⊗Q.swap _ f _
          ∙ cong (P⊗Q._,⊗ _) (sym $ funExt⁻ (α .N-hom f) _))
      where module P⊗Q = Tensor P Q

  opaque
    ⊗NT-id : ∀ {P : (Functor C (SET ℓP))}{Q : (Functor (C ^op) (SET ℓQ))}
      → (idTrans P ⊗NT idTrans Q) ≡ idfun _
    ⊗NT-id {P = P}{Q = Q} = funExt $ ind P Q (λ pq → isSet⊗ _ _)
      λ p q → refl

    ⊗NT-seq : ∀ {P P' P'' : (Functor C (SET ℓP))}{Q Q' Q'' : (Functor (C ^op) (SET ℓQ))}
      (α : NatTrans P P')(α' : NatTrans P' P'')
      (β : NatTrans Q Q')(β' : NatTrans Q' Q'')
      → ∀ pq → (seqTrans α α' ⊗NT seqTrans β β') pq ≡ (α' ⊗NT β') ((α ⊗NT β) pq)
    ⊗NT-seq {P = P} {P'' = P''} {Q = Q} {Q'' = Q''} α α' β β' =
      P⊗Q.ind (λ _ → isSet⊗ _ _) λ _ _ → refl
      where module P⊗Q = Tensor P Q

  ⊗-Bif : Bifunctor (FUNCTOR C (SET ℓP)) (FUNCTOR (C ^op) (SET ℓQ)) (SET _)
  ⊗-Bif = mkBifunctorPar ⊗-ParBif where
    open BifunctorPar
    ⊗-ParBif : BifunctorPar (FUNCTOR _ _) (FUNCTOR _ _) (SET _)
    ⊗-ParBif .Bif-ob P Q = (P ⊗ Q) , isSet⊗
    ⊗-ParBif .Bif-hom× {P'} {P} {Q'} {Q} α β = α ⊗NT β
    ⊗-ParBif .Bif-×-id {P}{Q} = ⊗NT-id
    ⊗-ParBif .Bif-×-seq α α' β β' = funExt (⊗NT-seq α α' β β')

  ◇F : Functor (PresheafCategory C ℓP) (PresheafCategory C (ℓ-max (ℓ-max ℓ ℓ') ℓP))
  ◇F = CurryBifunctor $ Sym $ ⊗-Bif ∘Fl CurryBifunctor (HomBif C)

  ◇ : Presheaf C ℓP → Presheaf C (ℓ-max (ℓ-max ℓ ℓ') ℓP)
  ◇ = ◇F .F-ob

  private
    test-◇ : ∀ (P : Presheaf C ℓP) x → ⟨ ◇ P .F-ob x ⟩ ≡ (appL (HomBif C) x ⊗ P)
    test-◇ P x = refl

  module _ (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
      module ◇P = PresheafNotation (◇ P)
      module ◇P⊗ {x} = Tensor (appL (HomBif C) x) P
    CoYoneda : PshIso P (◇ P)
    CoYoneda .trans .N-ob x p = C .id ◇P⊗.,⊗ p
    CoYoneda .trans .N-hom x y f p =
      ◇P⊗.swap _ f _ ∙ cong (◇P⊗._,⊗ p) (C .⋆IdL f ∙ (sym $ C .⋆IdR f))
    CoYoneda .nIso x = ◇P→P , ◇P-rt , P.⋆IdL
      where
        ◇P→P : ◇P.p[ x ] → P.p[ x ]
        ◇P→P = ◇P⊗.rec P.isSetPsh P._⋆_ λ f g q → sym $ P.⋆Assoc f g q

        ◇P-rt : section (λ p → C .id ◇P⊗.,⊗ p) ◇P→P
        ◇P-rt = ◇P⊗.ind (λ f⊗p → isSet⊗ _ _)
          λ f p → ◇P⊗.swap _ _ _ ∙ cong (◇P⊗._,⊗ p) (C .⋆IdL f)

  _⊗Hom_ :
    ∀ {P : Functor C (SET ℓP)}{Q : Functor C (SET ℓQ)}
    {R : Functor (C ^op) (SET ℓR)}{S : Functor (C ^op) (SET ℓS)}
    (α : PshHom (P ∘F fromOpOp) (Q ∘F fromOpOp))
    (β : PshHom R S)
    → P ⊗ R → Q ⊗ S
  _⊗Hom_ {P = P}{Q = Q}{R = R}{S = S} α β =
    P⊗R.rec Q⊗S.isSet⊗
      (λ {x} p r → α .N-ob x p Q⊗S.,⊗ β .N-ob x r)
      (λ p f r →
        cong (_ Q⊗S.,⊗_) (β .N-hom _ _ f r)
        ∙ Q⊗S.swap _ f _
        ∙ cong (Q⊗S._,⊗ _) (sym $ α .N-hom _ _ f p))
    where
      module P⊗R = Tensor P R
      module Q⊗S = Tensor Q S

  _⊗Iso_ : ∀ {P : Functor C (SET ℓP)}{Q : Functor C (SET ℓQ)}
    {R : Functor (C ^op) (SET ℓR)}{S : Functor (C ^op) (SET ℓS)}
    (α : PshIso (P ∘F fromOpOp) (Q ∘F fromOpOp))
    (β : PshIso R S)
    → Iso (P ⊗ R) (Q ⊗ S)
  _⊗Iso_ {P = P}{Q = Q}{R = R}{S = S} α β = iso
    (α .trans ⊗Hom β .trans)
    (invPshIso α .trans ⊗Hom invPshIso β .trans)
    (Q⊗S.ind (λ _ → Q⊗S.isSet⊗ _ _)
      (λ q s → cong₂ Q⊗S._,⊗_ (α .nIso _ .snd .fst q) (β .nIso _ .snd .fst s)))
    (P⊗R.ind (λ _ → P⊗R.isSet⊗ _ _)
      (λ p r → cong₂ P⊗R._,⊗_ (α .nIso _ .snd .snd p) (β .nIso _ .snd .snd r)))
    where
      module P⊗R = Tensor P R
      module Q⊗S = Tensor Q S
