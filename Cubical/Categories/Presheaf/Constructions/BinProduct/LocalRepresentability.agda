module Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Cartesian
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Functor
open PshHom
open PshIso
open NatTrans
open NatIso

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C

  -- This should be possible to do compositionally if PshProd were
  -- universe polymorphic
  LRProf : (P : Presheaf C ℓP) → Profunctor C C (ℓ-max ℓ' ℓP)
  LRProf P .F-ob x = (C [-, x ]) ×Psh P
  LRProf P .F-hom f = PshHom→NatTrans (×PshIntro (π₁ _ _ ⋆PshHom yoRec _ f) (π₂ _ _))
  LRProf P .F-id = makeNatTransPath $ funExt λ y → funExt λ f → ΣPathP (C.⋆IdR _ , refl)
  LRProf P .F-seq f g = makeNatTransPath $ funExt λ y → funExt λ h →
    ΣPathP ((sym $ C.⋆Assoc (π₁ (C [-, _ ]) P .N-ob y h) f g) , refl)

  LocallyRepresentable : Presheaf C ℓP → Type _
  LocallyRepresentable P = UniversalElements $ LRProf P

LRPresheaf : ∀ (C : Category ℓ ℓ') (ℓP : Level) → Type _
LRPresheaf C ℓP = Σ (Presheaf C ℓP) LocallyRepresentable

module _ {C : Category ℓ ℓ'} ((P , _×P) : LRPresheaf C ℓP) where
  private
    module C = Category C
    module P = PresheafNotation P
  open UniversalElementNotation
  LRPsh→Functor : Functor C C
  LRPsh→Functor = FunctorComprehension (LRProf P) _×P

  πLRF : NatTrans LRPsh→Functor Id
  πLRF .N-ob Γ = (Γ ×P) .element .fst
  πLRF .N-hom {Δ}{Γ} γ = PathPΣ (β (Γ ×P)) .fst

  -- something to do with Beck-Chevalley
  πLRFCart : isCartesian πLRF
  πLRFCart {Δ} {Γ} γ {Θ} γ,P δ γ,P⋆π≡δ⋆γ .fst .fst =
    intro (Δ ×P) (δ , (γ,P P.⋆ (Γ ×P) .element .snd))
  πLRFCart {Δ} {Γ} γ {Θ} γ,P δ γ,P⋆π≡δ⋆γ .fst .snd .fst = sym $ extensionality (Γ ×P) $ ΣPathP
    ( C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ PathPΣ (β (Γ ×P)) .fst ⟩
      ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ PathPΣ (β (Δ ×P)) .fst ⟩⋆⟨ refl ⟩
      ∙ (sym γ,P⋆π≡δ⋆γ)
    , P.⋆Assoc _ _ _ ∙ P.⟨⟩⋆⟨ PathPΣ (β (Γ ×P)) .snd ⟩
    ∙ PathPΣ (β (Δ ×P)) .snd
    )
  πLRFCart {Δ} {Γ} γ {Θ} γ,P δ γ,P⋆π≡δ⋆γ .fst .snd .snd = sym $ PathPΣ (β (Δ ×P)) .fst
  πLRFCart {Δ} {Γ} γ {Θ} γ,P δ γ,P⋆π≡δ⋆γ .snd (δ~ , (γ,P≡δ~⋆⟨γ⟩ , δ≡δ~⋆π)) = ΣPathPProp (λ _ → isProp× (C.isSetHom _ _) (C.isSetHom _ _)) $
    intro≡ (Δ ×P) (ΣPathP (δ≡δ~⋆π , (P.⟨ γ,P≡δ~⋆⟨γ⟩ ⟩⋆⟨⟩ ∙ P.⋆Assoc _ _ _ ∙ P.⟨⟩⋆⟨ PathPΣ (β (Γ ×P)) .snd ⟩ )))

  module _ {R : Presheaf C ℓR} where
    private module R = PresheafNotation R
    ⟪-⟫×P : PshHet LRPsh→Functor R (R ×Psh P)
    ⟪-⟫×P .N-ob Γ r .fst = πLRF .N-ob Γ R.⋆ r
    ⟪-⟫×P .N-ob Γ r .snd = (Γ ×P) .element .snd
    ⟪-⟫×P .N-hom Δ Γ γ r = ΣPathP
      ( (sym $ sym (R.⋆Assoc _ _ _) ∙ R.⟨ fst $ PathPΣ $ β $ Γ ×P ⟩⋆⟨⟩ ∙ R.⋆Assoc _ _ _)
      , (sym $ snd $ PathPΣ $ β $ Γ ×P))

LRPshIso→NatIso : ∀ {C : Category ℓ ℓ'}
  (P : LRPresheaf C ℓP)
  (Q : LRPresheaf C ℓQ)
  → (α : PshIso (P .fst) (Q .fst))
  → NatIso (LRPsh→Functor P) (LRPsh→Functor Q)
LRPshIso→NatIso P Q α = FunctorComprehension-NatIso (LRProf (P .fst)) (LRProf (Q .fst)) (P .snd) (Q .snd)
  (pshiso (mkRelatorHom (λ c d z → z .fst , α .trans .N-ob c (z .snd))
          (λ c c' d f p → ΣPathP (refl , (α .trans .N-hom c c' f (p .snd))))
          (λ _ _ _ _ _ → refl))
    λ x → (λ z → z .fst , α .nIso (x .fst) .fst (z .snd)) , ((λ b → ΣPathP (refl , (α .nIso (x .fst) .snd .fst (b .snd)))) , λ b → ΣPathP (refl , α .nIso (x .fst) .snd .snd (b .snd))))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D

  module _ (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) (α : PshHet F P Q)
    where
    presLRCone : ∀ {x : C.ob}
      → PshHom ((C [-, x ]) ×Psh P) (reindPsh F ((D [-, F ⟅ x ⟆ ]) ×Psh Q))
    presLRCone .N-ob = λ c (f , p) → (F ⟪ f ⟫) , (α .N-ob _ p)
    presLRCone .N-hom = λ _ _ f (g , p) → ΣPathP ((F .F-seq f g) , (α .N-hom _ _ f p))

    presLRCone-Nat : ProfunctorHom (LRProf P) (reindPshF F ∘F LRProf Q ∘F F)
    presLRCone-Nat = mkRelatorHom
      (λ c d → presLRCone .N-ob c)
      (λ c c' d → presLRCone .N-hom c c')
      λ c d d' (g , p) f → ΣPathP ((F .F-seq g f) , refl)

  module _ ((P , _×P) : LRPresheaf C ℓP) (Q : Presheaf D ℓQ)
    (α : PshHet F P Q)
    where
    open UniversalElement
    presLR : Type _
    presLR = ∀ (x : C.ob)
      → becomesUniversal (presLRCone P Q α {x})
        ((x ×P) .vertex)
        ((x ×P) .element)

  module _ (P : LRPresheaf C ℓP) (Q : LRPresheaf D ℓQ)
    (α : PshHet F (P .fst) (Q .fst))
    where
    presLR→NatIso : presLR P (Q .fst) α → NatIso (LRPsh→Functor Q ∘F F) (F ∘F LRPsh→Functor P)
    presLR→NatIso F⟪-×P⟫≅F⟪-⟫×Q = seqNatIso {G = FunctorComprehension (LRProf (Q .fst) ∘F F) (λ c → Q .snd (F-ob F c))}
      (record { trans = natTrans (λ x → D.id) λ _ → idTrans (Id {C = D}) .N-hom _ ; nIso = λ x → idNatIso (Id {C = D}) .nIso _ })
      (symNatIso (preserves-UE→NatIso (LRProf (P .fst)) (LRProf (Q .fst) ∘F F) F
        (presLRCone-Nat (P .fst) (Q .fst) α)
        (P .snd) (λ c → Q .snd (F-ob F c))
        F⟪-×P⟫≅F⟪-⟫×Q))

  module _ (P : LRPresheaf C ℓP) (Q : LRPresheaf D ℓQ)
    (α : PshHet F (P .fst) (Q .fst))
    where
    open UniversalElement
    private
      module Q = PresheafNotation (Q .fst)

    strictPresLR→NatIso :
      (F⟅c×P⟆≡Fc×Q : ∀ c → F ⟅ P .snd c .vertex ⟆ Eq.≡ Q .snd (F ⟅ c ⟆) .vertex)
      → (F⟅π⟆≡π : ∀ c →
        Eq.mixedHEq (Eq.ap (λ Fc×Q → (D [ Fc×Q , F ⟅ c ⟆ ]) × Q.p[ Fc×Q ]) (F⟅c×P⟆≡Fc×Q c))
          (F ⟪ P .snd c .element .fst ⟫ , α .N-ob _ (P .snd c .element .snd))
          (Q .snd (F ⟅ c ⟆) .element))
      → NatIso (LRPsh→Functor Q ∘F F) (F ∘F LRPsh→Functor P)
    strictPresLR→NatIso F⟅c×P⟆≡Fc×Q F⟅π⟆≡π = presLR→NatIso P Q α
      λ c → strictlyPreservesUniversalElement (presLRCone (P .fst) (Q .fst) α)
        (P .snd c)
        (Q .snd (F ⟅ c ⟆))
        (F⟅c×P⟆≡Fc×Q c)
        (F⟅π⟆≡π c)
