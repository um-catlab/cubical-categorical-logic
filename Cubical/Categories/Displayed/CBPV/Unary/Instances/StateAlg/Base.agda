-- Adjunction between Sets and (Boolean) state algebras
-- and their lifting to Families and displayed algebras
-- as CBPV and CBPVᴰ models.

{-# OPTIONS --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base where

open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment

open import Cubical.Algebra.State

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.Pure.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromU
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category hiding (_∘_)
open StructureOver
open Functorᴰ

StateAlgStructure : StructureOver (SET ℓ) ℓ ℓ
StateAlgStructure .StructureOver.ob[_] X = StateAlg ⟨ X ⟩
StateAlgStructure .StructureOver.Hom[_][_,_] f B B' = Homo f B B'
StateAlgStructure .StructureOver.idᴰ = idHomo
StateAlgStructure .StructureOver._⋆ᴰ_ = _⋆Homo_
StateAlgStructure .StructureOver.isPropHomᴰ {y = Y} = isPropHomo (Y .snd)

STATEALG : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
STATEALG ℓ = ∫C $ StructureOver→Catᴰ $ StateAlgStructure {ℓ}

StateAlgebra : (ℓ : Level) → Type (ℓ-suc ℓ)
StateAlgebra ℓ = Category.ob $ STATEALG ℓ

StateAlgHom : StateAlgebra ℓ → StateAlgebra ℓ → Type ℓ
StateAlgHom {ℓ} = Category.Hom[_,_] $ STATEALG ℓ

StateAlgForget : Functor (STATEALG ℓ) (SET ℓ)
StateAlgForget = Fst

StateAlgFamilyᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (STATEALG ℓ) (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
StateAlgFamilyᴰ ℓ ℓᴰ = EqReindex.reindex (SETᴰ ℓ ℓᴰ) StateAlgForget Eq.refl (λ _ _ → Eq.refl)

StateAlgStructureᴰ : ∀ ℓ ℓᴰ →
  StructureOver (∫C (StateAlgFamilyᴰ ℓ ℓᴰ))
    (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ ℓᴰ)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.ob[_] (B , Xᴰ) =
  StateAlgᴰ (B .snd) (λ x → ⟨ Xᴰ x ⟩)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.Hom[_][_,_] (f , fᴰ) Bᴰ Bᴰ' =
  Homoᴰ fᴰ (f .snd) Bᴰ Bᴰ'
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.idᴰ = idHomoᴰ
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver._⋆ᴰ_ {z = (C , Cᴰ)} ϕᴰ ψᴰ =
  ϕᴰ ⋆Homoᴰ ψᴰ
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.isPropHomᴰ {y = B , Bᴰ} =
  isPropHomoᴰ (λ x → Bᴰ x .snd)

STATEALGᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (STATEALG ℓ)
  (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
STATEALGᴰ ℓ ℓᴰ =
  ∫Cᴰ (StateAlgFamilyᴰ ℓ ℓᴰ) $ StructureOver→Catᴰ $ StateAlgStructureᴰ ℓ ℓᴰ

-- manual here is better than using Fstᴰ because it avoids a composition
StateAlgForgetᴰ : Functorᴰ StateAlgForget (STATEALGᴰ ℓ ℓᴰ) (SETᴰ ℓ ℓᴰ)
StateAlgForgetᴰ .Functorᴰ.F-obᴰ Bᴰ = Bᴰ .fst
StateAlgForgetᴰ .Functorᴰ.F-homᴰ fᴰ = fᴰ .fst
StateAlgForgetᴰ .Functorᴰ.F-idᴰ = refl
StateAlgForgetᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

module _ (X : Type ℓ) where
  -- The Free State Algebra can be constructed as the state monad
  FreeStateAlg : StateAlg (Bool → Bool × X)
  FreeStateAlg .StateAlg.rd ft ff = if_then ft true else ff false
  FreeStateAlg .StateAlg.wt b f _ = f b
  FreeStateAlg .StateAlg.wt-rd false _ _ = refl
  FreeStateAlg .StateAlg.wt-rd true _ _ = refl
  FreeStateAlg .StateAlg.rd-wt f = funExt λ { false → refl ; true → refl }
  FreeStateAlg .StateAlg.wt-wt _ _ _ = refl

  module FreeStateAlg = StateAlg FreeStateAlg

  η : X → Bool → Bool × X
  η x b = b , x

  module _ {Y : Type ℓ'} (B : StateAlg Y) where
    private module B = StateAlg B
    module _ (i : X → Y) where
      recFSA-f : (Bool → Bool × X) → Y
      recFSA-f f = B.rd (B.wt (f true  .fst) (i (f true  .snd)))
                           (B.wt (f false .fst) (i (f false .snd)))

      recFSA : Homo recFSA-f FreeStateAlg B
      recFSA .Homo.rd-hom ft ff rdftff p =
        cong recFSA-f p ∙ sym (B.rd-rd _ _ _ _)
      recFSA .Homo.wt-hom false f wtbf p =
        cong recFSA-f p
        ∙ B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)
      recFSA .Homo.wt-hom true f wtbf p =
        cong recFSA-f p
        ∙ B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)

      private module recFSA = Homo recFSA
      recFSA-β : ∀ x → recFSA-f (η x) ≡ i x
      recFSA-β x = sym $ B.rd-wt (i x)

    module _ {f : (Bool → Bool × X) → Y}
      (ϕ : Homo f FreeStateAlg B) where
      private
        module ϕ = Homo ϕ
      recFSA-η : ∀ x → recFSA-f (f ∘ η) x ≡ f x
      recFSA-η x =
        cong₂ B.rd (sym $ ϕ.wt-hom' _ _) (sym $ ϕ.wt-hom' _ _)
        ∙ (sym $ ϕ.rd-hom' _ _)
        ∙ cong f (sym $ FreeStateAlg.rd-wt x)

  module _ (Xᴰ : X → Type ℓ') where
    FreeStateAlgᴰ : StateAlgᴰ FreeStateAlg (λ f → ∀ b → Xᴰ (f b .snd))
    FreeStateAlgᴰ .StateAlgᴰ.rdᴰ {xf} {xt} xfᴰ xtᴰ false = xtᴰ false
    FreeStateAlgᴰ .StateAlgᴰ.rdᴰ {xf} {xt} xfᴰ xtᴰ true  = xfᴰ true
    FreeStateAlgᴰ .StateAlgᴰ.wtᴰ b fᴰ _ = fᴰ b
    FreeStateAlgᴰ .StateAlgᴰ.wt-rdᴰ false _ _ _ _ = refl
    FreeStateAlgᴰ .StateAlgᴰ.wt-rdᴰ true  _ _ _ _ = refl
    FreeStateAlgᴰ .StateAlgᴰ.rd-wtᴰ f fᴰ =
      funExt (λ { false → refl ; true → refl })
    FreeStateAlgᴰ .StateAlgᴰ.wt-wtᴰ b b' f fᴰ = refl

    ηᴰ : mapOver η Xᴰ (λ f → ∀ b → Xᴰ (f b .snd))
    ηᴰ x xᴰ b = xᴰ

FreeStateAlgebra : hSet ℓ → StateAlgebra ℓ
FreeStateAlgebra X .fst .fst = Bool → Bool × ⟨ X ⟩
FreeStateAlgebra X .fst .snd =
  isSetΠ (λ _ → isSet× isSetBool (X .snd))
FreeStateAlgebra X .snd = FreeStateAlg ⟨ X ⟩

StateAlgFree : LeftAdjoint (StateAlgForget {ℓ})
StateAlgFree X .UniversalElement.vertex = FreeStateAlgebra X
StateAlgFree X .UniversalElement.element = η ⟨ X ⟩
StateAlgFree X .UniversalElement.universal B = isIsoToIsEquiv
  ( ( λ i → recFSA-f ⟨ X ⟩ (B .snd) i
          , recFSA ⟨ X ⟩ (B .snd) i)
  , ( λ i → funExt (recFSA-β ⟨ X ⟩ (B .snd) i))
  , ( λ ϕ → Σ≡Prop (λ f → isPropHomo (B .fst .snd))
        (funExt (recFSA-η ⟨ X ⟩ (B .snd) (ϕ .snd))))
  )

StateAlgCBPVEq : MultCBPVCatEq (ℓ-suc ℓ) ℓ
StateAlgCBPVEq = U→MultCBPVEq StateAlgForget StateAlgFree

StateAlgCBPV : MultCBPVCat (ℓ-suc ℓ) ℓ
StateAlgCBPV = forgetEq StateAlgCBPVEq

module _ (C : CBPVCat ℓ ℓ') (CState : StateAlgEnrichment C) where
  private
    module C = Fibers C

  points : C.ob[ 𝓥 ] → Functorⱽ C (StateAlgCBPV {ℓ = ℓ'} .fst)
  points P .F-obᴰ {x = 𝓥} A =
    C.Hom[ _ ][ P , A ] , C.isSetHomᴰ
  points P .F-obᴰ {x = 𝓒} B =
    ((C.Hom[ _ ][ P , B ] , C.isSetHomᴰ) , CState .fst P B)
  points P .F-homᴰ {x = 𝓥} {y = 𝓥} f M = M C.⋆ᴰ f
  points P .F-homᴰ {x = 𝓥} {y = 𝓒} f M = M C.⋆ᴰ f
  points P .F-homᴰ {x = 𝓒} {y = 𝓒} f =
    (λ M → M C.⋆ᴰ f) , CState .snd .snd f P
  points P .F-idᴰ {x = 𝓥} = funExt C.⋆IdRᴰ
  points P .F-idᴰ {x = 𝓒} {xᴰ = B} =
    Σ≡Prop
      (λ h → isPropHomo (points P .F-obᴰ B .fst .snd))
      (funExt C.⋆IdRᴰ)
  points P .F-seqᴰ {x = 𝓥} {y = 𝓥} {z = 𝓥} f g =
    funExt (λ M → sym (C.⋆Assocᴰ M f g))
  points P .F-seqᴰ {x = 𝓥} {y = 𝓥} {z = 𝓒} f g =
    funExt (λ M → sym (C.⋆Assocᴰ M f g))
  points P .F-seqᴰ {x = 𝓥} {y = 𝓒} {z = 𝓒} f g =
    funExt (λ M → sym (C.⋆Assocᴰ M f g))
  points P .F-seqᴰ {x = 𝓒} {y = 𝓒} {z = 𝓒} {zᴰ = B} f g =
    Σ≡Prop
      (λ h → isPropHomo (points P .F-obᴰ B .fst .snd))
      (funExt (λ M → sym (C.⋆Assocᴰ M f g)))

StateAlgCBPVᴰ : ∀ ℓ ℓᴰ → CBPVCatᴰ (StateAlgCBPV {ℓ = ℓ} .fst)
  (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
StateAlgCBPVᴰ ℓ ℓᴰ = U→CBPVᴰ StateAlgForget (StateAlgForgetᴰ {ℓ = ℓ} {ℓᴰ = ℓᴰ})

StateAlgCBPVState : StateAlgEnrichment (StateAlgCBPV {ℓ = ℓ} .fst)
StateAlgCBPVState .fst A B .StateAlg.rd Mt Mf x =
  B .snd .StateAlg.rd (Mt x) (Mf x)
StateAlgCBPVState .fst A B .StateAlg.wt b M x =
  B .snd .StateAlg.wt b (M x)
StateAlgCBPVState .fst A B .StateAlg.wt-rd false Mt Mf =
  funExt λ x → B .snd .StateAlg.wt-rd false (Mt x) (Mf x)
StateAlgCBPVState .fst A B .StateAlg.wt-rd true Mt Mf =
  funExt λ x → B .snd .StateAlg.wt-rd true (Mt x) (Mf x)
StateAlgCBPVState .fst A B .StateAlg.rd-wt M =
  funExt λ x → B .snd .StateAlg.rd-wt (M x)
StateAlgCBPVState .fst A B .StateAlg.wt-wt b b' M =
  funExt λ x → B .snd .StateAlg.wt-wt b b' (M x)
StateAlgCBPVState .snd .fst V B .Homo.rd-hom Mt Mf rdtf p =
  λ i x → p i (V x)
StateAlgCBPVState .snd .fst V B .Homo.wt-hom b M wtbx p =
  λ i x → p i (V x)
StateAlgCBPVState .snd .snd S A .Homo.rd-hom Mt Mf rdtf p =
  λ i x → Homo.rd-hom (S .snd) (Mt x) (Mf x)
    (rdtf x) (funExt⁻ p x) i
StateAlgCBPVState .snd .snd S A .Homo.wt-hom b M wtbx p =
  λ i x → Homo.wt-hom (S .snd) b (M x)
    (wtbx x) (funExt⁻ p x) i

module _ (C : CBPVCat ℓ ℓ') (CState : StateAlgEnrichment C)
  (P : Fibers.ob[_] C 𝓥) where
  pointsPreservesState :
    PreservesStateAlgEnrichment
      (points C CState P) CState StateAlgCBPVState
  pointsPreservesState A B .Homo.rd-hom Mt Mf rdtf p =
    λ i V → Homo.rd-hom (CState .snd .fst V B) Mt Mf rdtf p i
  pointsPreservesState A B .Homo.wt-hom b M wtbx p =
    λ i V → Homo.wt-hom (CState .snd .fst V B) b M wtbx p i

StateAlgCBPVStateᴰ : ∀ ℓ ℓᴰ →
  StateAlgEnrichmentᴰ (StateAlgCBPVState {ℓ = ℓ}) (StateAlgCBPVᴰ ℓ ℓᴰ)
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.rdᴰ Mtᴰ Mfᴰ x xᴰ =
  Bᴰ .snd .StateAlgᴰ.rdᴰ (Mtᴰ x xᴰ) (Mfᴰ x xᴰ)
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.wtᴰ b Mᴰ x xᴰ =
  Bᴰ .snd .StateAlgᴰ.wtᴰ b (Mᴰ x xᴰ)
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.wt-rdᴰ false Mt Mf Mtᴰ Mfᴰ i x xᴰ =
  Bᴰ .snd .StateAlgᴰ.wt-rdᴰ false (Mt x) (Mf x)
    (Mtᴰ x xᴰ) (Mfᴰ x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.wt-rdᴰ true Mt Mf Mtᴰ Mfᴰ i x xᴰ =
  Bᴰ .snd .StateAlgᴰ.wt-rdᴰ true (Mt x) (Mf x)
    (Mtᴰ x xᴰ) (Mfᴰ x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.rd-wtᴰ M Mᴰ i x xᴰ =
  Bᴰ .snd .StateAlgᴰ.rd-wtᴰ (M x) (Mᴰ x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .fst Aᴰ Bᴰ .StateAlgᴰ.wt-wtᴰ b b' M Mᴰ i x xᴰ =
  Bᴰ .snd .StateAlgᴰ.wt-wtᴰ b b' (M x) (Mᴰ x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .fst {V = V} Vᴰ .Homoᴰ.rd-homᴰ
  Mt Mf Mtᴰ Mfᴰ rdtf rdtfᴰ p pᴰ i x xᴰ = pᴰ i (V x) (Vᴰ x xᴰ)
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .fst {V = V} Vᴰ .Homoᴰ.wt-homᴰ
  b M Mᴰ wtbx wtbxᴰ p pᴰ i x xᴰ = pᴰ i (V x) (Vᴰ x xᴰ)
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .snd Sᴰ .Homoᴰ.rd-homᴰ
  Mt Mf Mtᴰ Mfᴰ rdtf rdtfᴰ p pᴰ i x xᴰ =
  Sᴰ .snd .Homoᴰ.rd-homᴰ (Mt x) (Mf x)
    (Mtᴰ x xᴰ) (Mfᴰ x xᴰ) (rdtf x) (rdtfᴰ x xᴰ)
    (funExt⁻ p x) (λ j → pᴰ j x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .snd Sᴰ .Homoᴰ.wt-homᴰ
  b M Mᴰ wtbx wtbxᴰ p pᴰ i x xᴰ =
  Sᴰ .snd .Homoᴰ.wt-homᴰ b (M x) (Mᴰ x xᴰ)
    (wtbx x) (wtbxᴰ x xᴰ) (funExt⁻ p x) (λ j → pᴰ j x xᴰ) i


module _ {X : Type ℓ}{Xᴰ : X → Type ℓ'} where
  open StateAlgᴰ using (∫)

  -- ∫ (FSAᴰ Xᴰ) ≅ FSA (∫ Xᴰ)
  open Homo
  -- this is equivalent to pack⁻ but pack⁻ has better definitional
  -- behavior.
  unpack-f : (Bool → Bool × Σ X Xᴰ)
    → Σ[ f ∈ (Bool → Bool × X) ] (∀ b → Xᴰ (f b .snd))
  unpack-f = recFSA-f (Σ X Xᴰ) (∫ (FreeStateAlgᴰ X Xᴰ))
    (λ (x , xᴰ) → ((λ b → b , x) , λ b → xᴰ))

  unpack : Homo unpack-f (FreeStateAlg (Σ X Xᴰ)) (∫ (FreeStateAlgᴰ X Xᴰ))
  unpack = recFSA (Σ X Xᴰ) (∫ (FreeStateAlgᴰ X Xᴰ))
    (λ (x , xᴰ) → ((λ b → b , x) , λ b → xᴰ))

  pack-f : (Σ[ f ∈ (Bool → Bool × X) ] (∀ b → Xᴰ (f b .snd)))
    → Bool → Bool × Σ X Xᴰ
  pack-f (f , fᴰ) b = f b .fst , f b .snd , fᴰ b

  pack : Homo pack-f (∫ (FreeStateAlgᴰ X Xᴰ)) (FreeStateAlg (Σ X Xᴰ))
  pack .rd-hom (ft , ftᴰ) (ff , ffᴰ) rdtf p =
    cong pack-f p ∙ funExt λ { false → refl ; true → refl }
  pack .wt-hom b (ft , ftᴰ) wtbx p = cong pack-f p

  pack⁻ : isIso pack-f
  pack⁻ .fst ∫f .fst b .fst = ∫f b .fst
  pack⁻ .fst ∫f .fst b .snd = ∫f b .snd .fst
  pack⁻ .fst ∫f .snd b = ∫f b .snd .snd
  pack⁻ .snd .fst _ = refl
  pack⁻ .snd .snd _ = refl

  pack⁻Homo :
    Homo (pack⁻ .fst)
      (FreeStateAlg (Σ X Xᴰ))
      (StateAlgᴰ.∫ (FreeStateAlgᴰ X Xᴰ))
  pack⁻Homo = invHomo pack pack⁻

  module _ {Y : Type ℓ'} {Yᴰ : Y → Type ℓᴰ'}
    {B : StateAlg Y} (Bᴰ : StateAlgᴰ B Yᴰ) where
    private
      module B = StateAlg B
      module Bᴰ = StateAlgᴰ Bᴰ

    module _ (i : X → Y) (iᴰ : ∀ x → Xᴰ x → Yᴰ (i x))
      (isSetB : isSet Y) where
      -- ∫ FSAᴰ → FSA (∫ X Xᴰ) → ∫ Bᴰ
      ∫recFSAᴰ-f : (Σ[ f ∈ (Bool → Bool × X) ] (∀ b → Xᴰ (f b .snd)))
        → Σ Y Yᴰ
      ∫recFSAᴰ-f = recFSA-f (Σ X Xᴰ) Bᴰ.∫
        (λ z → i (z .fst) , iᴰ (z .fst) (z .snd)) ∘ pack-f

      ∫recFSAᴰ : Homo ∫recFSAᴰ-f (∫ (FreeStateAlgᴰ X Xᴰ)) Bᴰ.∫
      ∫recFSAᴰ = pack ⋆Homo recFSA (Σ X Xᴰ) Bᴰ.∫ (λ z → i (z .fst) , iᴰ (z .fst) (z .snd))

      recFSAᴰ-f : ∀ s → (∀ b → Xᴰ (s b .snd)) → Yᴰ (recFSA-f X B i s)
      recFSAᴰ-f s sᴰ = ∫recFSAᴰ-f (s , sᴰ) .snd

      recFSAᴰ : Homoᴰ recFSAᴰ-f (recFSA X B i) (FreeStateAlgᴰ X Xᴰ) Bᴰ
      recFSAᴰ .Homoᴰ.rd-homᴰ st sf stᴰ sfᴰ rdtf rdtfᴰ p pᴰ =
        hSetReasoning.rectifyOut (_ , isSetB) Yᴰ $
          cong (λ q → ∫recFSAᴰ-f (q .fst , q .snd)) (ΣPathP (p , pᴰ))
          ∙ Homo.rd-hom' ∫recFSAᴰ (st , stᴰ) (sf , sfᴰ)
      recFSAᴰ .Homoᴰ.wt-homᴰ b s sᴰ wtbx wtbxᴰ p pᴰ =
        hSetReasoning.rectifyOut (_ , isSetB) Yᴰ $
          cong (λ q → ∫recFSAᴰ-f (q .fst , q .snd)) (ΣPathP (p , pᴰ))
          ∙ Homo.wt-hom' ∫recFSAᴰ b (s , sᴰ)

      recFSAᴰ-β : ∀ x xᴰ
        → recFSAᴰ-f (η X x) (ηᴰ X Xᴰ x xᴰ)
          Bᴰ.P≡[ recFSA-β X B i x ] iᴰ x xᴰ
      recFSAᴰ-β x xᴰ = hSetReasoning.rectifyOut (_ , isSetB) Yᴰ $
        recFSA-β (Σ X Xᴰ) Bᴰ.∫
          (λ z → i (z .fst) , iᴰ (z .fst) (z .snd)) (x , xᴰ)

    module _ (isSetB : isSet Y) where
      recFSAᴰ-η :
          ∀ {f : (Bool → Bool × X) → Y}
          (fᴰ : ∀ s → (∀ b → Xᴰ (s b .snd)) → Yᴰ (f s))
          (f-hom : Homo f (FreeStateAlg X) B)
          (fᴰ-hom : Homoᴰ fᴰ f-hom (FreeStateAlgᴰ X Xᴰ) Bᴰ)
          s sᴰ
        → recFSAᴰ-f (f ∘ η X) (λ x xᴰ → fᴰ _ (ηᴰ X Xᴰ x xᴰ)) isSetB s sᴰ
            Bᴰ.P≡[ recFSA-η X B f-hom s ]
          fᴰ s sᴰ
      recFSAᴰ-η fᴰ f-hom fᴰ-hom s sᴰ =
        hSetReasoning.rectifyOut (_ , isSetB) _ $
        recFSA-η (Σ X Xᴰ) Bᴰ.∫
          (pack⁻Homo ⋆Homo Homoᴰ.∫ fᴰ-hom) (pack-f (s , sᴰ))

module _ {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  (ϕ : Homo f B B')
  {Xᴰ : X → Type ℓᴰ} (Bᴰ : StateAlgᴰ B Xᴰ)
  where
  private
    module B = StateAlg B
    module B' = StateAlg B'
    module ϕ = Homo ϕ
    module Bᴰ = StateAlgᴰ Bᴰ

  module _ (isSetB' : isSet X') where
    -- Not sure if this isSetB' is actually necessary but makes it
    -- easy
    push-Xᴰ : X' → Type _
    push-Xᴰ b' = Σ[ b ∈ fiber f b' ] Xᴰ (b .fst)

    push : StateAlgᴰ B' push-Xᴰ
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .fst .fst =
      B.rd (b'ᴰ .fst .fst) (b'ᴰ' .fst .fst)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .fst .snd =
      ϕ.rd-hom' _ _ ∙ cong₂ B'.rd (b'ᴰ .fst .snd) (b'ᴰ' .fst .snd)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .snd =
      Bᴰ.rdᴰ (b'ᴰ .snd) (b'ᴰ' .snd)
    push .StateAlgᴰ.wtᴰ b x .fst .fst = B.wt b (x .fst .fst)
    push .StateAlgᴰ.wtᴰ b x .fst .snd =
      ϕ.wt-hom' _ _ ∙ cong (B'.wt b) (x .fst .snd)
    push .StateAlgᴰ.wtᴰ b x .snd = Bᴰ.wtᴰ b (x .snd)
    push .StateAlgᴰ.wt-rdᴰ false xt xf xtᴰ xfᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-rd _ _ _)
      , Bᴰ.wt-rdᴰ _ _ _ _ _)
    push .StateAlgᴰ.wt-rdᴰ true xt xf xtᴰ xfᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-rd _ _ _)
      , Bᴰ.wt-rdᴰ _ _ _ _ _)
    push .StateAlgᴰ.rd-wtᴰ x xᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.rd-wt _)
      , Bᴰ.rd-wtᴰ _ _)
    push .StateAlgᴰ.wt-wtᴰ b b' x xᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-wt _ _ _)
      , Bᴰ.wt-wtᴰ _ _ _ _)

    σ-fᴰ : mapOver f Xᴰ push-Xᴰ
    σ-fᴰ x xᴰ = (x , refl) , xᴰ

    σ : Homoᴰ σ-fᴰ ϕ Bᴰ push
    σ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
      ΣPathP (ΣPathPProp (λ _ → isSetB' _ _) p , pᴰ)
    σ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ =
      ΣPathP (ΣPathPProp (λ _ → isSetB' _ _) p , pᴰ)

    module _ {X'' : Type ℓ''} {B'' : StateAlg X''}
      (isSetB'' : isSet X'') {g : X' → X''} (ψ : Homo g B' B'')
      {Xᴰ'' : X'' → Type ℓᴰ''} (Bᴰ'' : StateAlgᴰ B'' Xᴰ'') where
      private
        module ψ = Homo ψ
        module Bᴰ'' where
          open StateAlgᴰ Bᴰ'' public
          open hSetReasoning (_ , isSetB'') Xᴰ'' using (rectifyOut) public
      module _ (fgᴰ : mapOver (g ∘ f) Xᴰ Xᴰ'')
        (ϕψᴰ : Homoᴰ fgᴰ (ϕ ⋆Homo ψ) Bᴰ Bᴰ'') where
        private module ϕψᴰ = Homoᴰ ϕψᴰ
        -- Maybe can avoid this using EqFiber but not sure that it's
        -- ultimately helpful to do so?
        recPush-fᴰ : mapOver g push-Xᴰ Xᴰ''
        recPush-fᴰ b' x =
          Bᴰ''.reind (cong g (x .fst .snd)) (fgᴰ (x .fst .fst) (x .snd))

        recPush : Homoᴰ recPush-fᴰ ψ push Bᴰ''
        recPush .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
          Bᴰ''.rectifyOut $
          cong (λ q → g (q .fst) , recPush-fᴰ (q .fst) (q .snd))
            (ΣPathP (p , pᴰ))
          ∙
          Bᴰ''.reind-filler⁻ _
          ∙ Homo.rd-hom' ϕψᴰ.∫ _ _
          ∙ cong₂ (Bᴰ''.∫ .StateAlg.rd)
            (Bᴰ''.reind-filler _)
            (Bᴰ''.reind-filler _)
        recPush .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ =
          Bᴰ''.rectifyOut $
          cong (λ q → g (q .fst) , recPush-fᴰ (q .fst) (q .snd))
            (ΣPathP (p , pᴰ))
          ∙
          Bᴰ''.reind-filler⁻ (λ i → g (StateAlgᴰ.wtᴰ push b xᴰ .fst .snd i))
          ∙ Homo.wt-hom' ϕψᴰ.∫ _ _
          ∙ cong (Bᴰ''.∫ .StateAlg.wt _) (Bᴰ''.reind-filler _)

        recPush-β : ∀ x xᴰ
          → recPush-fᴰ (f x) (σ-fᴰ x xᴰ)
            Bᴰ''.P≡[ refl ] fgᴰ x xᴰ
        recPush-β x xᴰ = Bᴰ''.rectifyOut (Bᴰ''.reind-filler⁻ _)

module _ {X : Type ℓ}(Xᴰ : X → Type ℓᴰ)
  {Y : Type ℓ'} (B : StateAlg Y)
  (i : X → Y) (isSetB : isSet Y)
  where
  private
    module B = StateAlg B

  FreeStateAlgⱽ-Xᴰ : Y → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓ')
  FreeStateAlgⱽ-Xᴰ y = Σ[ s ∈ fiber (recFSA-f X B i) y ] (∀ b → Xᴰ (s .fst b .snd))

  FreeStateAlgⱽ : StateAlgᴰ B FreeStateAlgⱽ-Xᴰ
  FreeStateAlgⱽ = push (recFSA X B i) (FreeStateAlgᴰ X Xᴰ) isSetB

  -- Q: it is technically unnecessary to provide an explicit
  -- definition of FreeStateAlgᴰ, since we can define it using ⊤ⱽ and
  -- push, in which case we could simplify this definition to just
  --
  -- FreeStateAlgⱽ = push (recFSA (Σ X Xᴰ) B (i ∘ fst)) ⊤ⱽ isSetB
