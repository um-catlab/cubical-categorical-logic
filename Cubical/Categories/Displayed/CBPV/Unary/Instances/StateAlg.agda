-- Adjunction between Sets and (Boolean) state algebras
-- and their lifting to Families and displayed algebras
-- as CBPV and CBPVᴰ models.

{-# OPTIONS --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg where

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
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Base
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

StateAlgebra : (l : Level) → Type (ℓ-suc l)
StateAlgebra l = Σ[ X ∈ hSet l ] StateAlg ⟨ X ⟩

StateAlgHom : StateAlgebra ℓ → StateAlgebra ℓ → Type ℓ
StateAlgHom A B = Σ[ f ∈ (⟨ A .fst ⟩ → ⟨ B .fst ⟩) ] Homo f (A .snd) (B .snd)

StateAlgHom≡ : ∀ {A B : StateAlgebra ℓ} (f g : StateAlgHom A B)
  → f .fst ≡ g .fst → f ≡ g
StateAlgHom≡ {B = B} f g = Σ≡Prop (λ h → isPropHomo (B .fst .snd))

STATEALG : (l : Level) → Category (ℓ-suc l) l
STATEALG l .Category.ob = StateAlgebra l
STATEALG l .Category.Hom[_,_] = StateAlgHom
STATEALG l .Category.id = (idfun _) , idHomo
STATEALG l .Category._⋆_ f g = (g .fst ∘ f .fst) , (f .snd ⋆Homo g .snd)
STATEALG l .Category.⋆IdL {y = B} f =
  Σ≡Prop (λ h → isPropHomo (B .fst .snd)) refl
STATEALG l .Category.⋆IdR {y = B} f =
  Σ≡Prop (λ h → isPropHomo (B .fst .snd)) refl
STATEALG l .Category.⋆Assoc {w} {x} {y} {z} f g h =
  Σ≡Prop (λ k → isPropHomo (z .fst .snd)) refl
STATEALG l .Category.isSetHom {y = B} =
  isSetΣ (isSetΠ (λ _ → B .fst .snd))
    (λ _ → isProp→isSet (isPropHomo (B .fst .snd)))

StateAlgForget : Functor (STATEALG ℓ) (SET ℓ)
StateAlgForget .Functor.F-ob A = A .fst
StateAlgForget .Functor.F-hom f = f .fst
StateAlgForget .Functor.F-id = refl
StateAlgForget .Functor.F-seq f g = refl

StateAlgFamilyᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (STATEALG ℓ)
  (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.ob[_] B = ⟨ B .fst ⟩ → hSet ℓᴰ
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.Hom[_][_,_] f Xᴰ Yᴰ =
  ∀ x → ⟨ Xᴰ x ⟩ → ⟨ Yᴰ (f .fst x) ⟩
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.idᴰ x xᴰ = xᴰ
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ._⋆ᴰ_ {f = f} fᴰ gᴰ x xᴰ =
  gᴰ (f .fst x) (fᴰ x xᴰ)
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.⋆IdLᴰ fᴰ = refl
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.⋆IdRᴰ fᴰ = refl
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
StateAlgFamilyᴰ ℓ ℓᴰ .Categoryᴰ.isSetHomᴰ {yᴰ = Yᴰ} =
  isSetΠ λ x → isSetΠ λ xᴰ → Yᴰ _ .snd

StateAlgStructureᴰ : ∀ ℓ ℓᴰ →
  StructureOver (∫C (StateAlgFamilyᴰ ℓ ℓᴰ))
    (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ ℓᴰ)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.ob[_] (B , Xᴰ) =
  StateAlgᴰ (B .snd) (λ x → ⟨ Xᴰ x ⟩)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.Hom[_][_,_] (f , fᴰ) Bᴰ Bᴰ' =
  Homoᴰ fᴰ (f .snd) Bᴰ Bᴰ'
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.idᴰ = idHomoᴰ
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver._⋆ᴰ_ {z = (C , Cᴰ)} ϕᴰ ψᴰ =
  (ϕᴰ ⋆Homoᴰ ψᴰ) (C .fst .snd)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.isPropHomᴰ {y = B , Bᴰ} =
  isPropHomoᴰ (λ x → Bᴰ x .snd)

STATEALGᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (STATEALG ℓ)
  (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
STATEALGᴰ ℓ ℓᴰ =
  ∫Cᴰ (StateAlgFamilyᴰ ℓ ℓᴰ)
    (StructureOver→Catᴰ (StateAlgStructureᴰ ℓ ℓᴰ))

StateAlgForgetᴰ : Functorᴰ StateAlgForget (STATEALGᴰ ℓ ℓᴰ) (SETᴰ ℓ ℓᴰ)
StateAlgForgetᴰ .Functorᴰ.F-obᴰ Bᴰ = Bᴰ .fst
StateAlgForgetᴰ .Functorᴰ.F-homᴰ fᴰ = fᴰ .fst
StateAlgForgetᴰ .Functorᴰ.F-idᴰ = refl
StateAlgForgetᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

module _ (X : Type ℓ) where
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
      recFSA .Homo.rd-hom ft ff = sym (B.rd-rd _ _ _ _)
      recFSA .Homo.wt-hom false f =
        B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)
      recFSA .Homo.wt-hom true f =
        B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)

      private module recFSA = Homo recFSA
      recFSA-β : ∀ x → recFSA-f (η x) ≡ i x
      recFSA-β x = sym $ B.rd-wt (i x)

    module _ {f : (Bool → Bool × X) → Y}
      (ϕ : Homo f FreeStateAlg B) where
      private
        module ϕ = Homo ϕ
      recFSA-η : ∀ x → recFSA-f (f ∘ η) x ≡ f x
      recFSA-η x =
        cong₂ B.rd (sym $ ϕ.wt-hom _ _) (sym $ ϕ.wt-hom _ _)
        ∙ (sym $ ϕ.rd-hom _ _)
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
StateAlgCBPVState .snd .fst V B .Homo.rd-hom Mt Mf = refl
StateAlgCBPVState .snd .fst V B .Homo.wt-hom b M = refl
StateAlgCBPVState .snd .snd S A .Homo.rd-hom Mt Mf =
  funExt λ x → S .snd .Homo.rd-hom (Mt x) (Mf x)
StateAlgCBPVState .snd .snd S A .Homo.wt-hom b M =
  funExt λ x → S .snd .Homo.wt-hom b (M x)

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
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .fst Vᴰ .Homoᴰ.rd-homᴰ Mt Mf Mtᴰ Mfᴰ = refl
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .fst Vᴰ .Homoᴰ.wt-homᴰ b M Mᴰ = refl
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .snd Sᴰ .Homoᴰ.rd-homᴰ Mt Mf Mtᴰ Mfᴰ i x xᴰ =
  Sᴰ .snd .Homoᴰ.rd-homᴰ (Mt x) (Mf x)
    (Mtᴰ x xᴰ) (Mfᴰ x xᴰ) i
StateAlgCBPVStateᴰ ℓ ℓᴰ .snd .snd Sᴰ .Homoᴰ.wt-homᴰ b M Mᴰ i x xᴰ =
  Sᴰ .snd .Homoᴰ.wt-homᴰ b (M x) (Mᴰ x xᴰ) i


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
  pack .rd-hom (ft , ftᴰ) (ff , ffᴰ) = funExt λ
    { false → refl
    ; true → refl }
  pack .wt-hom b (ft , ftᴰ) = refl

  pack⁻ : isIso pack-f
  pack⁻ .fst ∫f .fst b .fst = ∫f b .fst
  pack⁻ .fst ∫f .fst b .snd = ∫f b .snd .fst
  pack⁻ .fst ∫f .snd b = ∫f b .snd .snd
  pack⁻ .snd .fst _ = refl
  pack⁻ .snd .snd _ = refl

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
      recFSAᴰ .Homoᴰ.rd-homᴰ st sf stᴰ sfᴰ = hSetReasoning.rectifyOut (_ , isSetB) Yᴰ $
        ∫recFSAᴰ .rd-hom (st , stᴰ) (sf , sfᴰ)
      recFSAᴰ .Homoᴰ.wt-homᴰ b s sᴰ = hSetReasoning.rectifyOut (_ , isSetB) Yᴰ $
        ∫recFSAᴰ .wt-hom b (s , sᴰ)

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
      ϕ.rd-hom _ _ ∙ cong₂ B'.rd (b'ᴰ .fst .snd) (b'ᴰ' .fst .snd)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .snd =
      Bᴰ.rdᴰ (b'ᴰ .snd) (b'ᴰ' .snd)
    push .StateAlgᴰ.wtᴰ b x .fst .fst = B.wt b (x .fst .fst)
    push .StateAlgᴰ.wtᴰ b x .fst .snd =
      ϕ.wt-hom _ _ ∙ cong (B'.wt b) (x .fst .snd)
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
    σ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ = ΣPathP ((ΣPathPProp (λ _ → isSetB' _ _) refl) , refl)
    σ .Homoᴰ.wt-homᴰ b x xᴰ = ΣPathP ((ΣPathPProp (λ _ → isSetB' _ _) refl) , refl)

    --
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
        recPush .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ = Bᴰ''.rectifyOut $
          Bᴰ''.reind-filler⁻ _
          ∙ ϕψᴰ.∫ .Homo.rd-hom _ _
          ∙ cong₂ (Bᴰ''.∫ .StateAlg.rd)
            (Bᴰ''.reind-filler _)
            (Bᴰ''.reind-filler _)
        recPush .Homoᴰ.wt-homᴰ b x xᴰ = Bᴰ''.rectifyOut $
          Bᴰ''.reind-filler⁻ (λ i → g (StateAlgᴰ.wtᴰ push b xᴰ .fst .snd i))
          ∙ ϕψᴰ.∫ .Homo.wt-hom _ _
          ∙ cong (Bᴰ''.∫ .StateAlg.wt _) (Bᴰ''.reind-filler _)


module _ {X : Type ℓ}(Xᴰ : X → Type ℓᴰ)
  {Y : Type ℓ'} (B : StateAlg Y)
  (i : X → Y) (isSetB : isSet Y)
  where
  private
    module B = StateAlg B

  -- Can we get the universal property for this as a combination of
  -- the universal properties for the others?
  FreeStateAlgⱽ-Xᴰ : Y → Type (ℓ-max (ℓ-max ℓ ℓᴰ) ℓ')
  FreeStateAlgⱽ-Xᴰ y = Σ[ s ∈ fiber (recFSA-f X B i) y ] (∀ b → Xᴰ (s .fst b .snd))

  FreeStateAlgⱽ : StateAlgᴰ B FreeStateAlgⱽ-Xᴰ
  FreeStateAlgⱽ = push (recFSA X B i) (FreeStateAlgᴰ X Xᴰ) isSetB

-- summarizing,
-- - we have an opcartesian lift ηᴰ : C [ η ][ Aᴰ , FSAᴰ Aᴰ ] of Aᴰ
-- - we have a opcartesian lifts σ : C [ ϕ ][ Bᴰ , push ϕ ] for any ϕ : B → B'
--
-- Given any M : C [ A , B ] we can construct a heterogeneous
-- opcartesian lift by composition:
-- - ηᴰ ⋆ᴰ σ[ rec M ] : C [ η ⋆ rec M ][ Aᴰ , Bᴰ ]
-- which we can then reind to be C [ M ][ Aᴰ , Bᴰ ]
--
-- - Second we have FSA Aᴰ ↦ F A


-- given M : C [ A , B ] and Aᴰ over A, we can construct push M Aᴰ as a composition:
-- - first, we get a homomorphism rec M : C [ F A , B ]
-- Given Xᴰ over X, we have η : C [ X , FSA X ]
