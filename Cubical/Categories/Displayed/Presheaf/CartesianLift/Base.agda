{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open PshHom
open PshIso
open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P

  CartesianLift : ∀ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  CartesianLift p Pᴰ = UniversalElementⱽ Cᴰ _ (reindYo p Pᴰ)

  -- TODO: make this functorial
  -- i.e. an input displayed category over C whose objects are Σ[ c ] P.p[ c ] × Pᴰ

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    isFibration : Type _
    isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration Qᴰ)
         where
  isFibrationReind : isFibration (reind {P = P} α Qᴰ)
  isFibrationReind p = isFibQᴰ (α .N-ob _ p) ◁PshIsoⱽ invPshIsoⱽ (reindYo-seqIsoⱽ α Qᴰ p)

-- Reindexing a projectionlike endofunctor gives a displayed endofunctor
-- when cartesian lifts along the projection exists
-- TODO : Find the most general version of this
module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (F : Functor C C)
  (πF : NatTrans F Id)
  where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      CartesianLift (πF ⟦ Γ ⟧) (Cᴰ [-][-, Γᴰ ]))
    where

    open UniversalElementⱽ

    introπF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ Δᴰ , vertexᴰ (πF* Γᴰ) ]
    introπF* {Γᴰ = Γᴰ} γᴰ = introᴰ (πF* Γᴰ) γᴰ

    introπF*⟨_⟩⟨_⟩ :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ Δᴰ' : Cᴰ.ob[ Δ ]}{γ γ' : C [ Δ , F ⟅ Γ ⟆ ]} →
        {Δᴰ≡Δᴰ' : Δᴰ ≡ Δᴰ'} →
        (γ≡γ' : γ ≡ γ') →
        {γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ]} →
        {γᴰ' : Cᴰ [ γ' C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ' , Γᴰ ]} →
        γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ≡Δᴰ' i , Γᴰ ]) ] γᴰ' →
        introπF* γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ≡Δᴰ' i , vertexⱽ (πF* Γᴰ) ]) ] introπF* γᴰ'
    introπF*⟨ γ≡γ' ⟩⟨ γᴰ≡γᴰ' ⟩ i = introπF* (γᴰ≡γᴰ' i)

    π-πF* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ [ πF ⟦ Γ ⟧ ][ vertexⱽ (πF* Γᴰ) , Γᴰ ]
    π-πF* Γᴰ = Cᴰ.reind (C.⋆IdL _) $ πF* Γᴰ .elementⱽ

    β-πF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
      → introπF* γᴰ Cᴰ.⋆ᴰ π-πF* Γᴰ ≡ γᴰ
    β-πF* {Γᴰ = Γᴰ} γᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.≡in (βⱽ (πF* Γᴰ) {pᴰ = γᴰ})

    open NatTrans

    weakenπFᴰ : Functorᴰ F Cᴰ Cᴰ
    weakenπFᴰ .F-obᴰ Γᴰ = πF* Γᴰ .vertexⱽ
    weakenπFᴰ .F-homᴰ {f = γ} {xᴰ = Γᴰ} {yᴰ = Δᴰ} γᴰ =
      introπF* (Cᴰ.reind (sym $ πF .N-hom γ) $ (π-πF* Γᴰ Cᴰ.⋆ᴰ γᴰ))
    weakenπFᴰ .F-idᴰ {xᴰ = Γᴰ} =
        introπF*⟨ F .F-id  ⟩⟨
          Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⋆IdR _
            ∙ (sym $ Cᴰ.reind-filler _ _)
        ⟩
          ▷ (sym $ weak-ηⱽ (πF* Γᴰ))
    weakenπFᴰ .F-seqᴰ γᴰ δᴰ =
      introπF*⟨ F .F-seq _ _ ⟩⟨
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
               ∙ Cᴰ.reind-filler _ _
               ∙ (Cᴰ.≡in $ sym $ β-πF* (Cᴰ.reind (sym $ πF .N-hom _) (π-πF* _ Cᴰ.⋆ᴰ γᴰ)))
               ⟩⋆⟨ refl ⟩
          ∙ (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (πF* _))

    weakenπFNatTransᴰ : NatTransᴰ πF weakenπFᴰ 𝟙ᴰ⟨ Cᴰ ⟩
    weakenπFNatTransᴰ .NatTransᴰ.N-obᴰ Γᴰ =
      Cᴰ.reind (C.⋆IdL _) $ πF* Γᴰ .elementⱽ
    weakenπFNatTransᴰ .NatTransᴰ.N-homᴰ fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.reind-filler _ _
        ∙ (Cᴰ.≡in $ βⱽ (πF* _))
        ∙ (sym $ Cᴰ.reind-filler _ _)
        ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
        ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
