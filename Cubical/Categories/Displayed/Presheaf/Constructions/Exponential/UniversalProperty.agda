{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws hiding (cong₂Funct)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable

open Category
open Functor
open Functorᴰ
open isIsoOver
open PshHom
open PshIso
open PshHomᴰ

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {P : Presheaf C ℓP}
    ((Pᴰ , _×ⱽ_*Pᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ)
    (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
    where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      Pᴰ⇒Qᴰ = (Pᴰ , _×ⱽ_*Pᴰ) ⇒PshSmallⱽ Qᴰ
      module Pᴰ⇒Qᴰ = PresheafᴰNotation Pᴰ⇒Qᴰ

    -- The easy case. If we are in the Qᴰ reasoning machine, but the
    -- qᴰ≡qᴰ' is over "refl", then we can use a proof from the Pᴰ⇒Qᴰ
    -- reasoning machine.
    ⇒≡-inS :
      ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p : P.p[ Γ ]}
      {qᴰ qᴰ' : Qᴰ.p[ p ][ vertexⱽ (Γᴰ ×ⱽ p *Pᴰ) ]}
      → Path Pᴰ⇒Qᴰ.p[ _ , Γᴰ ]
          (p , qᴰ)
          (p , qᴰ')
      → Path Qᴰ.p[ _ , vertexⱽ (Γᴰ ×ⱽ p *Pᴰ) ]
          (p , qᴰ)
          (p , qᴰ')
    ⇒≡-inS {Γ}{Γᴰ} qᴰ≡qᴰ' = ΣPathP (refl , (rectify (congS₂ (congS₂ Qᴰ2) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _)) (λ i → qᴰ≡qᴰ' i .snd))) where
      Qᴰ2 : (p p' : P.p[ Γ ]) → Type _
      Qᴰ2 p p' = Qᴰ.p[ p ][ vertexⱽ (Γᴰ ×ⱽ p' *Pᴰ) ]

    -- The general case. If we are in the Pᴰ⇒Qᴰ reasoning machine, we
    -- can't get back to the Qᴰ, but we need to insert the LR-cong
    -- Isoⱽ to one side.
    ⇒≡-in :
      ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p p' : P.p[ Γ ]}
      {qᴰ : Qᴰ.p[ p ][ vertexⱽ (Γᴰ ×ⱽ p *Pᴰ) ]}
      {qᴰ' : Qᴰ.p[ p' ][ vertexⱽ (Γᴰ ×ⱽ p' *Pᴰ) ]}
      → (pqᴰ≡p'qᴰ' : Path Pᴰ⇒Qᴰ.p[ _ , Γᴰ ]
          (p , qᴰ)
          (p' , qᴰ'))
      → Path Qᴰ.p[ _ , vertexⱽ (Γᴰ ×ⱽ p *Pᴰ) ]
          (p , qᴰ)
          ((C.id P.⋆ p') , (LocallyRepresentableⱽNotation.LR-cong Pᴰ _×ⱽ_*Pᴰ (cong fst pqᴰ≡p'qᴰ') Qᴰ.⋆ᴰ qᴰ'))
    ⇒≡-in pqᴰ≡p'qᴰ' =
      sym (Qᴰ.fromPathPPshᴰ (λ i → vertexⱽ (_ ×ⱽ (pqᴰ≡p'qᴰ' (~ i) .fst) *Pᴰ)) (Pᴰ⇒Qᴰ.≡out (sym pqᴰ≡p'qᴰ')))
      ∙ Qᴰ.⟨ Cᴰ.≡in (sym (LocallyRepresentableⱽNotation.LR-cong≡pathToPshHom Pᴰ _×ⱽ_*Pᴰ (cong fst pqᴰ≡p'qᴰ'))) ⟩⋆⟨⟩

    -- Firstly, the universal property of ⇒PshSmall
    module _ where
      open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ

      ⇒PshSmallⱽ-app : PshHomⱽ (Pᴰ⇒Qᴰ ×ⱽPsh Pᴰ) Qᴰ
      ⇒PshSmallⱽ-app .N-obᴰ (α , pᴰ) =
        Qᴰ.reind (P.⋆IdL _) $
          introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) pᴰ) Qᴰ.⋆ᴰ α
      ⇒PshSmallⱽ-app .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} {γᴰ} {α , pᴰ} = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.reind-filler _)
        ∙ sym (Qᴰ.⋆Assoc _ _ _)
        ∙ Qᴰ.⟨ app-naturality-lemma ⟩⋆⟨⟩
        ∙ Qᴰ.⋆Assoc _ _ _
        ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩
    module _ {R : Presheaf C ℓR}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}{α : PshHom R P} where
      private
        module R = PresheafNotation R
        module Rᴰ = PresheafᴰNotation Rᴰ
      open LocallyRepresentableⱽNotation _ _×ⱽ_*Pᴰ
      ⇒PshSmallⱽ-introᴰ⁻ :
        PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ
        → PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ
      ⇒PshSmallⱽ-introᴰ⁻ αᴰ = (αᴰ ×ⱽHom reind-π) ⋆PshHomᴰⱽ ⇒PshSmallⱽ-app

      ⇒PshSmallⱽ-introᴰ :
        PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ
        → PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ
      ⇒PshSmallⱽ-introᴰ αᴰ .N-obᴰ {Γ} {Γᴰ} {r} rᴰ =
        αᴰ .N-obᴰ ((π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ) , (Pᴰ.reind (P.⋆IdL _) (π₂LR Γᴰ (α .N-ob Γ r))))
      ⇒PshSmallⱽ-introᴰ αᴰ .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {r} {γᴰ} {rᴰ} =
      -- TODO: still haven't figured out how to do this without the manual rectify
        rectify (sym (congS₂Bifunct Qᴰ2 _ _ _ _)
                ∙ congS₂ (congS₂ Qᴰ2) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))
        (compPathP
          (λ i → αᴰ .N-obᴰ ((lem1 i) , lem2 i))
          (αᴰ .N-homᴰ
            {fᴰ = funcLR γᴰ}
            {pᴰ = (π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ)
                  , Pᴰ.reind (P.⋆IdL (α .N-ob Γ r)) (π₂LR Γᴰ (α .N-ob Γ r))}))
        where
          Qᴰ2 : (p : P.p[ Δ ])(p' : P.p[ Δ ]) → Type _
          Qᴰ2 p p' = Qᴰ.p[ p ][ vertexⱽ (Δᴰ ×ⱽ p' *Pᴰ) ]

          module αᴰ = PshHomᴰ αᴰ
          lem1 : PathP (λ i → Rᴰ.p[ γ R.⋆ r ][ vertexⱽ (Δᴰ ×ⱽ α .N-hom Δ Γ γ r i *Pᴰ) ])
            (π₁LR Δᴰ (α .N-ob Δ ((R PresheafNotation.⋆ γ) r)) Rᴰ.⋆ⱽᴰ (γᴰ Rᴰ.⋆ᴰ rᴰ))
            (funcLR γᴰ Rᴰ.⋆ᴰ (π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ))
          lem1 = Rᴰ.toPathPPshᴰ (λ i → vertexⱽ (Δᴰ ×ⱽ α .N-hom _ _ γ r i *Pᴰ))
            (sym $
              sym (Rᴰ.⋆Assocᴰⱽᴰ _ _ _)
              ∙ Rᴰ.⟨ sym (Cᴰ.reind-filler _) ∙ β₁LR _ _ ⟩⋆⟨⟩
              ∙ Rᴰ.⋆Assocⱽᴰᴰ _ _ _
              ∙ sym (Rᴰ.reind-filler _)
              ∙ Rᴰ.⟨ symP (PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, _ ]) (λ i → vertexⱽ (Δᴰ ×ⱽ α .N-hom _ _ γ r i *Pᴰ)) (cong (π₁LR Δᴰ) (α .N-hom Δ Γ γ r)))
                ∙ Cᴰ.reind-filler _ ⟩⋆⟨⟩
              ∙ Rᴰ.⋆Assocᴰⱽᴰ _ _ _)

          lem2 : PathP (λ i → Pᴰ.p[ α .N-ob Δ (γ R.⋆ r) ][ vertexⱽ (Δᴰ ×ⱽ α .N-hom Δ Γ γ r i *Pᴰ) ])
            (Pᴰ.reind (P.⋆IdL (α .N-ob Δ (γ R.⋆ r))) (π₂LR Δᴰ (α .N-ob Δ (γ R.⋆ r))))
            (Pᴰ.reind (sym $ α .N-hom Δ Γ γ r) ((funcLR γᴰ Pᴰ.⋆ᴰ Pᴰ.reind (P.⋆IdL (α .N-ob Γ r)) (π₂LR Γᴰ (α .N-ob Γ r)))))
          lem2 = PresheafᴰNotation.toPathPPshᴰ Pᴰ (λ i → vertexⱽ (Δᴰ ×ⱽ α .N-hom _ _ γ r i *Pᴰ))
            (Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ ⟩
            ∙ PresheafᴰNotation.fromPathPPshᴰ Pᴰ (λ i → vertexⱽ (Δᴰ ×ⱽ α .N-hom _ _ γ r i *Pᴰ))
                (cong (π₂LR Δᴰ) (α .N-hom Δ Γ γ r))
            ∙ (sym $ sym (Pᴰ.reind-filler _)
            ∙ Pᴰ.⟨⟩⋆⟨ (sym $ Pᴰ.reind-filler _) ⟩
            ∙ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _)))

      -- opaque
      --   ⇒PshSmallⱽ-β : ∀ (αᴰ : PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ)
      --     → (⇒PshSmallⱽ-introᴰ αᴰ ×ⱽHom reind-π) ⋆PshHomᴰⱽ ⇒PshSmallⱽ-app ≡ αᴰ
      --   ⇒PshSmallⱽ-β αᴰ = makePshHomᴰPath λ {Γ} {Γᴰ} {r} → funExt λ rᴰpᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      --     {!!}
      --     --  sym (Qᴰ.reind-filler _)
      --     -- ∙ sym (∫PshHom αᴰ .N-hom _ _ ? ?)
      --     -- ∙ ?
      --     -- ∙ N-obᴰ⟨_⟩ αᴰ (×≡Snd-hSet R.isSetPsh
      --     --   (Rᴰ.⟨⟩⋆⟨ sym $ Rᴰ.reind-filler _ ⟩ ∙ sym (Rᴰ.⋆Assoc _ _ _) ∙ Rᴰ.⟨ β₁LR _ _ ⟩⋆⟨⟩ ∙ Rᴰ.⋆IdL _)
      --     --   (change-base {C = λ p → Pᴰ.p[ p ][ ? ]} (α .N-ob Γ) P.isSetPsh (R.⋆IdL r)
      --     --     (sym (Pᴰ.reind-filler _ ) ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ ⟩ ∙ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _))))

      --   ⇒PshSmallⱽ-η : ∀ (αᴰ : PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ)
      --     → αᴰ ≡ ⇒PshSmallⱽ-introᴰ ((αᴰ ×ⱽHom reind-π) ⋆PshHomᴰⱽ ⇒PshSmallⱽ-app)
      --   ⇒PshSmallⱽ-η αᴰ = makePshHomᴰPath λ {Γ} {Γᴰ} {r} → funExt λ rᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      --     sym (Qᴰ.⋆IdL _)
      --     ∙ Qᴰ.⟨
      --         extensionalityLR
      --           (Cᴰ.⋆IdL _ ∙ sym
      --           (Cᴰ.⋆Assoc _ {!!} _ ∙ Cᴰ.⟨⟩⋆⟨ β₁LR {!!} {!!} ∙ sym (Cᴰ.reind-filler {!!} _) ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _)
      --           ∙ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ β₁LR {!!} {!!} ⟩ ∙ β₁LR {!!} {!!} ⟩⋆⟨⟩
      --           ∙ Cᴰ.⋆IdL _))
      --           (Pᴰ.⋆IdL _ ∙ sym (Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ sym (Pᴰ.reind-filler {!!} _) ⟩
      --           ∙ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ sym (Pᴰ.reind-filler {!!} _) ⟩
      --           ∙ β₂LR _ _ ∙ sym (Pᴰ.reind-filler {!!} _) ∙ sym (Pᴰ.reind-filler {!!} _)))
      --       ⟩⋆⟨⟩
      --     ∙ {!!}
      --     -- ∙ Qᴰ.⋆Assoc _ _ _ ∙ Qᴰ.⋆Assoc _ _ _
      --     -- ∙ Qᴰ.⟨⟩⋆⟨ sym $ ⇒≡-in $ sym $ sym (∫PshHom αᴰ .N-hom _ _ _ _) ∙ N-obᴰ⟨_⟩ αᴰ (Rᴰ.reind-filler _)  ⟩
      --     -- ∙ Qᴰ.reind-filler _

      -- ⇒PshSmallⱽ-UMPᴰ : Iso (PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ) (PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ)
      -- ⇒PshSmallⱽ-UMPᴰ =
      --   iso ⇒PshSmallⱽ-introᴰ ⇒PshSmallⱽ-introᴰ⁻
      --     (λ αᴰ → sym $ ⇒PshSmallⱽ-η αᴰ)
      --     ⇒PshSmallⱽ-β

    --   opaque
    --     ⇒PshSmallⱽ-introᴰ≡
    --       : ∀ {αᴰ : PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ}{βᴰ : PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ}
    --       → αᴰ ≡ ⇒PshSmallⱽ-introᴰ⁻ βᴰ
    --       → ⇒PshSmallⱽ-introᴰ αᴰ ≡ βᴰ
    --     ⇒PshSmallⱽ-introᴰ≡ = isoFun≡ ⇒PshSmallⱽ-UMPᴰ

    --     ⇒PshSmallⱽ-ext : ∀ {αᴰ βᴰ : PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ}
    --       → ⇒PshSmallⱽ-introᴰ⁻ αᴰ ≡ ⇒PshSmallⱽ-introᴰ⁻ βᴰ
    --       → αᴰ ≡ βᴰ
    --     ⇒PshSmallⱽ-ext = isoInvInjective ⇒PshSmallⱽ-UMPᴰ _ _

    -- module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
    --   private
    --     module Rᴰ = PresheafᴰNotation Rᴰ
    --   open LocallyRepresentableⱽNotation _ _×ⱽ_*Pᴰ
    --   ⇒PshSmallⱽ-introⱽ :
    --     PshHomⱽ (Rᴰ ×ⱽPsh Pᴰ) Qᴰ
    --     → PshHomⱽ Rᴰ Pᴰ⇒Qᴰ
    --   ⇒PshSmallⱽ-introⱽ α⟨rᴰ,pᴰ⟩ =
    --     ⇒PshSmallⱽ-introᴰ ((idPshHomᴰ ×ⱽHom invPshIsoⱽ (reind-idIsoⱽ Pᴰ) .fst) ⋆PshHomⱽ α⟨rᴰ,pᴰ⟩)

    --   ⇒PshSmallⱽ-UMPⱽ : Iso (PshHomⱽ (Rᴰ ×ⱽPsh Pᴰ) Qᴰ) (PshHomⱽ Rᴰ Pᴰ⇒Qᴰ)
    --   ⇒PshSmallⱽ-UMPⱽ =
    --     compIso (precomp⋆PshHomⱽᴰ-Iso (idPshIsoᴰ ×ⱽIso invPshIsoⱽ (reind-idIsoⱽ Pᴰ)))
    --             ⇒PshSmallⱽ-UMPᴰ
