module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation renaming (_∘ˡ_ to _∘ˡNT_)
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.UniversalProperty
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functor
open Functorᴰ
open PshHom
open PshHomᴰ
open UniversalElement
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c : C .Category.ob}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (-×c : BinProductsWith C c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  (F-× : preservesProvidedBinProductsWith F -×c)
  where
  private
    module C = Category C
    module D = Category D
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    F*Dᴰ = Base.reindex Dᴰ F
    module F*Dᴰ = Fibers F*Dᴰ
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module F⟨-×c⟩ {Γ} =
      BinProductNotation
        (preservesUniversalElement→UniversalElement
          (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

    module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
      module F⟨Γ×c⟩ =
        BinProductNotation
          (preservesUniversalElement→UniversalElement
            (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

  mapProdStr : ∀ {Γ} → D [ F ⟅ Γ -×c.×a ⟆ , F ⟅ Γ ⟆ -×Fc.×a ]
  mapProdStr = F ⟪ -×c.π₁ ⟫ -×Fc.,p F ⟪ -×c.π₂ ⟫

  mapProdStrPshHet : ∀ {Γ} →
    PshHet F (C [-, Γ -×c.×a ]) (D [-, F ⟅ Γ ⟆ -×Fc.×a ])
  mapProdStrPshHet = yoRec _ mapProdStr

  prodStrNatTrans : NatTrans (F ∘F -×c.×aF) (-×Fc.×aF ∘F F)
  prodStrNatTrans .NatTrans.N-ob _ = mapProdStr
  prodStrNatTrans .NatTrans.N-hom f =
    -×Fc.,p-extensionality
      (D.⋆Assoc _ _ _
      ∙ cong₂ D._⋆_ refl -×Fc.×β₁
      ∙ (sym $ F .F-seq _ _ )
      ∙ cong (F .F-hom) -×c.×β₁
      ∙ F .F-seq _ _
      ∙ cong₂ D._⋆_ (sym -×Fc.×β₁) refl
      ∙ D.⋆Assoc _ _ _
      ∙ cong₂ D._⋆_ refl (sym -×Fc.×β₁)
      ∙ (sym $ D.⋆Assoc _ _ _))
      (D.⋆Assoc _ _ _
      ∙ cong₂ D._⋆_ refl -×Fc.×β₂
      ∙ (sym $ F .F-seq _ _ )
      ∙ cong (F .F-hom) -×c.×β₂
      ∙ (sym -×Fc.×β₂)
      ∙ cong₂ D._⋆_ refl (sym -×Fc.×β₂)
      ∙ (sym $ D.⋆Assoc _ _ _))

  -- We can build this NatTrans/Iso concretely for products, but
  -- this should be constructible for a general functor comprehension
  -- I believe its more complex for the abstract case because you
  -- need to reason about a profunctor heteromorphism mediated by F
  --
  -- That is,
  -- -×c.×aF is replaced with comprehension of S : Profunctor C C ℓS
  -- -×Fc.×aF is replaced with comprehension of R : Profunctor D D ℓR
  -- and we have a ProfHet F F S R
  -- i.e. a natural transformation S ⇒ precomposeF (F ^op) ∘F R ∘F F
  prodStrNatIso : NatIso (F ∘F -×c.×aF) (-×Fc.×aF ∘F F)
  prodStrNatIso .NatIso.trans = prodStrNatTrans
  prodStrNatIso .NatIso.nIso c =
    isiso
      (the-is-iso .fst -×Fc.×ue.element)
      (-×Fc.×ue.intro-natural
      ∙ -×Fc.×ue.intro≡
        (the-is-iso .snd .fst -×Fc.×ue.element
        ∙ sym (PresheafNotation.⋆IdL (BinProductProf D ⟅ _ ⟆) -×Fc.×ue.element)))
      (F⟨-×c⟩.×ue.intro-natural
      ∙ F⟨-×c⟩.×ue.intro≡
          (-×Fc.×ue.universal ((F ∘F -×c.×aF) .F-ob c) .equiv-proof
            (F-hom F (-×c.×ue.element .fst) , F-hom F (-×c.×ue.element .snd))
            .fst .snd
          ∙ sym (PresheafNotation.⋆IdL (BinProductProf D ⟅ _ ⟆) _)))
    where
    the-is-iso = isEquivToIsIso _ (F-× c ((-×Fc.×aF ∘F F) .F-ob c))

  module _
    (π₁*C : ∀ {Γ} →
      (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ -×c.π₁)
    (π₁*D : ∀ {Δ} →
      (Δᴰ : Dᴰ.ob[ Δ ]) → CartesianLift Dᴰ Δᴰ -×Fc.π₁)
    where

    private
      module ∀ⱽCᴰ = UniversalQuantifierPsh -×c π₁*C
      ∀ⱽPshCᴰ = ∀ⱽCᴰ.∀ⱽPsh
      module ∀ⱽDᴰ = UniversalQuantifierPsh -×Fc π₁*D
      ∀ⱽPshDᴰ = ∀ⱽDᴰ.∀ⱽPsh

    module Fᴰ-weakening (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where
      private
        module Fᴰ = FunctorᴰNotation Fᴰ

      Fᴰ-weakening-NatTransᴰ :
        NatTransᴰ prodStrNatTrans
          (Fᴰ ∘Fᴰ ∀ⱽCᴰ.weakenπFᴰ)
          (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ Fᴰ)
      Fᴰ-weakening-NatTransᴰ .NatTransᴰ.N-obᴰ xᴰ =
        ∀ⱽDᴰ.introπF* $
          Dᴰ.reind (cong (F .F-hom) (C.⋆IdL _) ∙ (sym -×Fc.×β₁)) $
            Fᴰ .F-homᴰ (elementⱽ (π₁*C xᴰ))
      Fᴰ-weakening-NatTransᴰ .NatTransᴰ.N-homᴰ fᴰ =
        Dᴰ.rectify $ Dᴰ.≡out $
          introᴰ-natural (π₁*D _)
          ∙ introᴰ≡ (π₁*D _)
              (change-base (D._⋆ -×Fc.π₁) D.isSetHom
                (-×Fc.,p-extensionality
                  (D.⋆Assoc _ _ _
                  ∙ D.⟨ refl ⟩⋆⟨ -×Fc.×β₁ ⟩
                  ∙ (sym $ F .F-seq _ _)
                  ∙ cong (F .F-hom) (-×c.×β₁)
                  ∙ F .F-seq _ _
                  ∙ D.⟨ sym -×Fc.×β₁ ⟩⋆⟨ refl ⟩
                  ∙ D.⋆Assoc _ _ _
                  ∙ D.⟨ refl ⟩⋆⟨ sym -×Fc.×β₁ ⟩
                  ∙ (sym $ D.⋆Assoc _ _ _))
                  (D.⋆Assoc _ _ _
                  ∙ D.⟨ refl ⟩⋆⟨ -×Fc.×β₂ ⟩
                  ∙ (sym $ F .F-seq _ _)
                  ∙ cong (F .F-hom) (-×c.×β₂)
                  ∙ sym -×Fc.×β₂
                  ∙ D.⟨ refl ⟩⋆⟨ sym -×Fc.×β₂ ⟩
                  ∙ (sym $ D.⋆Assoc _ _ _))
                ∙ (sym $ D.⋆IdR _))
                ((sym $ Dᴰ.reind-filler _ _)
                ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
                ∙ (sym $ Fᴰ.∫F-seqᴰ _ _)
                ∙ Fᴰ.⟨ ∀ⱽCᴰ.βᴰ-πF* _
                       ∙ (sym $ Cᴰ.reind-filler _ _)
                       ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩ ⟩Fᴰ
                ∙ Fᴰ.∫F-seqᴰ _ _
                ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
                ∙ Dᴰ.⟨ sym (∀ⱽDᴰ.βᴰ-πF* _) ⟩⋆⟨ refl ⟩
                ∙ Dᴰ.⋆Assoc _ _ _
                ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩ ∙ Dᴰ.reind-filler _ _ ⟩
                ∙ Dᴰ.reind-filler _ _
                ∙ sym (∀ⱽDᴰ.βᴰ-πF* _)
                ∙ Dᴰ.⟨ sym (introᴰ-natural (π₁*D _)) ⟩⋆⟨ refl ⟩
                ∙ Dᴰ.reind-filler _ _))

      Fᴰ-weakening-isNatIsoᴰ-Ty : Type _
      Fᴰ-weakening-isNatIsoᴰ-Ty =
        ∀ {x} (xᴰ : Cᴰ.ob[ x ]) →
          isIsoᴰ Dᴰ (prodStrNatIso .NatIso.nIso x) (Fᴰ-weakening-NatTransᴰ .NatTransᴰ.N-obᴰ xᴰ)

      module _
        (Fᴰ-weakening-isNatIsoᴰ : Fᴰ-weakening-isNatIsoᴰ-Ty)
        where

        private
          Fᴰ-weakening-NatIsoᴰ :
            NatIsoᴰ prodStrNatIso
              (Fᴰ ∘Fᴰ ∀ⱽCᴰ.weakenπFᴰ)
              (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ Fᴰ)
          Fᴰ-weakening-NatIsoᴰ = record {
              transᴰ = Fᴰ-weakening-NatTransᴰ
            ; nIsoᴰ = Fᴰ-weakening-isNatIsoᴰ }

        module _ {Γ : C.ob} (Qⱽ : Presheafⱽ (F ⟅ Γ ⟆ -×Fc.×a) Dᴰ ℓQᴰ) where
          private
            module Qⱽ = PresheafⱽNotation Qⱽ
            module ∀ⱽPshDᴰ =
              PresheafⱽNotation (∀ⱽPshDᴰ Qⱽ)
            module ∀ⱽPshCᴰ =
              PresheafⱽNotation (∀ⱽPshCᴰ (reindHet' mapProdStrPshHet Fᴰ Qⱽ))

          reindHet∀PshIsoⱽ :
            PshIsoⱽ
              (reindHet' (Functor→PshHet F Γ) Fᴰ (∀ⱽPshDᴰ Qⱽ))
              (∀ⱽPshCᴰ (reindHet' mapProdStrPshHet Fᴰ Qⱽ))
          reindHet∀PshIsoⱽ =
            {!!}
            -- reindPshIsoⱽ reindFuncCompIsoⱽ
            -- ⋆PshIsoⱽ reind-seqIsoⱽ _ _ _
            -- ⋆PshIsoⱽ reindPshIsoⱽ (reind-introIsoⱽ (NatIsoᴰ→PshIsoᴰ (symNatIsoᴰ the-nat-isoᴰ)))
            -- ⋆PshIsoⱽ reind-seqIsoⱽ _ _ _
            -- ⋆PshIsoⱽ
            --   reindPathIsoⱽ
            --     (makePshHomPath (funExt₂ λ x p →
            --       cong₂ D._⋆_ (D.⋆IdL _ ∙ D.⋆IdR _) refl
            --       ∙ (sym $ prodStrNatIso .NT.NatIso.trans .NT.NatTrans.N-hom p)))
            -- ⋆PshIsoⱽ invPshIsoⱽ (reind-seqIsoⱽ _ _ _)
            -- ⋆PshIsoⱽ reindPshIsoⱽ annotateType

            -- where

            -- -- To avoid ugly goals with many reinds,
            -- -- we construct the core of the PshIsoⱽ
            -- -- as this NatIsoᴰ. We then turn it into a PshIsoᴰ,
            -- -- turn that PshIsoᴰ into a PshIsoⱽ, and patch up
            -- -- the necessary reinds in between
            -- the-nat-isoᴰ :
            --   NatIsoᴰ _
            --     ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ))
            --     ((Qⱽ ∘Fᴰ (∀ⱽDᴰ.weakenπFᴰ ^opFᴰ)) ∘Fᴰ (Fᴰ ^opFᴰ))
            -- the-nat-isoᴰ =
            --   (symNatIsoᴰ $ CATᴰ⋆Assoc _ _ _)
            --   ⋆NatIsoᴰ (Qⱽ ∘ʳᴰⁱ
            --               (∘Fᴰ-^opFᴰ-NatIsoᴰ ∀ⱽCᴰ.weakenπFᴰ Fᴰ
            --               ⋆NatIsoᴰ opNatIsoᴰ (symNatIsoᴰ Fᴰ-weakening-NatIsoᴰ)
            --               ⋆NatIsoᴰ (symNatIsoᴰ $ ∘Fᴰ-^opFᴰ-NatIsoᴰ Fᴰ ∀ⱽDᴰ.weakenπFᴰ)))
            --   ⋆NatIsoᴰ CATᴰ⋆Assoc _ _ _

            -- -- This is needed because there is not enough inference if
            -- -- eqToPshIsoⱽ is just used inline above
            -- -- sameissue as reindFuncUnitEq in
            -- -- Displayed.Presheaf.Constructions.Unit.Properties
            -- annotateType :
            --   PshIsoⱽ
            --     (reind (mapProdStrPshHet ∘ˡ -×c.×aF)
            --       ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ)))
            --     (reindHet' mapProdStrPshHet Fᴰ Qⱽ
            --       ∘Fᴰ (∀ⱽCᴰ.weakenπFᴰ ^opFᴰ))
            -- annotateType = eqToPshIsoⱽ (Eq.refl , Eq.refl)
