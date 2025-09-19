module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
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
import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functor
open Functorᴰ
open PshHom
open PshHomᴰ
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
    F*Dᴰ = reindex Dᴰ F
    module F*Dᴰ = Fibers F*Dᴰ
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module F-× = preservesProvidedBinProductsWithNotation F -×c -×Fc F-×
    module F⟨-×c⟩ {Γ} =
      BinProductNotation
        (preservesUniversalElement→UniversalElement
          (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

    module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
      module F⟨Γ×c⟩ =
        BinProductNotation
          (preservesUniversalElement→UniversalElement
            (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

  open UniversalElement

  module _
    (π₁*C : ∀ {Γ} →
      (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ -×c.π₁)
    (π₁*D : ∀ {Δ} →
      (Δᴰ : Dᴰ.ob[ Δ ]) → CartesianLift Dᴰ Δᴰ -×Fc.π₁)
    where

    -- π₁*D : ∀ {Γ} →
    --   (Δᴰ : Dᴰ.ob[ F ⟅ Γ ⟆ ]) →
    --   CartesianLift (reindex Dᴰ F) Δᴰ -×c.π₁
    -- π₁*D Δᴰ = CartesianLiftReindex F {!π₁*C!}

    private
      module ∀ⱽC = UniversalQuantifierPsh -×c π₁*C
      ∀ⱽPshC = ∀ⱽC.∀ⱽPsh
      module ∀ⱽD = UniversalQuantifierPsh -×Fc π₁*D
      ∀ⱽPshD = ∀ⱽD.∀ⱽPsh

    module _ {Γ : C.ob}
      (Qⱽ : Presheafⱽ (F ⟅ Γ ⟆ -×Fc.×a) Dᴰ ℓQᴰ)
      (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
      where
      private
        module Qⱽ = PresheafⱽNotation Qⱽ
        module ∀ⱽPshD =
          PresheafⱽNotation (∀ⱽPshD Qⱽ)
        module ∀ⱽPshC =
          PresheafⱽNotation (∀ⱽPshC (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ))

      Fᴰπ₁⇒π₁Fᴰ :
        NatTransᴰ (F-×.FNatIso .NT.NatIso.trans)
          (Fᴰ ∘Fᴰ ∀ⱽC.weakenπFᴰ) (∀ⱽD.weakenπFᴰ ∘Fᴰ Fᴰ)
      Fᴰπ₁⇒π₁Fᴰ .NatTransᴰ.N-obᴰ cᴰ =
        introᴰ (π₁*D (Fᴰ .F-obᴰ cᴰ)) $
          Dᴰ.reind ({!!} ∙ {!!}) $
            Fᴰ .F-homᴰ (π₁*C cᴰ .elementⱽ)
      Fᴰπ₁⇒π₁Fᴰ .NatTransᴰ.N-homᴰ fᴰ = {!!}

      -- reindHet∀Psh :
      --   PshIsoⱽ
      --     (reindHet' (Functor→PshHet F Γ) Fᴰ (∀ⱽPshD Qⱽ))
      --     (∀ⱽPshC (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ))
      -- reindHet∀Psh =
      --   reindPshIsoⱽ reindFuncCompIsoⱽ
      --   ⋆PshIsoⱽ reind-seqIsoⱽ _ _ _
      --   ⋆PshIsoⱽ bar
      --   ⋆PshIsoⱽ {!refl!}
      --   ⋆PshIsoⱽ baz
      --   ⋆PshIsoⱽ (invPshIsoⱽ $ reind-seqIsoⱽ _ _ _)
      --   ⋆PshIsoⱽ reindPshIsoⱽ foo
      --   where
      --   foo :
      --     PshIsoⱽ
      --       (reind (F-×.preservesProdPshHet ∘ˡ -×c.×aF)
      --         ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽC.weakenπFᴰ ^opFᴰ)))
      --       (reindHet' F-×.preservesProdPshHet Fᴰ Qⱽ
      --         ∘Fᴰ (∀ⱽC.weakenπFᴰ ^opFᴰ))
      --   foo = eqToPshIsoⱽ (Eq.refl , Eq.refl)

      --   bar :
      --     PshIsoⱽ
      --       (reind
      --           (Functor→PshHet F Γ ⋆PshHom
      --               (Functor→PshHet -×Fc.×aF (F-ob F Γ) ∘ˡ F))
      --           ((Qⱽ ∘Fᴰ (∀ⱽD.weakenπFᴰ ^opFᴰ)) ∘Fᴰ (Fᴰ ^opFᴰ)))
      --       (reind (Functor→PshHet _ Γ) $
      --       (Qⱽ ∘Fᴰ ((∀ⱽD.weakenπFᴰ ∘Fᴰ Fᴰ) ^opFᴰ)))
      --   bar = eqToPshIsoⱽ (Eq.refl , Eq.refl)

      --   -- D-PshHom :
      --   --   PshHom (D [-, F-ob (F ∘F -×c.×aF) Γ ])
      --   --          (D [-, F-ob F Γ -×Fc.×a ])
      --   -- D-PshHom
      --   -- .N-ob d f = f D.⋆ F-×.mapProdStr
      --   -- D-PshHom .N-hom = {!!}

      --   baz :
      --     PshIsoⱽ
      --       (reind {!!} $
      --           (Qⱽ ∘Fᴰ ((Fᴰ ∘Fᴰ ∀ⱽC.weakenπFᴰ) ^opFᴰ))
      --       )
      --       (reind
      --           (Functor→PshHet -×c.×aF Γ ⋆PshHom
      --           (F-×.preservesProdPshHet ∘ˡ -×c.×aF))
      --           ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽC.weakenπFᴰ ^opFᴰ)))
      --   baz = {!!} --eqToPshIsoⱽ (Eq.refl , Eq.refl)


-- Goal: PshIsoⱽ
--       (reind
--        (Functor→PshHet F Γ ⋆PshHom
--         (Functor→PshHet -×Fc.×aF (F-ob F Γ) ∘ˡ F))
--        ((Qⱽ ∘Fᴰ (∀ⱽD.weakenπFᴰ ^opFᴰ)) ∘Fᴰ (Fᴰ ^opFᴰ)))
--       (reind
--        (Functor→PshHet -×c.×aF Γ ⋆PshHom
--         (F-×.preservesProdPshHet ∘ˡ -×c.×aF))
--        ((Qⱽ ∘Fᴰ (Fᴰ ^opFᴰ)) ∘Fᴰ (∀ⱽC.weakenπFᴰ ^opFᴰ)))

      -- reindHet∀Psh .fst .N-obᴰ {p = p} pⱽ =
      --   Qⱽ.reind the-reind-path
      --     $
      --     introᴰ (π₁*D _)
      --       (Dᴰ.reind (cong (F .F-hom) (C.⋆IdL _)
      --                  ∙ F-×.preserves-π₁
      --                  ∙ (sym $ -×Fc.×β₁ {g = F ⟪ -×c.π₂ ⟫})) $
      --         Fᴰ .F-homᴰ (π₁*C _ .elementⱽ))
      --       Qⱽ.⋆ᴰ pⱽ
      --     where
      --     the-reind-path =
      --           ((cong₂ D._⋆_ (cong₂ -×Fc._,p_ -×Fc.×β₁ refl) refl)
      --           ∙ -×Fc.×ue.intro-natural
      --           ∙ -×Fc.⟨
      --           (sym $ D.⋆Assoc _ _ _ )
      --           ∙ cong₂ D._⋆_ (sym F-×.preserves-π₁) refl
      --           ⟩,p⟨ sym F-×.preserves-π₂ ⟩
      --           ∙ -×Fc.⟨ sym $ F .F-seq _ _ ⟩,p⟨ refl ⟩
      --           ∙ -×Fc.⟨
      --           cong (F .F-hom) (sym $ -×c.×β₁) ⟩,p⟨
      --           cong (F .F-hom) (sym -×c.×β₂) ⟩
      --           )
      -- reindHet∀Psh .fst .N-homᴰ {fᴰ = fᴰ} {pᴰ = pᴰ} =
      --   Qⱽ.rectify $ Qⱽ.≡out $
      --     (sym $ Qⱽ.reind-filler _ _)
      --     ∙ Qⱽ.⟨⟩⋆⟨ (sym $ Qⱽ.reind-filler _ _)
      --             ∙ (sym $ Qⱽ.reind-filler _ _) ⟩
      --     ∙ (sym $ Qⱽ.⋆Assoc _ _ _)
      --     ∙ {!!}
      --     ∙ Qⱽ.⟨⟩⋆⟨ Qⱽ.reind-filler _ _ ⟩
      --     ∙ Qⱽ.reind-filler _ _
      --     ∙ Qⱽ.reind-filler _ _
      -- reindHet∀Psh .snd = {!!}
