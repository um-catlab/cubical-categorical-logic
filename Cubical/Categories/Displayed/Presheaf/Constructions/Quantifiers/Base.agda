{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation as NT
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
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open NatTrans
open Functor
open Functorᴰ
open PshIso
open PshHom
open PshHomᴰ
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where

  open UniversalElement

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module UniversalQuantifierFPsh
    (F : Functor C C)
    (πF : NatTrans F Id)
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      CartesianLift Cᴰ Γᴰ (πF ⟦ Γ ⟧))
    where

    πF-PshHom : ∀ {Γ} → PshHom (C [-, F ⟅ Γ ⟆ ]) (C [-, Γ ])
    πF-PshHom = yoRec _ (N-ob πF _)

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

    opaque
      unfolding hSetReasoning.reind
      β-πF* :
        ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
          {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
        → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
        → introπF* γᴰ Cᴰ.⋆ᴰ π-πF* Γᴰ ≡ γᴰ
      β-πF* {Γᴰ = Γᴰ} γᴰ =
        Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ ⟩
          ∙ Cᴰ.reind-filler _
          ∙ Cᴰ.reind-filler _
          ∙ Cᴰ.≡in (βⱽ (πF* Γᴰ) {pᴰ = γᴰ})

      βᴰ-πF* :
        ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
          {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
        → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
        → Path
            Cᴰ.Hom[ _ , _ ]
            (_ , introπF* γᴰ Cᴰ.⋆ᴰ πF* Γᴰ .elementⱽ)
            (_ , γᴰ)
      βᴰ-πF* γᴰ =
        Cᴰ.reind-filler _
        ∙ Cᴰ.reind-filler _
        ∙ Cᴰ.≡in (βⱽ (πF* _) {pᴰ = γᴰ})

    open NatTrans

    weakenπFᴰ : Functorᴰ F Cᴰ Cᴰ
    weakenπFᴰ .F-obᴰ Γᴰ = πF* Γᴰ .vertexⱽ
    weakenπFᴰ .F-homᴰ {f = γ} {xᴰ = Γᴰ} {yᴰ = Δᴰ} γᴰ =
      introπF* (Cᴰ.reind (sym $ πF .N-hom γ) $ (π-πF* Γᴰ Cᴰ.⋆ᴰ γᴰ))
    weakenπFᴰ .F-idᴰ {xᴰ = Γᴰ} =
        introπF*⟨ F .F-id  ⟩⟨
          Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _)
            ∙ Cᴰ.⋆IdR _
            ∙ (sym $ Cᴰ.reind-filler _)
        ⟩
          ▷ (sym $ weak-ηⱽ (πF* Γᴰ))
    weakenπFᴰ .F-seqᴰ γᴰ δᴰ =
      introπF*⟨ F .F-seq _ _ ⟩⟨
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩
               ∙ Cᴰ.reind-filler _
               ∙ (Cᴰ.≡in $ sym $ β-πF* (Cᴰ.reind (sym $ πF .N-hom _) (π-πF* _ Cᴰ.⋆ᴰ γᴰ)))
               ⟩⋆⟨ refl ⟩
          ∙ (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ ⟩
          ∙ Cᴰ.reind-filler _
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (πF* _))

    opaque
      unfolding hSetReasoning.reind
      weakenπFNatTransᴰ : NatTransᴰ πF weakenπFᴰ 𝟙ᴰ⟨ Cᴰ ⟩
      weakenπFNatTransᴰ .NatTransᴰ.N-obᴰ Γᴰ =
        Cᴰ.reind (C.⋆IdL _) $ πF* Γᴰ .elementⱽ
      weakenπFNatTransᴰ .NatTransᴰ.N-homᴰ fᴰ =
        Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ ⟩
          ∙ Cᴰ.reind-filler _
          ∙ Cᴰ.reind-filler _
          ∙ (Cᴰ.≡in $ βⱽ (πF* _))
          ∙ (sym $ Cᴰ.reind-filler _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⟨ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩

    module _ (P : Presheaf C ℓP) where
      private
        module P = PresheafNotation P

      selfNatTrans : NatTrans (P ∘F (Id ^opF)) (P ∘F (F ^opF))
      selfNatTrans = P NT.∘ʳ (opNatTrans πF)

      selfPshHet : PshHet F P P
      selfPshHet =
        eqToPshHom _ Eq.refl Eq.refl
        ⋆PshHom NatTrans→PshHom selfNatTrans

      module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
        private
          module Pᴰ = PresheafᴰNotation Pᴰ

        selfNatTransᴰ :
          NatTransᴰ (P ∘ʳ opNatTrans πF)
            (Pᴰ ∘Fᴰ (𝟙ᴰ⟨ Cᴰ ⟩ ^opFᴰ))
            (Pᴰ ∘Fᴰ (weakenπFᴰ ^opFᴰ))
        selfNatTransᴰ = Pᴰ ∘ʳᴰ opNatTransᴰ weakenπFNatTransᴰ

        selfPshHetᴰ :
          PshHetᴰ selfPshHet weakenπFᴰ Pᴰ Pᴰ
        selfPshHetᴰ =
           PshHomEqPshHomᴰ (precomp𝟙ᴰPshIsoᴰ .fst) Eq.refl
           ⋆PshHomᴰ NatTransᴰ→PshHomᴰ selfNatTransᴰ

    module _
      {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
      {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
      where
      private
        module P = PresheafNotation P
        module Q = PresheafNotation Q
        module Pᴰ = PresheafᴰNotation Pᴰ
        module Qᴰ = PresheafᴰNotation Qᴰ

    module _
      {Γ : C.ob}
      (Pⱽ : Presheafⱽ (F ⟅ Γ ⟆) Cᴰ ℓPᴰ) where

      private
        module Pⱽ = PresheafⱽNotation Pⱽ

      ∀FⱽPsh : Presheafⱽ Γ Cᴰ ℓPᴰ
      ∀FⱽPsh = reindHet' (Functor→PshHet F Γ) weakenπFᴰ Pⱽ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {a : C .Category.ob}
  (bp : BinProductsWith C a)
  where

  private
    module bp = BinProductsWithNotation bp
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module UniversalQuantifierPsh
    (π₁* : ∀ {Γ} → (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ bp.π₁)
    where
    open UniversalQuantifierFPsh bp.×aF bp.π₁Nat π₁* public

    module _
      {Γ : C.ob}
      (Pⱽ : Presheafⱽ (Γ bp.×a) Cᴰ ℓPᴰ) where

      private
        module Pⱽ = PresheafⱽNotation Pⱽ

      ∀ⱽPsh : Presheafⱽ Γ Cᴰ ℓPᴰ
      ∀ⱽPsh = ∀FⱽPsh Pⱽ

      module _
        {Q : Presheaf C ℓQ}
        (α : PshHom Q (C [-, Γ ]))
        where

        mkProdPshHom : PshHom (Q ×Psh (C [-, a ])) (C [-, Γ bp.×a ])
        mkProdPshHom = ×PshIntro (π₁ _ _ ⋆PshHom α) (π₂ _ _) ⋆PshHom invPshIso (yoRecIso (bp Γ)) .trans

      module _
        {Q : Presheaf C ℓQ}
        {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
        {α : PshHom Q (C [-, Γ ])}
        (αᴰ : PshHomᴰ (α ⋆PshHom Functor→PshHet bp.×aF Γ)
                     Qᴰ (reindPshᴰFunctor weakenπFᴰ Pⱽ))
        where

        private
          module Q = PresheafNotation Q
          module Qᴰ = PresheafᴰNotation Qᴰ
          module αᴰ = PshHomᴰ αᴰ

-- TODO fix from opaque reind
--         opaque
--           unfolding hSetReasoning.reind
--           ∀ⱽPsh-introᴰ⁻' :
--             PshHomᴰ (mkProdPshHom α) (reind (π₁ Q (C [-, a ])) Qᴰ) Pⱽ
--           ∀ⱽPsh-introᴰ⁻' .N-obᴰ qᴰ =
--             Pⱽ.reind
--               (sym $ bp.,p≡
--                 (((sym $ C.⋆IdL _)
--                   ∙ C.⟨ sym bp.×β₁ ⟩⋆⟨ refl ⟩
--                   ∙ C.⋆Assoc _ _ _
--                   ∙ C.⟨ refl ⟩⋆⟨ sym bp.×β₁ ⟩)
--                   ∙ (sym $ C.⋆Assoc _ _ _))
--                 (sym bp.×β₂
--                 ∙ C.⟨ refl ⟩⋆⟨ sym bp.×β₂ ⟩
--                 ∙ (sym $ C.⋆Assoc _ _ _))) $
--               (introπF* (Cᴰ.reind (sym bp.×β₁) $ Cᴰ.idᴰ) Pⱽ.⋆ᴰ αᴰ.N-obᴰ qᴰ)
--           ∀ⱽPsh-introᴰ⁻' .N-homᴰ =
--             Pⱽ.rectify $ Pⱽ.≡out $
--               (sym $ Pⱽ.reind-filler _)
--               ∙ Pⱽ.⟨⟩⋆⟨ αᴰ.N-obᴰ⟨(sym $ Qᴰ.reind-filler _)⟩ ⟩
--               ∙ Pⱽ.⟨⟩⋆⟨ Pⱽ.≡in αᴰ.N-homᴰ ⟩
--               ∙ (sym $ Pⱽ.⋆Assoc _ _ _)
--               ∙ Pⱽ.⟨
--                 introᴰ-natural (π₁* _)
--                 ∙ (introᴰ≡ (π₁* _) $
--                     change-base (C._⋆ bp.π₁) C.isSetHom
--                       (bp.,p-extensionality
--                         (C.⋆Assoc _ _ _
--                         ∙ C.⟨ refl ⟩⋆⟨ bp.×β₁ ⟩
--                         ∙ (sym $ C.⋆Assoc _ _ _)
--                         ∙ C.⟨ bp.×β₁ ⟩⋆⟨ refl ⟩
--                         ∙ C.⋆IdL _
--                         ∙ (sym $ C.⋆IdR _)
--                         ∙ C.⟨ refl ⟩⋆⟨ sym $ bp.×β₁ ⟩
--                         ∙ (sym $ C.⋆Assoc _ _ _))
--                         (C.⋆Assoc _ _ _
--                         ∙ C.⟨ refl ⟩⋆⟨ bp.×β₂ ⟩
--                         ∙ bp.×β₂
--                         ∙ C.⟨ refl ⟩⋆⟨ sym $ bp.×β₂ ⟩
--                         ∙ (sym $ C.⋆Assoc _ _ _))
--                       ∙ (sym $ C.⋆IdR _)) $
--                       (sym $ Cᴰ.reind-filler _)
--                       ∙ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _)
--                                         ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩ ⟩
--                       ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
--                       ∙ Cᴰ.⟨ βᴰ-πF* _ ⟩⋆⟨ refl ⟩
--                       ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ ⟩⋆⟨ refl ⟩
--                       ∙ Cᴰ.⋆IdL _
--                       ∙ (sym $ Cᴰ.⋆IdR _)
--                       ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ ⟩
--                       ∙ Cᴰ.reind-filler _
--                       ∙ (sym $ βᴰ-πF* _)
--                       ∙ Cᴰ.reind-filler _)
--                 ⟩⋆⟨⟩
--               ∙ Pⱽ.⟨ sym $ introᴰ-natural (π₁* _) ⟩⋆⟨⟩
--               ∙ Pⱽ.⋆Assoc _ _ _
--               ∙ Pⱽ.⟨⟩⋆⟨ Pⱽ.reind-filler _ ⟩

--       module _
--         {Q : Presheaf C ℓQ}
--         {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
--         {α : PshHom Q (C [-, Γ ])}
--         (αᴰ : PshHomᴰ α Qᴰ ∀ⱽPsh)
--         where

-- --         private
-- --           module Q = PresheafNotation Q
-- --           module Qᴰ = PresheafᴰNotation Qᴰ

-- --         ∀ⱽPsh-introᴰ⁻ :
-- --           PshHomᴰ (mkProdPshHom α)
-- --             (reind (π₁ Q (C [-, a ])) Qᴰ) Pⱽ
-- --         ∀ⱽPsh-introᴰ⁻ = ∀ⱽPsh-introᴰ⁻' (αᴰ ⋆PshHomᴰ reind-π)

-- --       module _
-- --         {Q : Presheaf C ℓQ}
-- --         {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
-- --         {α : PshHom Q (C [-, Γ ])}
-- --         (αᴰ : PshHomᴰ
-- --              (×PshIntro (π₁ _ _ ⋆PshHom α) (π₂ _ _ )
-- --                ⋆PshHom invPshIso (yoRecIso (bp Γ)) .trans)
-- --                (reind (π₁ Q (C [-, a ])) Qᴰ) Pⱽ)
-- --         where
-- --         private
-- --           module Q = PresheafNotation Q
-- --           module Qᴰ = PresheafᴰNotation Qᴰ
-- --           module αᴰ = PshHomᴰ αᴰ

-- --         ∀ⱽPsh-introᴰ' :
-- --           PshHomᴰ (α ⋆PshHom Functor→PshHet bp.×aF Γ)
-- --             Qᴰ
-- --             (reindPshᴰFunctor weakenπFᴰ Pⱽ)
-- --         ∀ⱽPsh-introᴰ' .N-obᴰ {x = c} {xᴰ = cᴰ} {p = q} qᴰ =
-- --           Pⱽ.reind
-- --             (bp.×ue.intro≡
-- --               (ΣPathP (
-- --                 (α .N-hom _ _ _ q
-- --                 ∙ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩)
-- --                 ∙ sym bp.×β₁ ,
-- --                 (sym bp.×β₂))))
-- --             $
-- --             αᴰ .N-obᴰ {p = _ , bp.π₂} $
-- --               elementⱽ (π₁* _) Qᴰ.⋆ᴰ qᴰ
-- --         ∀ⱽPsh-introᴰ' .N-homᴰ =
-- --           Pⱽ.rectify $ Pⱽ.≡out $
-- --             (sym $ Pⱽ.reind-filler _)
-- --             ∙ αᴰ.N-obᴰ⟨
-- --                 change-base _ Q.isSetPsh
-- --                   -- TODO this ΣPathP can probably be simplified
-- --                   (ΣPathP (
-- --                     (Q.⟨ C.⋆IdL _ ⟩⋆⟨⟩
-- --                      ∙ (sym $ Q.⋆Assoc _ _ _)
-- --                      ∙ Q.⟨ sym bp.×β₁
-- --                            ∙ C.⟨ refl ⟩⋆⟨ sym $ C.⋆IdL _ ⟩ ⟩⋆⟨⟩
-- --                      ∙ (Q.⋆Assoc _ _ _)) ,
-- --                     sym bp.×β₂))
-- --                   (Qᴰ.⟨ Cᴰ.reind-filler _ ⟩⋆⟨⟩
-- --                   ∙ (sym $ Qᴰ.⋆Assoc _ _ _)
-- --                   ∙ Qᴰ.⟨ Cᴰ.reind-filler _ ∙ (sym $ βᴰ-πF* _) ⟩⋆⟨⟩
-- --                   ∙ Qᴰ.⋆Assoc _ _ _
-- --                   ∙ Qᴰ.reind-filler _)
-- --                ⟩
-- --             ∙ Pⱽ.≡in (αᴰ .N-homᴰ)
-- --             ∙ Pⱽ.⟨⟩⋆⟨ Pⱽ.reind-filler _ ⟩

-- --         ∀ⱽPsh-introᴰ : PshHomᴰ α Qᴰ ∀ⱽPsh
-- --         ∀ⱽPsh-introᴰ = reind-introᴰ ∀ⱽPsh-introᴰ'
