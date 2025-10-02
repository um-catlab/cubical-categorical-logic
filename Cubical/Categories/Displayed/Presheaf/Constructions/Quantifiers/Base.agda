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
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
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
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open NatTrans
open Functor
open Functorᴰ
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
