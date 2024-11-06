{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.Cartesian.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS : Level

--open Category

---- this has to be somewhere
--module _ (C : Category ℓC ℓC') where
--  private module C = Category C
--  open isIso
--  module _ {c c' c'' : C.ob} where
--    -- this is not super useful?
--    CatIso-Post : CatIso C c c' → Iso (C [ c'' , c ]) (C [ c'' , c' ])
--    CatIso-Post f = iso
--      (C._⋆ f .fst)
--      (C._⋆ f .snd .inv)
--      (λ g → C.⋆Assoc _ _ _ ∙ congS (g C.⋆_) (f .snd .sec) ∙ C.⋆IdR _)
--      (λ g → C.⋆Assoc _ _ _ ∙ congS (g C.⋆_) (f .snd .ret) ∙ C.⋆IdR _)
---- general facts about UniversalElements
--module _ (C : Category ℓC ℓC') (P : Presheaf C ℓS) where
--  open UniversalElement
--  module _ (ue ue' : UniversalElement C P) where
--    private
--      f : Σ[ f ∈ C [ ue .vertex , ue' .vertex ] ] (ue' .element) ∘ᴾ⟨ C , P ⟩ f ≡ ue .element
--      f = ue' .universal (ue .vertex) .equiv-proof (ue .element) .fst
--      f⁻¹ : Σ[ f⁻¹ ∈ C [ ue' .vertex , ue .vertex ] ] (ue .element) ∘ᴾ⟨ C , P ⟩ f⁻¹ ≡ ue' .element
--      f⁻¹ = ue .universal (ue' .vertex) .equiv-proof (ue' .element) .fst
--      ue'-self : Σ[ u ∈ C [ ue' .vertex , ue' .vertex ] ] (ue' .element) ∘ᴾ⟨ C , P ⟩ u ≡ ue' .element
--      ue'-self = ue' .universal (ue' .vertex) .equiv-proof (ue' .element) .fst
--      ue'-self-contr : ∀ y → ue'-self ≡ y
--      ue'-self-contr = ue' .universal (ue' .vertex) .equiv-proof (ue' .element) .snd
--      p : ue'-self .fst ≡ Category.id C
--      p = congS fst
--        (ue'-self-contr (C .Category.id , funExt⁻ (P .Functor.F-id) _))
--      ff⁻¹-fiber : (ue' .element) ∘ᴾ⟨ C , P ⟩ (f .fst ∘⟨ C ⟩ f⁻¹ .fst) ≡ ue' .element
--      ff⁻¹-fiber = congS (λ g → g (ue' .element)) (P .Functor.F-seq (f .fst) (f⁻¹ .fst)) ∙
--        congS (P ⟪ f⁻¹ .fst ⟫) (f .snd) ∙
--        f⁻¹ .snd
--      q : ue'-self .fst ≡ f .fst ∘⟨ C ⟩ f⁻¹ .fst
--      q = congS fst
--        (ue'-self-contr (f .fst ∘⟨ C ⟩ f⁻¹ .fst , ff⁻¹-fiber))
--      -- totally symmetric
--      ue-self : Σ[ u ∈ C [ ue .vertex , ue .vertex ] ] ue .element ∘ᴾ⟨ C , P ⟩ u ≡ ue .element
--      ue-self = ue .universal (ue .vertex) .equiv-proof (ue .element) .fst
--      ue-self-contr : ∀ y → ue-self ≡ y
--      ue-self-contr = ue .universal (ue .vertex) .equiv-proof (ue .element) .snd
--      p' : ue-self .fst ≡ Category.id C
--      p' = congS fst
--        (ue-self-contr (C .Category.id , funExt⁻ (P .Functor.F-id) _))
--      f⁻¹f-fiber : (ue .element) ∘ᴾ⟨ C , P ⟩ (f⁻¹ .fst ∘⟨ C ⟩ f .fst) ≡ ue .element
--      f⁻¹f-fiber = congS (λ g → g (ue .element)) (P .Functor.F-seq (f⁻¹ .fst) (f .fst)) ∙
--        congS (P ⟪ f .fst ⟫) (f⁻¹ .snd) ∙
--        f .snd
--      q' : ue-self .fst ≡ f⁻¹ .fst ∘⟨ C ⟩ f .fst
--      q' = congS fst
--        (ue-self-contr (f⁻¹ .fst ∘⟨ C ⟩ f .fst , f⁻¹f-fiber))
--    ue-iso : CatIso C (ue .vertex) (ue' .vertex)
--    ue-iso = catiso (f .fst) (f⁻¹ .fst) (sym q ∙ p) (sym q' ∙ p')
--    ue-iso-triangle : ue' .element ∘ᴾ⟨ C , P ⟩ (ue-iso .fst) ≡ ue .element
--    ue-iso-triangle = f .snd

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
    open Functor
    record CartesianFunctor : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      field
        |F| : Functor (C .fst) (D .fst)
        PreservesProducts : ∀ c c' → preservesRepresentation
          |F|
          (BinProductProf _ ⟅ c , c' ⟆)
          (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆)
          (natTrans
            (λ _ (lift (g₁ , g₂)) → lift (|F| ⟪ g₁ ⟫ , |F| ⟪ g₂ ⟫))
            (λ f → funExt (λ (lift (g₁ , g₂)) → congS lift (≡-× (|F| .F-seq _ _) (|F| .F-seq _ _)))))
          (BinProductToRepresentable _ (C .snd .snd _ _))
        PreservesTerminal : preservesTerminal _ _ |F|
--  record CartesianFunctor : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
--    field
--      |F| : Functor (C .fst) (D .fst)
--      PreservesProducts : (c c' : C.ob) → isUniversal (D .fst)
--        (BinProductProf _ ⟅ |F| ⟅ c ⟆ , |F| ⟅ c' ⟆ ⟆) --(PshProd {C = D .fst} ⟅ YO ⟅ |F| ⟅ c ⟆ ⟆ , YO ⟅ |F| ⟅ c' ⟆ ⟆ ⟆b)
--        _ (|F| ⟪ C.π₁ ⟫ , |F| ⟪ C.π₂ ⟫)
--      PreservesTerminal : preservesTerminal _ _ |F|
--  --record CartesianFunctor' : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
--  --  field
--  --    |F| : Functor (C .fst) (D .fst)
--  --    PreservesProducts : {c c' c×c' : C.ob} (π₁ : C .fst [ c×c' , c ])(π₂ : C .fst [ c×c' , c' ]) →
--  --      isUniversal (C .fst)
--  --      (PshProd {C = C .fst} ⟅ YO ⟅ c ⟆ , YO ⟅ c' ⟆ ⟆b)
--  --      c×c' (π₁ , π₂) →
--  --      isUniversal (D .fst)
--  --      (PshProd {C = D .fst} ⟅ YO ⟅ |F| ⟅ c ⟆ ⟆ , YO ⟅ |F| ⟅ c' ⟆ ⟆ ⟆b)
--  --      _ (|F| ⟪ C.π₁ ⟫ , |F| ⟪ C.π₂ ⟫)
--  --    PreservesTerminal : preservesTerminal _ _ |F|
--  module _ (F : Functor (C .fst) (D .fst)) where
--    open UniversalElement
--    open Iso
--    open Functor
--    module _ {c c' : C.ob} (thm : isUniversal (D .fst)
--      (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆) --(PshProd {C = D .fst} ⟅ YO ⟅ F ⟅ c ⟆ ⟆ , YO ⟅ F ⟅ c' ⟆ ⟆ ⟆b)
--      _ (F ⟪ C.π₁ ⟫ , F ⟪ C.π₂ ⟫))
--      where
--      module _
--        (arb : UniversalElement (C .fst) (BinProductProf _ ⟅ c , c' ⟆)) --(PshProd {C = C .fst} ⟅ YO ⟅ c ⟆ , YO ⟅ c' ⟆ ⟆b)
--        where
--        test : isUniversal (D .fst)
--          (BinProductProf _ ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆) --(PshProd {C = D .fst} ⟅ YO ⟅ F ⟅ c ⟆ ⟆ , YO ⟅ F ⟅ c' ⟆ ⟆ ⟆b)
--          _ (F ⟪ arb .element .fst ⟫ , F ⟪ arb .element .snd ⟫)
--        test d .equiv-proof (f , g) = uniqueExists
--          (CatIso-Post (D .fst) (preserveIsosF {F = F} ii) .fun save)
--          (ΣPathP ({!!} , {!!}))
--          {!!}
--          {!!}
--          where
--          ii : CatIso _ (c C.×bp c') (arb .vertex)
--          ii = ue-iso _ (BinProductProf (C .fst) ⟅ c , c' ⟆) --(PshProd ⟅ YO ⟅ c ⟆ , YO ⟅ c' ⟆ ⟆b)
--            (BinProductToRepresentable _ (C .snd .snd _ _)) arb
--          _ : CatIso _ (F ⟅ c C.×bp c' ⟆) (F ⟅ arb .vertex ⟆)
--          _ = preserveIsosF {F = F} ii
--          p : (ii .fst ⋆⟨ C .fst ⟩ arb .element .fst , ii .fst ⋆⟨ C .fst ⟩ arb .element .snd) ≡ (C.π₁ , C.π₂)
--          p = ue-iso-triangle _ (BinProductProf (C .fst) ⟅ c , c' ⟆) (BinProductToRepresentable _ (C .snd .snd _ _)) arb
--          q : F ⟪ ii .fst ⟫ ⋆⟨ D .fst ⟩ F ⟪ arb .element .fst ⟫ ≡ F ⟪ C.π₁ ⟫
--          q = F-triangle F (congS fst p)
--          q' : F ⟪ ii .fst ⟫ ⋆⟨ D .fst ⟩ F ⟪ arb .element .snd ⟫ ≡ F ⟪ C.π₂ ⟫
--          q' = F-triangle F (congS snd p)
--          save : D .fst [ d , F ⟅ c C.×bp c' ⟆ ]
--          save = thm d .equiv-proof (f , g) .fst .fst


--module _ {C : CartesianCategory ℓC ℓC'}
--         {D : CartesianCategory ℓD ℓD'}
--         {E : CartesianCategory ℓE ℓE'}
--         (G : CartesianFunctor' D E)
--         (F : CartesianFunctor' C D)
--  where
--  private
--    module G = CartesianFunctor' G
--    module F = CartesianFunctor' F
--  open CartesianFunctor'
--  _∘×F_ : CartesianFunctor' C E
--  _∘×F_ .|F| = G.|F| ∘F F.|F|
--  _∘×F_ .PreservesProducts π₁ π₂ p e .equiv-proof (f , g) = uniqueExists {!G .PreservesProducts!} {!!} {!!} {!!}
--  _∘×F_ .PreservesTerminal = {!!}
