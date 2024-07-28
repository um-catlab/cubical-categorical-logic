{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open CartesianOver

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    {c : C .ob}{c' : C .ob}
    {dᴰ' : Dᴰ.ob[ F ⟅ c' ⟆ ]}{f : C [ c , c' ]}
    where
    reflectsCartesianOvers
      : CartesianOver Dᴰ dᴰ' (F ⟪ f ⟫)
      → CartesianOver F*Dᴰ dᴰ' f
    reflectsCartesianOvers f-lift .f*cᴰ' = f-lift .f*cᴰ'
    reflectsCartesianOvers f-lift .π = f-lift .π
    reflectsCartesianOvers f-lift .isCartesian {c''} dᴰ'' g gfᴰ = uniqueExists
      (⟨gfᴰ⟩' .fst .fst)
      ⟨gfᴰ⟩'-commutes
      (λ _ → F*Dᴰ.isSetHomᴰ _ _)
      ⟨gfᴰ⟩'-uniq
      where
        gfᴰ' : Dᴰ.Hom[ _ ][ dᴰ'' , dᴰ' ]
        gfᴰ' = R.reind (F .F-seq g f) gfᴰ

        ⟨gfᴰ⟩' = f-lift .isCartesian dᴰ'' (F ⟪ g ⟫) gfᴰ'

        ⟨gfᴰ⟩'-commutes : ⟨gfᴰ⟩' .fst .fst F*Dᴰ.⋆ᴰ f-lift .π ≡ gfᴰ
        ⟨gfᴰ⟩'-commutes = R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
          (R.reind-filler-sym (F .F-seq g f) _)
          (⟨gfᴰ⟩' .fst .snd))
          (symP (R.reind-filler (F .F-seq g f) gfᴰ)))

        ⟨gfᴰ⟩'-uniq
          : (gᴰ : F*Dᴰ.Hom[ g ][ dᴰ'' , f-lift .f*cᴰ' ])
          → (gᴰ F*Dᴰ.⋆ᴰ f-lift .π) ≡ gfᴰ
          → ⟨gfᴰ⟩' .fst .fst ≡ gᴰ
        ⟨gfᴰ⟩'-uniq gᴰ gᴰ-commutes = cong fst (⟨gfᴰ⟩' .snd (gᴰ ,
          (R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
            (R.reind-filler (sym (F .F-seq _ _)) _)
            gᴰ-commutes)
            (R.reind-filler (F .F-seq g f) gfᴰ)))))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  reindReflectsVerticalTerminal :
    ∀ c → VerticalTerminalAt Dᴰ (F ⟅ c ⟆)
    → VerticalTerminalAt (reindex Dᴰ F) c
  reindReflectsVerticalTerminal c 𝟙ᴰ .vertexᴰ = 𝟙ᴰ .vertexᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .elementᴰ = 𝟙ᴰ .elementᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .universalᴰ = 𝟙ᴰ .universalᴰ

  VerticalTerminalsReindex :
    VerticalTerminals Dᴰ
    → VerticalTerminals (reindex Dᴰ F)
  VerticalTerminalsReindex vta c =
    reindReflectsVerticalTerminal c (vta (F ⟅ c ⟆))

  module _ {termC : Terminal' C} where
    open Terminal'Notation termC
    LiftedTerminalReindex :
      VerticalTerminalAt Dᴰ (F ⟅ 𝟙 ⟆)
      → LiftedTerminal (reindex Dᴰ F) termC
    LiftedTerminalReindex 𝟙ᴰ =
      Vertical/𝟙→LiftedTerm _
        (reindReflectsVerticalTerminal (termC .vertex) 𝟙ᴰ)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} where
  -- do all the equational reasoning in the "reference space" Dᴰ
  open HomᴰReasoning Dᴰ
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Rᴰ = Categoryᴰ (reindex Dᴰ F)
  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (vbp : VerticalBinProductsAt Dᴰ (Fcᴰ , Fcᴰ')) where
    private
      module Fcᴰ∧Fcᴰ' = VerticalBinProductsAtNotation vbp
      reind-π₁ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ Fcᴰ∧Fcᴰ'.vert , Fcᴰ ]
      reind-π₁ = reind (sym (F .F-id)) Fcᴰ∧Fcᴰ'.π₁

      reind-π₂ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ Fcᴰ∧Fcᴰ'.vert , Fcᴰ' ]
      reind-π₂ = reind (sym (F .F-id)) Fcᴰ∧Fcᴰ'.π₂

    reindReflectsVerticalBinProd :
      VerticalBinProductsAt (reindex Dᴰ F) (Fcᴰ , Fcᴰ')
    reindReflectsVerticalBinProd .vertexᴰ = Fcᴰ∧Fcᴰ'.vert
    reindReflectsVerticalBinProd .elementᴰ = reind-π₁ , reind-π₂
    reindReflectsVerticalBinProd .universalᴰ
      {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof = λ cone → goal cone
      where
      goal : (cone : Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , Fcᴰ ] ×
              Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , Fcᴰ' ]) → _
      goal cone = uniqueExists l reind-l-β
        (λ _ _ _ → isSet× Dᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ _ _ _ _)
        (λ a' x₁ → congS fst
          (vbp .universalᴰ .equiv-proof reind-cone .snd (a' , subgoal a' x₁)))
        where
        p : F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
        p = F .F-seq _ _ ∙ congS (λ x₁ → F ⟪ f ⟫ ⋆⟨ D ⟩ x₁) (F .F-id)
        reind-cone : Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , Fcᴰ ] ×
          Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , Fcᴰ' ]
        reind-cone .fst = reind p (cone .fst)
        reind-cone .snd = reind p (cone .snd)
        l : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , vbp .vertexᴰ ]
        l = Fcᴰ∧Fcᴰ'.⟨ reind-cone .fst , reind-cone .snd ⟩
        l-β : (l Dᴰ.⋆ᴰ Fcᴰ∧Fcᴰ'.π₁ , l Dᴰ.⋆ᴰ Fcᴰ∧Fcᴰ'.π₂) ≡ reind-cone
        l-β = vbp .universalᴰ .equiv-proof reind-cone .fst .snd
        reind-l-β : (l Rᴰ.⋆ᴰ reind-π₁ , l Rᴰ.⋆ᴰ reind-π₂) ≡ cone
        reind-l-β = ≡-×
          (≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
            congP (λ _ x → l Dᴰ.⋆ᴰ x) (reind-filler-sym _ _) [ _ ]∙[ _ ]
            congS fst l-β [ _ ]∙[ _ ]
            reind-filler-sym _ _))
          (≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
            congP (λ _ x → l Dᴰ.⋆ᴰ x) (reind-filler-sym _ _) [ _ ]∙[ _ ]
            congS snd l-β [ _ ]∙[ _ ]
            reind-filler-sym _ _))
        subgoal : (l' : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , Fcᴰ∧Fcᴰ'.vert ]) →
          (x₁ : (l' Rᴰ.⋆ᴰ reind-π₁ , l' Rᴰ.⋆ᴰ reind-π₂) ≡ cone) →
          (l' Dᴰ.⋆ᴰ Fcᴰ∧Fcᴰ'.π₁ , l' Dᴰ.⋆ᴰ Fcᴰ∧Fcᴰ'.π₂) ≡ reind-cone
        subgoal l' x₁ = ≡-×
          (≡[]-rectify
            (congP (λ _ x → l' Dᴰ.⋆ᴰ x) (reind-filler _ _) [ _ ]∙[ _ ]
            reind-filler _ _ [ _ ]∙[ _ ]
            congS fst x₁ [ _ ]∙[ _ ]
            reind-filler _ _))
          (≡[]-rectify
            (congP (λ _ x → l' Dᴰ.⋆ᴰ x) (reind-filler _ _) [ _ ]∙[ _ ]
            reind-filler _ _ [ _ ]∙[ _ ]
            congS snd x₁ [ _ ]∙[ _ ]
            reind-filler _ _))

  VerticalBinProdsReindex : VerticalBinProducts Dᴰ →
    VerticalBinProducts (reindex Dᴰ F)
  VerticalBinProdsReindex vps Fcᴰ×Fcᴰ' =
    reindReflectsVerticalBinProd (vps Fcᴰ×Fcᴰ')

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  private module Dᴰ = Categoryᴰ Dᴰ
  module _ {c c' : C .ob} (prod : BinProduct' _ (c , c')) where
    private module c×c' = BinProduct'Notation prod
    module _
      {Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]}
      {Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]}
      (lift-π₁ : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫))
      (lift-π₂ : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫))
      (vbp : VerticalBinProductsAt Dᴰ (lift-π₁ .f*cᴰ' , lift-π₂ .f*cᴰ'))
      where
      LiftedBinProdReindex : LiftedBinProduct (reindex Dᴰ F) prod (Fcᴰ , Fc'ᴰ)
      LiftedBinProdReindex = VerticalBinProdsAt→LiftedBinProduct
        prod (reindex Dᴰ F)
        (reflectsCartesianOvers Dᴰ F lift-π₁)
        (reflectsCartesianOvers Dᴰ F lift-π₂)
        (reindReflectsVerticalBinProd vbp)

    module _ (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]) (fib : isFibration Dᴰ) where
      isFib→F⟪π₁⟫* : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫)
      isFib→F⟪π₁⟫* = CartesianLift→CartesianOver Dᴰ (fib _)
    module _ (Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) (fib : isFibration Dᴰ) where
      isFib→F⟪π₂⟫* : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫)
      isFib→F⟪π₂⟫* = CartesianLift→CartesianOver Dᴰ (fib _)

    module _
      {Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ]}
      {Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]}
      (lift-π₁ : CartesianOver Dᴰ Fcᴰ (F ⟪ c×c'.π₁ ⟫))
      (lift-π₂ : CartesianOver Dᴰ Fc'ᴰ (F ⟪ c×c'.π₂ ⟫))
      (vbps : VerticalBinProducts Dᴰ)
      where
      VerticalBinProds→ϕ[π₁x]∧ψ[π₂x] :
        VerticalBinProductsAt Dᴰ (lift-π₁ .f*cᴰ' , lift-π₂ .f*cᴰ')
      VerticalBinProds→ϕ[π₁x]∧ψ[π₂x] = vbps _

  module _
    (prods : BinProducts' C) where
    private module B = BinProducts'Notation prods
    module _
      (lift-π₁₂ : {c c' : C .ob}
        (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ])(Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) →
        CartesianOver Dᴰ Fcᴰ (F ⟪ B.π₁ {a = c} {b = c'} ⟫) ×
        CartesianOver Dᴰ Fc'ᴰ (F ⟪ B.π₂ {a = c} {b = c'} ⟫))
      (vbp : {c c' : C .ob} (Fcᴰ : Dᴰ.ob[ F ⟅ c ⟆ ])(Fc'ᴰ : Dᴰ.ob[ F ⟅ c' ⟆ ]) →
        VerticalBinProductsAt Dᴰ (lift-π₁₂ Fcᴰ Fc'ᴰ .fst .f*cᴰ' ,
          lift-π₁₂ Fcᴰ Fc'ᴰ .snd .f*cᴰ'))
      where
      LiftedBinProdsReindex : LiftedBinProducts (reindex Dᴰ F) prods
      LiftedBinProdsReindex (Fcᴰ , Fc'ᴰ) = LiftedBinProdReindex (prods _)
        (lift-π₁₂ Fcᴰ Fc'ᴰ .fst)
        (lift-π₁₂ Fcᴰ Fc'ᴰ .snd)
        (vbp Fcᴰ Fc'ᴰ)

  module _ (prods : BinProducts' C)
    (fib : isFibration Dᴰ)
    (vbps : VerticalBinProducts Dᴰ) where
    LiftedBinProdsReindex' : LiftedBinProducts (reindex Dᴰ F) prods
    LiftedBinProdsReindex' = LiftedBinProdsReindex prods
      (λ Fcᴰ Fc'ᴰ →
        isFib→F⟪π₁⟫* (prods _) Fcᴰ fib , isFib→F⟪π₂⟫* (prods _) Fc'ᴰ fib)
      (λ Fcᴰ Fc'ᴰ → VerticalBinProds→ϕ[π₁x]∧ψ[π₂x]
        (prods _)
        (isFib→F⟪π₁⟫* (prods _) Fcᴰ fib)
        (isFib→F⟪π₂⟫* (prods _) Fc'ᴰ fib)
        vbps)
