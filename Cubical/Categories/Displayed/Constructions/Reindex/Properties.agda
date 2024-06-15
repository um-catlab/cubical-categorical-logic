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
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Displayed.Instances.Sets.Base
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.Constructions.BinProduct.More
  open import Cubical.Categories.Adjoint.UniversalElements
  open import Cubical.Categories.Instances.Sets
  open Functorᴰ
  open HomᴰReasoning Dᴰ
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Rᴰ = Categoryᴰ (reindex Dᴰ F)
  module _ {c} cᴰ cᴰ' (vbp : VerticalBinProductsAt Dᴰ {c = F ⟅ c ⟆} (cᴰ , cᴰ')) where
    private module Bᴰ = VerticalBinProductsAtNotation vbp
    _ : Dᴰ.Hom[ id D ][ vbp .vertexᴰ , cᴰ ] × Dᴰ.Hom[ id D ][ vbp .vertexᴰ , cᴰ' ]
    _ = Bᴰ.vert-π₁₂
    reind-π₁₂ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ vbp .vertexᴰ , cᴰ ] × Dᴰ.Hom[ F ⟪ C .id ⟫ ][ vbp .vertexᴰ , cᴰ' ]
    reind-π₁₂ .fst = (transport (congS (λ x → Dᴰ.Hom[ x ][ vbp .vertexᴰ , cᴰ ]) (sym (F .F-id))) Bᴰ.vert-π₁)
    reind-π₁₂ .snd = (transport (congS (λ x → Dᴰ.Hom[ x ][ vbp .vertexᴰ , cᴰ' ]) (sym (F .F-id))) Bᴰ.vert-π₂ )
    cohere-π₁ : Bᴰ.vert-π₁ Dᴰ.≡[ sym (F .F-id) ] reind-π₁₂ .fst
    cohere-π₁ = toPathP refl
    cohere-π₂ : Bᴰ.vert-π₂ Dᴰ.≡[ sym (F .F-id) ] reind-π₁₂ .snd
    cohere-π₂ = toPathP refl
    --π₁ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ vbp .vertexᴰ , cᴰ ]
    --π₁ = transport (congS (λ x → Dᴰ.Hom[ x ][ vbp .vertexᴰ , cᴰ ]) (sym (F .F-id))) (vbp .elementᴰ .fst)
    --π₂ : Dᴰ.Hom[ F ⟪ C .id ⟫ ][ vbp .vertexᴰ , cᴰ' ]
    --π₂ = transport (congS (λ x → Dᴰ.Hom[ x ][ vbp .vertexᴰ , cᴰ' ]) (sym (F .F-id))) (vbp .elementᴰ .snd)
    reindReflectsVerticalBinProd : VerticalBinProductsAt (reindex Dᴰ F) {c = c} (cᴰ , cᴰ')
    reindReflectsVerticalBinProd .vertexᴰ = vbp .vertexᴰ
    reindReflectsVerticalBinProd .elementᴰ = reind-π₁₂
    reindReflectsVerticalBinProd .universalᴰ {x = x} {xᴰ = xᴰ} {f = f} .equiv-proof =
      λ cone → goal cone
      where
      goal : (cone : Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , cᴰ ] ×
              Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , cᴰ' ]) → _
      goal cone = uniqueExists l subgoal {!!} {!!}
        where
        --_ : Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , cᴰ ] ×
        --      Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ][ xᴰ , cᴰ' ]
        --_ = cone
        p : F ⟪ f ⋆⟨ C ⟩ C .id ⟫ ≡ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
        p = F .F-seq _ _ ∙ congS (λ x₁ → F ⟪ f ⟫ ⋆⟨ D ⟩ x₁) (F .F-id)
        --q' : Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , cᴰ ] ×
        --  Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , cᴰ' ]
        --q' = transport
        --  (congS (λ x₁ → Dᴰ.Hom[ x₁ ][ xᴰ , cᴰ ] × Dᴰ.Hom[ x₁ ][ xᴰ , cᴰ' ]) p)
        --  cone
        q : Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , cᴰ ] ×
          Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ D .id ][ xᴰ , cᴰ' ]
        q .fst = transport
          (congS (λ x₁ → Dᴰ.Hom[ x₁ ][ xᴰ , cᴰ ]) p) (cone .fst)
        q .snd = transport
          (congS (λ x₁ → Dᴰ.Hom[ x₁ ][ xᴰ , cᴰ' ]) p) (cone .snd)
        ok :  cone .fst Dᴰ.≡[ p ] q .fst
        ok = toPathP refl
        ok' :  cone .snd Dᴰ.≡[ p ] q .snd
        ok' = toPathP refl
        ok'' : PathP (λ i → Dᴰ.Hom[ p i ][ xᴰ , cᴰ ] × Dᴰ.Hom[ p i ][ xᴰ , cᴰ' ]) cone q
        ok'' = ΣPathP (ok , ok')
        l : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , vbp .vertexᴰ ]
        l = vbp .universalᴰ .equiv-proof q .fst .fst
        Dᴰ→Rᴰ₁ : l Dᴰ.⋆ᴰ reind-π₁₂ .fst Dᴰ.≡[ _ ] l Rᴰ.⋆ᴰ reind-π₁₂ .fst
        Dᴰ→Rᴰ₁ = toPathP refl
        Dᴰ→Rᴰ₂ : l Dᴰ.⋆ᴰ reind-π₁₂ .snd Dᴰ.≡[ _ ] l Rᴰ.⋆ᴰ reind-π₁₂ .snd
        Dᴰ→Rᴰ₂ = toPathP refl
        bz : UniversalElement D ((D [-, (F ⟅ c ⟆ ) ]) ∘F (Id ^opF))
        bz = IdRightAdj' D (F ⟅ c ⟆)
        l-comm : (l Dᴰ.⋆ᴰ Bᴰ.vert-π₁ , l Dᴰ.⋆ᴰ Bᴰ.vert-π₂) ≡ q
        l-comm = vbp .universalᴰ .equiv-proof q .fst .snd
        bleh : l Dᴰ.⋆ᴰ Bᴰ.vert-π₁ ≡ q .fst
        bleh = congS (λ x → x .fst) l-comm
        huh : Dᴰ.Hom[ F ⟪ f ⋆⟨ C ⟩ (C .id) ⟫ ][ xᴰ , cᴰ ]
        huh = l Rᴰ.⋆ᴰ (reind-π₁₂ .fst)
        huh'' : Dᴰ.Hom[ F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ C .id ⟫ ][ xᴰ , cᴰ ]
        huh'' = l Dᴰ.⋆ᴰ reind-π₁₂ .fst
        uhoh : l Dᴰ.⋆ᴰ reind-π₁₂ .fst Dᴰ.≡[ _ ] l Dᴰ.⋆ᴰ Bᴰ.vert-π₁
        uhoh = congP (λ _ x → l Dᴰ.⋆ᴰ x ) (symP cohere-π₁)
        zoo : vbp .universalᴰ .equiv-proof q .fst ≡ (l , l-comm)
        zoo = vbp .universalᴰ .equiv-proof q .snd (l , l-comm)
        subgoal : (l Rᴰ.⋆ᴰ (reind-π₁₂ .fst) ,
                l Rᴰ.⋆ᴰ (reind-π₁₂ .snd))
                ≡ cone
        subgoal = ≡-×
          (≡[]-rectify (symP Dᴰ→Rᴰ₁ [ _ ]∙[ _ ] uhoh [ _ ]∙[ _ ] bleh [ _ ]∙[ _ ] symP ok ))
          {!!}
        --yyy : Functor (C ^op) (SET ℓC')
        --yyy = (C [-, c ]) ∘F (Id ^opF)
        --zzz : Functorᴰ yyy (reindex Dᴰ F ^opᴰ) (SETᴰ ℓC' ℓDᴰ')
        --zzz = ((reindex Dᴰ F ×ᴰ reindex Dᴰ F) [-][-, cᴰ , cᴰ' ]) ∘Fᴰ (Δᴰ (reindex Dᴰ F) ^opFᴰ)
        ----zzz' : SETᴰ ℓC' ℓDᴰ' [ yyy .F-hom f ][ zzz .F-obᴰ (vbp .vertexᴰ) , zzz .F-obᴰ xᴰ ]
        ----zzz' = zzz .F-homᴰ l
        ----a2 : q .fst Dᴰ.≡[ congS (λ x → seq' D (F ⟪ f ⟫) x) (sym (F .F-id)) ∙ sym (F .F-seq _ _) ] cone .fst
        ----a2 = {!!}
        ----a1 : (l Dᴰ.⋆ᴰ π₁) Dᴰ.≡[ sym (F .F-seq _ _) ] cone .fst
        ----a1 = {!!}
        --subgoal : (zzz .F-homᴰ l (C .id) reind-π₁₂) .fst ≡ cone .fst
        --subgoal = {!!} --≡[]-rectify {!!}
