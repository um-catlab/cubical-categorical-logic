{-

  The slice category over a displayed category. Used in the definition
  of a fibration.

-}

module Cubical.Categories.Displayed.Instances.Slice where

open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base as Disp
open import Cubical.Categories.Displayed.Instances.BinProduct.More as BPᴰ
  hiding (introF)
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor

-- Do we actually need this?
-- module _ (C : Category ℓC ℓC') (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
--   private module Slice = EqReindex Cᴰ {!!} {!!} {!!} -- Eq.refl (λ _ _ → Eq.refl)
--   -- See test below for the intuitive definition
--   _/C_ : Categoryᴰ C _ _
--   _/C_ = ∫Cᴰ (weaken C C) ({!!} ×ᴰ {!!}) -- (Cᴰ' ×ᴰ Arrow C)
--     where Cᴰ' = Slice.reindex

--   module _ {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--     {F : Functor D C}
--     (Fᴰ₁ : Functor D C)
--     (Fᴰ₂ : Functorᴰ Fᴰ₁ Dᴰ Cᴰ)
--     (Fᴰ₃ : F ⇒ Fᴰ₁)
--     where
--     -- NOTE: this is not the most general introduction rule possible.
--     -- A more general version would allow Fᴰ₁ to depend on Dᴰ as well.
--     introF : Functorᴰ F Dᴰ _/C_
--     introF = TotalCatᴰ.introF _ _ (Wk.introF F Fᴰ₁)
--       (BPᴰ.introS _
--         (Slice.introS _ (reindS' (Eq.refl , Eq.refl) (TotalCat.elim Fᴰ₂)))
--         (reindS' (Eq.refl , Eq.refl)
--           (compSectionFunctor (arrIntroS {F1 = F} {F2 = Fᴰ₁} Fᴰ₃)
--             (TotalCat.Fst {Cᴰ = Dᴰ}))))

--   private
--     open Category
--     open Categoryᴰ
--     test : ∀ {c} → _/C_ .ob[_] c ≡ (Σ[ c' ∈ C .ob ] Cᴰ .ob[_] c' × C [ c , c' ])
--     test = refl

--   Δ/C : Functorᴰ Id Cᴰ _/C_
--   Δ/C = introF Id 𝟙ᴰ⟨ Cᴰ ⟩ (idTrans Id)

--   private
--     open Functorᴰ
--     _ : ∀ c (cᴰ : Cᴰ .ob[_] c) → Δ/C .F-obᴰ cᴰ ≡ (c , (cᴰ , C .id))
--     _ = λ c cᴰ → refl

-- -- module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
-- --   {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
-- --   {F : Functor C D}
-- --   (Fᴰ₁ : Functor C D)
-- --   where
-- --   introF : Functorᴰ F Cᴰ (D /C Dᴰ)
-- --   introF = TotalCatᴰ.introF _ _ (Wk.introF F Fᴰ₁) {!Slice.introS!}

-- module _ (C : Category ℓC ℓC') where
--   -- Slices .ob[ c ] = Σ[ c' ∈ C .ob] C [ c' , c ]
--   Slices : Categoryᴰ C (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
--   Slices = ∫Cᴰ (weaken C C) (Arrow C)

--   private
--     open Category
--     open Categoryᴰ
--     test : ∀ {c} → Slices .ob[_] c ≡ (Σ[ c' ∈ C .ob ] C [ c , c' ])
--     test = refl

--   Subobjects : Categoryᴰ C _ _
--   Subobjects = ∫Cᴰ (weaken C C) (Mono C)
--   private
--     open Category
--     open Categoryᴰ
--     test' : ∀ {c} → Subobjects .ob[_] c
--       ≡ (Σ[ c' ∈ C .ob ] Σ[ f ∈ C [ c , c' ] ] isMonic C f)
--     test' = refl
