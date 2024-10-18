{-

  reindexing The Iso category over a monoidal category along strong
  monoidal functors gives a displayed monoidal category. This can
  probably be generalized, but it would require isofibrations and so
  this direct argument is a little simpler e.g., because everything
  hasPropHoms.

  TODO: shouldn't this be about IsoComma? should IsoComma just be
  defined as reindex of Iso?

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Arrow.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.Monoidal
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
import Cubical.Categories.Displayed.Instances.Arrow.Base as Arrow

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open MonoidalCategoryᴰ
open TensorStrᴰ
open MonoidalStrᴰ
open NatTrans
open NatIso
open Functor

module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M
  Iso : MonoidalCategoryᴰ (M ×M M) ℓC' ℓC'
  Iso .Cᴰ = Arrow.Iso M.C
  Iso .monstrᴰ = TensorPropᴰ→TensorStrᴰ (M ×M M) (Iso .Cᴰ)
    hasPropHomsCᴰ
    MP
    where
      hasPropHomsCᴰ = (Arrow.hasPropHomsIso M.C)
      open MonoidalPropᴰ
      MP : MonoidalPropᴰ (M ×M M) (Arrow.Iso M.C)
      MP .tenstrᴰ .unitᴰ = idCatIso
      MP .tenstrᴰ .─⊗ᴰ─ = mkPropHomsFunctor hasPropHomsCᴰ
        (λ { (x≅x' , y≅y') → F-Iso {F = M.─⊗─} (CatIso× M.C M.C x≅x' y≅y') })
        λ { ((f-sq , _) , (g-sq , _)) →
          sym (M.─⊗─ .F-seq _ _ )
          ∙ cong₂ M._⊗ₕ_ f-sq g-sq
          ∙ M.─⊗─ .F-seq _ _ 
          , _
          }
      MP .MonoidalPropᴰ.αᴰ⟨_,_,_⟩ x≅x' y≅y' z≅z' =
        sym (M.α .trans .N-hom _) , _
      MP .α⁻¹ᴰ⟨_,_,_⟩ _ _ _ =
        sym (symNatIso M.α .trans .N-hom _) , _ 
      MP .MonoidalPropᴰ.ηᴰ⟨_⟩ x≅x' =
        sym (M.η .trans .N-hom _)
        , _
      MP .η⁻¹ᴰ⟨_⟩ x≅x' =
        sym (symNatIso M.η .trans .N-hom _)
        , _
      MP .MonoidalPropᴰ.ρᴰ⟨_⟩ _ = sym (M.ρ .trans .N-hom _) , _
      MP .ρ⁻¹ᴰ⟨_⟩ _ = sym (symNatIso M.ρ .trans .N-hom _) , _

-- module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
--          (G : OpLaxMonoidalFunctor M N)(H : LaxMonoidalFunctor M N) where
--   private
--     module M = MonoidalCategory M
--     module N = MonoidalCategory N
--     module G = OpLaxMonoidalFunctor G
--     module H = LaxMonoidalFunctor H

-- module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
--          (G H : StrongMonoidalFunctor M N)
--   where
--   private
--     module M = MonoidalCategory M
--     module N = MonoidalCategory N
--     module G = StrongMonoidalFunctor G
--     module H = StrongMonoidalFunctor H

--     |G≅H| : Categoryᴰ M.C ℓD' ℓD'
--     |G≅H| = reindex (Arrow.Iso N.C) (G.F ,F H.F)
--     hasPropHomsG≅H : hasPropHoms |G≅H|
--     hasPropHomsG≅H = (hasPropHomsReindex (Arrow.Iso N.C) (G.F ,F H.F) (Arrow.hasPropHomsIso N.C))

--   IsoComma : MonoidalCategoryᴰ M ℓD' ℓD'
--   IsoComma .Cᴰ = |G≅H|
--   IsoComma .monstrᴰ = TensorPropᴰ→TensorStrᴰ M |G≅H|
--     hasPropHomsG≅H
--     MP
--     where
--       open MonoidalPropᴰ
--       opaque
--         MP : MonoidalPropᴰ M |G≅H|
--         MP .tenstrᴰ .unitᴰ = ⋆Iso (invIso G.ε-Iso) H.ε-Iso
--         MP .tenstrᴰ .─⊗ᴰ─ = mkPropHomsFunctor hasPropHomsG≅H
--           (λ { {x , y} (Gx≅Hx , Gy≅Hy) →
--             -- 
--             ⋆Iso (invIso (NatIsoAt (G.μ-Iso) _))
--             (⋆Iso (F-Iso {F = N.─⊗─} (CatIso× N.C N.C Gx≅Hx Gy≅Hy))
--             (NatIsoAt (H.μ-Iso) _)) })
--           λ { {x , x'} {y , y'} {f , g} {Gx≅Hx , Gx'≅Hx'} {Gy≅Hy , Gy'≅Hy'}
--               ((f-sq , _) , (g-sq , _))
--             → sym (N.⋆Assoc _ _ _)
--             ∙ cong₂ N._⋆_ (symNatIso G.μ-Iso .trans .N-hom _) refl
--             ∙ N.⋆Assoc _ _ _  
--             ∙ cong₂ N._⋆_ refl
--               (sym (N.⋆Assoc _ _ _)
--               ∙ cong₂ N._⋆_
--                 (sym (N.─⊗─ .F-seq _ _)
--                 ∙ cong₂ N._⊗ₕ_ f-sq g-sq
--                 ∙ (N.─⊗─ .F-seq _ _) )
--                   refl
--               ∙ N.⋆Assoc _ _ _)
--             ∙ cong₂ N._⋆_ refl (cong₂ N._⋆_ refl (H.μ-Iso .trans .N-hom _))
--             ∙ sym (N.⋆Assoc _ _ _) ∙ sym (N.⋆Assoc _ _ _)
--             ∙ cong₂ N._⋆_ (N.⋆Assoc _ _ _) refl  
--               , _
--             }
--         MP .MonoidalPropᴰ.αᴰ⟨_,_,_⟩ Gx≅Hx Gy≅Hy Gz≅Hz .fst =
--           {!!}
--         MP .MonoidalPropᴰ.αᴰ⟨_,_,_⟩ Gx≅Hx Gy≅Hy Gz≅Hz .snd = _
--         MP .α⁻¹ᴰ⟨_,_,_⟩ = {!!}
--         MP .MonoidalPropᴰ.ηᴰ⟨_⟩ {x} Gx≅Hx .fst =
--           {!G.η-law x!}
--           ∙ cong₂ N._⋆_ refl (cong₂ N._⋆_ refl ({!!} ∙ sym (H.ηε-law x) ∙ N.⋆Assoc _ _ _))
--           ∙ cong₂ N._⋆_ refl
--             ( sym (N.⋆Assoc _ _ _)
--             ∙ cong₂ N._⋆_ ( sym (N.─⊗─ .F-seq _ _) ∙ cong₂ N._⊗ₕ_ refl (N.⋆IdR _)) refl
--             ∙ sym (N.⋆Assoc _ _ _))
--           ∙ sym (N.⋆Assoc _ _ _)
--         MP .MonoidalPropᴰ.ηᴰ⟨_⟩ Gx≅Hx .snd = _
--         MP .η⁻¹ᴰ⟨_⟩ {x} Gx≅Hx .fst = {!!}
--         MP .η⁻¹ᴰ⟨_⟩ {x} Gx≅Hx .snd = _
--         MP .MonoidalPropᴰ.ρᴰ⟨_⟩ = {!!}
--         MP .ρ⁻¹ᴰ⟨_⟩ = {!!}
