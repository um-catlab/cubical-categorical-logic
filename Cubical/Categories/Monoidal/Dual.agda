{- The dual monoidal category, I.e. x ⊗^co y = y ⊗ x -}

module Cubical.Categories.Monoidal.Dual where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Constructions.BinProduct as BP

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open NatTrans
open NatIso
open isIso
module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M
  open TensorStr
  open MonoidalStr
  open MonoidalCategory
  _^co : MonoidalCategory ℓC ℓC'
  _^co .C = M.C
  _^co .monstr .tenstr .─⊗─ = M.─⊗─ ∘F Sym {C = M.C} {D = M.C}
  _^co .monstr .tenstr .unit = M.unit
  _^co .monstr .α .trans .N-ob x = M.α⁻¹⟨ _ , _ , _ ⟩
  _^co .monstr .α .trans .N-hom _ = symNatIso M.α .trans .N-hom _
  _^co .monstr .α .nIso x .inv = M.α⟨ _ , _ , _ ⟩
  _^co .monstr .α .nIso x .sec = M.α .nIso _ .ret
  _^co .monstr .α .nIso x .ret = M.α .nIso _ .sec
  _^co .monstr .η .trans .N-ob = M.ρ .trans .N-ob
  _^co .monstr .η .trans .N-hom = M.ρ .trans .N-hom
  _^co .monstr .η .nIso = M.ρ .nIso
  _^co .monstr .ρ .trans .N-ob = M.η .trans .N-ob
  _^co .monstr .ρ .trans .N-hom = M.η .trans .N-hom
  _^co .monstr .ρ .nIso = M.η .nIso
  _^co .monstr .pentagon w x y z =
    ⋆CancelL (⋆Iso (NatIsoAt M.α _) (NatIsoAt M.α _))
      (cong₂ M._⋆_ (sym (M.pentagon z y x w)) refl
      ∙ (cong₂ M._⋆_ refl (sym (M.⋆Assoc _ _ _)) ∙ lhsIso .snd .ret)
      ∙ sym (⋆Iso (NatIsoAt M.α _) (NatIsoAt M.α _) .snd .ret))
    where
      lhsIso =
        ⋆Iso
          (F-Iso {F = M.─⊗─} (CatIso× M.C M.C
            idCatIso
            (NatIsoAt M.α (y , x , w))))
          (⋆Iso (NatIsoAt M.α (z , (y M.⊗ x) , w))
            (F-Iso {F = M.─⊗─}
              (CatIso× M.C M.C
                (NatIsoAt M.α (z , y , x))
                idCatIso)))
  _^co .monstr .triangle x y =
    sym (⋆InvLMove (NatIsoAt M.α _) (M.triangle _ _))
