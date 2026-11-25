{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Sets

module _ (ℓ : Level) where
  SetCBPVCod : CBPVCatᴰ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
  SetCBPVCod = reindexChosenReind (SETCod ℓ) (weakenΠ KIND (SET ℓ))

  SetCBPVCodReind : ChosenReind SetCBPVCod
  SetCBPVCodReind = reindexReind (SETCod ℓ) (weakenΠ KIND (SET ℓ))

  private
    SETCodCCⱽ^op : CartesianCategoryⱽ (SET ℓ ^op) (ℓ-suc ℓ) ℓ
    SETCodCCⱽ^op = cartesiancategoryⱽ (SETCod ℓ ^opᴰ) InitialsⱽSETCod
      BinCoProductsⱽSETCod isOpfibrationSETCod

    module Cart = CartesianCategoryⱽ
      (CartesianCategoryⱽReindexChosenReind SETCodCCⱽ (weakenΠ KIND (SET ℓ)))
    module OpCart = CartesianCategoryⱽ
      (CartesianCategoryⱽReindexChosenReind SETCodCCⱽ^op (SetCBPVΠTotal^op ℓ))

  SetCBPVCod-Uⱽ : hasUⱽ SetCBPVCod
  SetCBPVCod-Uⱽ f Bᴰ =
    reindexCartesianLiftChosenReind (SETCod ℓ) (weakenΠ KIND (SET ℓ)) (_ , f) Bᴰ
      (isFibrationSETCod Bᴰ _ f)

  SetCBPVCod-Fⱽ : hasFⱽ SetCBPVCod
  SetCBPVCod-Fⱽ f Aᴰ =
    f*Aᴰ .fst ,
    pshiso
      (pshhom
        (λ x → f*Aᴰ .snd .PshIso.trans .PshHom.N-ob x)
        (λ c c' g p → f*Aᴰ .snd .PshIso.trans .PshHom.N-hom c c' g p))
      (f*Aᴰ .snd .PshIso.nIso)
    where
    f*Aᴰ = reindexCartesianLiftChosenReind (SETCod ℓ ^opᴰ) (SetCBPVΠ^op ℓ) (_ , f)
      Aᴰ
      (isOpfibrationSETCod Aᴰ _ f)

  SetCBPVCodⱽ : MultCBPVCatⱽ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
  SetCBPVCodⱽ .fst = SetCBPVCod
  SetCBPVCodⱽ .snd .fst = SetCBPVCod-Uⱽ
  SetCBPVCodⱽ .snd .snd = SetCBPVCod-Fⱽ

  SetCBPVCod-Initialsⱽ : ValueInitialsⱽ SetCBPVCod
  SetCBPVCod-Initialsⱽ A =
    init' .fst ,
    pshiso
      (pshhom
        (λ x → init' .snd .PshIso.trans .PshHom.N-ob x)
        (λ _ _ _ _ → refl))
      (init' .snd .PshIso.nIso)
    where
    init' = OpCart.termⱽ (𝓥 , A)

  SetCBPVCod-BinCoProductsⱽ : ValueBinCoProductsⱽ SetCBPVCod
  SetCBPVCod-BinCoProductsⱽ A₁ᴰ A₂ᴰ =
    bcp' .fst ,
    pshiso
      (pshhom
        (λ x → bcp' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y f p → bcp' .snd .PshIso.trans .PshHom.N-hom x y f p))
      (bcp' .snd .PshIso.nIso)
    where
    bcp' = OpCart.bpⱽ A₁ᴰ A₂ᴰ

  SetCBPVCod-OpcartesianLifts : hasVerticalOpcartesianLiftsAt SetCBPVCod 𝓥
  SetCBPVCod-OpcartesianLifts f Aᴰ =
    lift' .fst ,
    pshiso
      (pshhom
        (λ x → lift' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y g p → lift' .snd .PshIso.trans .PshHom.N-hom x y g p))
      (lift' .snd .PshIso.nIso)
    where
    lift' = OpCart.cartesianLifts Aᴰ _ (_ , f)

  SetAddCBPVCodⱽ : AddCBPVCatⱽ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
  SetAddCBPVCodⱽ .fst = SetCBPVCodⱽ
  SetAddCBPVCodⱽ .snd .fst A = Cart.termⱽ (𝓥 , A)
  SetAddCBPVCodⱽ .snd .snd .fst = Cart.bpⱽ
  SetAddCBPVCodⱽ .snd .snd .snd .fst f Bᴰ = Cart.cartesianLifts Bᴰ _ (_ , f)
  SetAddCBPVCodⱽ .snd .snd .snd .snd .fst = SetCBPVCod-Initialsⱽ
  SetAddCBPVCodⱽ .snd .snd .snd .snd .snd .fst = SetCBPVCod-BinCoProductsⱽ
  SetAddCBPVCodⱽ .snd .snd .snd .snd .snd .snd .fst = SetCBPVCod-OpcartesianLifts
  SetAddCBPVCodⱽ .snd .snd .snd .snd .snd .snd .snd .fst B = Cart.termⱽ (𝓒 , B)
  SetAddCBPVCodⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst = Cart.bpⱽ
  SetAddCBPVCodⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd f Bᴰ =
    Cart.cartesianLifts Bᴰ _ (_ , f)
