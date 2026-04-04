module Cubical.Categories.Instances.TotalCategory.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open UniversalElement
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
   module _ (term : Terminal' C) (termᴰ : Terminalᴰ Cᴰ term) where
     private
       module term = TerminalNotation term
       module termᴰ = TerminalᴰNotation Cᴰ {term = term} termᴰ
     ∫term : Terminal' (∫C Cᴰ)
     ∫term .vertex = term .vertex , termᴰ .fst
     ∫term .element = _
     ∫term .universal (Γ , Γᴰ) = isIsoToIsEquiv ((λ _ → term.!t , termᴰ.introᴰ _) ,
       (λ _ → refl)
       , (λ _ → sym $ termᴰ.∫ηᴰ _))

   -- TODO: ∫bp
   module _ {x y xᴰ yᴰ} (bp : BinProduct C (x , y)) (bpᴰ : BinProductᴰ Cᴰ bp xᴰ yᴰ) where
     private
       module bp = BinProductNotation bp
       module bpᴰ = BinProductᴰNotation Cᴰ bp bpᴰ

     ∫bp : BinProduct (∫C Cᴰ) ((x , xᴰ) , (y , yᴰ))
     ∫bp .vertex = bpᴰ.ue.vertex , bpᴰ .fst
     ∫bp .element = (bp.π₁ , bpᴰ.πᴰ₁) , (bp.π₂ , bpᴰ.πᴰ₂)
     ∫bp .universal (Γ , Γᴰ) = isIsoToIsEquiv
       ( (λ x₁ → _ , bpᴰ.introᴰ (x₁ .fst .snd , x₁ .snd .snd))
       , (λ _ → ΣPathP ((ΣPathP (bp.×β₁ , bpᴰ.×βᴰ₁ _ _)) , ΣPathP (_ , bpᴰ.×βᴰ₂ _ _)))
       , λ a → {!bpᴰ.∫ηᴰ!} -- why is there a reind-refl here?
         ∙ sym (bpᴰ.∫ηᴰ (a .snd)))


       -- bpᴰ.introᴰ
       -- ((Cᴰ
       --   Cubical.Categories.Displayed.Presheaf.Uncurried.Base.PresheafᴰNotation.⋆ᴰ
       --   ((C Cubical.Categories.Instances.Sets.[-, x ])
       --    Cubical.Categories.Presheaf.Constructions.BinProduct.Base._.×Psh
       --    (C Cubical.Categories.Instances.Sets.[-, y ])))
       --  (BinProductᴰSpec Cᴰ bp xᴰ yᴰ) (a .snd) (bpᴰ .snd .fst)))
