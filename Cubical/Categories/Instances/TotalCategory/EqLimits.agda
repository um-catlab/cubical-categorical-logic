-- Test to demonstrate that the eq stuff works for universalelementᴰ well.
--
-- Notice that there are _NO_ reind-fillers in this entire file or any
-- reinds in any goal!
module Cubical.Categories.Instances.TotalCategory.EqLimits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Exponentials.Small

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.ExponentialD
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open UniversalElement
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
   -- module _ (term : Terminal' C) (termᴰ : Terminalᴰ Cᴰ term) where
   --   private
   --     module term = TerminalNotation term
   --     module termᴰ = TerminalᴰNotation Cᴰ {term = term} termᴰ
   --   ∫term : Terminal' (∫C Cᴰ)
   --   ∫term .vertex = term .vertex , termᴰ .fst
   --   ∫term .element = _
   --   ∫term .universal (Γ , Γᴰ) = isIsoToIsEquiv ((λ _ → term.!t , termᴰ.introᴰ _) ,
   --     (λ _ → refl)
   --     , (λ _ → sym $ termᴰ.∫ηᴰ _))

   -- TODO: ∫bp
   module _ (bp : BinProducts C) (bpᴰ : BinProductsᴰ Cᴰ bp) where
     private
       module bpᴰ = BinProductsᴰNotation Cᴰ bp bpᴰ
     ∫bp : BinProducts (∫C Cᴰ)
     ∫bp ((c , cᴰ) , d , dᴰ) .vertex = _ , bpᴰ.vᴰ cᴰ dᴰ
     ∫bp ((c , cᴰ) , d , dᴰ) .element = (_ , bpᴰ.eᴰ .fst) , _ , bpᴰ.eᴰ .snd
     ∫bp ((c , cᴰ) , d , dᴰ) .universal (Γ , Γᴰ) = isIsoToIsEquiv
       ( (λ ((_ , fᴰ) , (_ , gᴰ)) → _ , bpᴰ.introᴰ (fᴰ , gᴰ))
       , (λ b → ≡-× bpᴰ.∫×β₁ᴰ bpᴰ.∫×β₂ᴰ)
       , λ a → sym bpᴰ.∫ηᴰ)

     module _ (exp : AllExponentiable C bp) (expᴰ : AllExponentiableᴰ Cᴰ bp bpᴰ exp) where
       open UEᴰ
       ∫exp : AllExponentiable (∫C Cᴰ) ∫bp
       ∫exp c d .vertex  = _ , expᴰ (c .snd) (d .snd) .vᴰ
       ∫exp c d .element = _ , (expᴰ (c .snd) (d .snd) .eᴰ)
       ∫exp c d .universal (Γ , Γᴰ) = isIsoToIsEquiv
         ( (λ (f⟨x⟩ , fᴰ⟨xᴰ⟩) → _ , introᴰ (expᴰ (c .snd) (d .snd)) fᴰ⟨xᴰ⟩)
         , (λ (f⟨x⟩ , fᴰ⟨xᴰ⟩) → ∫βᴰ (expᴰ (c .snd) (d .snd)))
         , λ (f , fᴰ) → sym (∫ηᴰ (expᴰ (c .snd) (d .snd))))
