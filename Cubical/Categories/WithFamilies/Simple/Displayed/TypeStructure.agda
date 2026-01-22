-- Displayed and vertical type structure:
--
-- Functionᴰ
-- Functionⱽ
-- ∀
module Cubical.Categories.WithFamilies.Simple.Displayed.TypeStructure where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
    ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
  open SCwF S
  open SCwFᴰ Sᴰ
  FunTypeᴰ : {A B : Ty} (A⇒B : FunType S A B) (Aᴰ : Tyᴰ A)(Bᴰ : Tyᴰ B) → Type _
  FunTypeᴰ {A} A⇒B Aᴰ Bᴰ =
    Σ[ Aᴰ⇒ᴰBᴰ ∈ Tyᴰ (A⇒B .fst) ]
    -- ⇒ᴰPshSmall = extᴰAᴰ* (Tmᴰ Bᴰ)
    PshIsoᴰ (A⇒B .snd) (Tmᴰ Aᴰ⇒ᴰBᴰ) (⇒ᴰPshSmall {Q = Tm _} (Tm A , ext A) (Tmᴰ Aᴰ , extᴰ Aᴰ) (Tmᴰ Bᴰ))

  -- 

-- module _ (S@(C , Ty , Tm , tm , ext) : SCwF ℓC ℓC' ℓT ℓT')
--   (Sⱽ@(Cᴰ , Tyᴰ , Tmᴰ , tmⱽ , cLSubst , bpⱽ , cLTerm) : SCwFⱽ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')
--   where
  
--   FunTypesⱽ : {A : Ty} (Aᴰ Bᴰ : Tyᴰ A) → Type _
--   FunTypesⱽ {A} Aᴰ Bᴰ =
--     Σ[ Aᴰ⇒ⱽBᴰ ∈ Tyᴰ A ]
--     PshIsoⱽ {!Tmᴰ Aᴰ⇒ⱽBᴰ!} {!!}
