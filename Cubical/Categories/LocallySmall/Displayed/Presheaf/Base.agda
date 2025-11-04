module Cubical.Categories.LocallySmall.Displayed.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

import Cubical.Categories.Category.Base as SmallCat
import Cubical.Categories.Presheaf.Base as SmallPsh
import Cubical.Categories.Functor.Base as SmallFunctor
import Cubical.Categories.Displayed.Base as SmallCatᴰ
import Cubical.Categories.Displayed.Functor as SmallFunctorᴰ
import Cubical.Categories.Displayed.Presheaf.Base as SmallPshᴰ

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Presheaf.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.SmallFibers
open import Cubical.Categories.LocallySmall.Displayed.Instances.Set
open import Cubical.Categories.LocallySmall.Displayed.Instances.Functor
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω
open Liftω

private
  module SET = CategoryᴰNotation SET
  module SETᴰ = SmallFibersᴰCategoryᴰNotation SETᴰ
module _
  {C : SmallCategory ℓC ℓC'}
  where

  module _ {ℓP : Level}  (P : Presheaf C ℓP) where
    module _ (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
      private
        module Cᴰ = CategoryᴰNotation ⟨ Cᴰ ⟩smallcatᴰ

      Presheafᴰ : (ℓPᴰ : Level) → Typeω
      Presheafᴰ ℓPᴰ =
        Functorᴰ P ⟨ Cᴰ ^opsmallᴰ ⟩smallcatᴰ
          ⟨ SETᴰ.vᴰ[ liftω ℓP ][ liftω ℓPᴰ ] ⟩smallcatᴰ

      PRESHEAFᴰ : Categoryᴰ (∫C (weaken (∫C (PRESHEAF C)) LEVEL)) _ _
      PRESHEAFᴰ = FIBER-FUNCTORᴰ (Cᴰ ^opsmallᴰ) SET SETᴰ

      -- The locally small displayed category of
      -- globally small displayed presheaves
      -- displayed over the locally small category
      -- of globally small presheaves on a small
      -- category
      ∫PRESHEAFᴰ : Categoryᴰ (∫C (PRESHEAF C)) _ _
      ∫PRESHEAFᴰ = ∫Cᴰ _ PRESHEAFᴰ

      module _ {ℓPᴰ} (Pᴰ : Presheafᴰ ℓPᴰ) where
        private
          module PSHᴰ = CategoryᴰNotation PRESHEAFᴰ
          module Pᴰ = FunctorᴰNotation Pᴰ

        ∫P : Presheaf (∫Csmall Cᴰ) (ℓ-max ℓP ℓPᴰ)
        -- what goes here?
        ∫P = {!!} ∘F Pᴰ.∫F ∘F help
           where
           help :
             Functor
               (⟨ ∫Csmall Cᴰ ⟩smallcat ^op)
               (CategoryᴰNotation.∫C (⟨ Cᴰ ⟩smallcatᴰ ^opᴰ))
           help = record {
               F-ob = λ z → liftω (z .lowerω .fst) , liftω (z .lowerω .snd)
             ; F-hom = λ {x} {y} z → z
             ; F-id = refl
             ; F-seq = λ _ _ → refl }

module _
  {C : SmallCat.Category ℓC ℓC'}
  (Cᴰ : SmallCatᴰ.Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module C = SmallCat.Category C
    module Cᴰ = SmallCatᴰ.Categoryᴰ Cᴰ

  SmallPresheafᴰ : {ℓP : Level} →
    (P : SmallPresheaf C ℓP) → (ℓPᴰ : Level) → Type _
  SmallPresheafᴰ P ℓPᴰ = SmallPshᴰ.Presheafᴰ P Cᴰ ℓPᴰ

  module _ {ℓP} (P : SmallPresheaf C ℓP) ℓPᴰ where
    open Functor
    open Functorᴰ
    private
      module SFunctor = SmallFunctor.Functor
      module SFunctorᴰ = SmallFunctorᴰ.Functorᴰ
      P' = SmallPresheaf→Presheaf C ℓP P

    SmallPresheafᴰ→Presheafᴰ :
      SmallPresheafᴰ P ℓPᴰ → Presheafᴰ P' (mkSmallCategoryᴰ Cᴰ) ℓPᴰ
    SmallPresheafᴰ→Presheafᴰ Pᴰ .F-obᴰ =
      λ z → liftω (Pᴰ .SFunctorᴰ.F-obᴰ (z .lowerω))
    SmallPresheafᴰ→Presheafᴰ Pᴰ .F-homᴰ =
      Pᴰ .SFunctorᴰ.F-homᴰ
    SmallPresheafᴰ→Presheafᴰ Pᴰ .F-idᴰ =
      ΣPathP (P .SFunctor.F-id , Pᴰ .SFunctorᴰ.F-idᴰ)
    SmallPresheafᴰ→Presheafᴰ Pᴰ .F-seqᴰ {x = liftω x}{z = liftω z}
      {xᴰ = liftω xᴰ}{zᴰ = liftω zᴰ}{f = f}{g = g} fᴰ gᴰ =
      {!!}
      -- ΣPathP (P .SFunctor.F-seq _ _ , Pᴰ .SFunctorᴰ.F-seqᴰ fᴰ gᴰ)
      -- ∙ ΣPathP (
      --   (sym $ transportRefl _) ,
      --   (SETᴰ.rectify
      --     {x = (liftω ℓP , liftω (P .SFunctor.F-ob x)) , liftω ℓPᴰ}
      --     {y = (liftω ℓP , liftω (P .SFunctor.F-ob z)) , liftω ℓPᴰ}
      --     {f = (_ , λ x → P .SFunctor.F-hom g (P .SFunctor.F-hom f x)) , _}
      --     {g = (_ , λ z₁ →
      --                  P .SmallFunctor.Functor.F-hom g
      --                  (P .SmallFunctor.Functor.F-hom f z₁)) , _}
      --     {p = {!refl!}}
      --     {xᴰ = liftω (Pᴰ .SFunctorᴰ.F-obᴰ xᴰ)}
      --     {yᴰ = liftω (Pᴰ .SFunctorᴰ.F-obᴰ zᴰ)}
      --     $ transport-filler _ _))

    Presheafᴰ→SmallPresheafᴰ :
      Presheafᴰ P' (mkSmallCategoryᴰ Cᴰ) ℓPᴰ → SmallPresheafᴰ P ℓPᴰ
    Presheafᴰ→SmallPresheafᴰ Pᴰ .SFunctorᴰ.F-obᴰ =
      λ z → F-obᴰ Pᴰ (liftω z) .lowerω
    Presheafᴰ→SmallPresheafᴰ Pᴰ .SFunctorᴰ.F-homᴰ = F-homᴰ Pᴰ
    Presheafᴰ→SmallPresheafᴰ Pᴰ .SFunctorᴰ.F-idᴰ =
      {!!}
    Presheafᴰ→SmallPresheafᴰ Pᴰ .SFunctorᴰ.F-seqᴰ = {!!}
