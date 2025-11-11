{-
  The Tabulator of a profunctor specializes to the displayed category of elements of a presheaf.
-}

module Cubical.Categories.LocallySmall.Displayed.Constructions.Graph.Presheaf.GloballySmall.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.HLevels
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.StructureOver.Base

open SmallCategoryᴰ

module _ {C : SmallCategory ℓC ℓC'} (P : Presheaf C ℓP) where
  open StructureOver
  private
    module C = SmallCategory C
    module P = PresheafNotation P
    ElementStr : StructureOver C.cat (mapω' P.p[_]) _
    ElementStr .Hom[_][_,_] f (liftω p) (liftω q) = (f P.⋆ q) ≡ p
    ElementStr .idᴰ = P.⋆IdL _
    ElementStr ._⋆ᴰ_ fy≡x gz≡y =
      P.⋆Assoc _ _ _
      ∙ cong (_ P.⋆_) gz≡y
      ∙ fy≡x
    ElementStr .isPropHomᴰ = P.isSetPsh _ _

  Element : SmallCategoryᴰ C ℓP ℓP
  Element = smallcatᴰ _ (StructureOver→Catᴰ ElementStr)

  hasPropHomsElement : hasPropHoms (Element .catᴰ)
  hasPropHomsElement = hasPropHomsStructureOver ElementStr

  private
    module ∫Element = Category (∫C Element)
    test-Element : ∀ x p y q
      → ∫Element.Hom[ (x , liftω p) , (y , liftω q) ] ≡ fiber (P._⋆ q) p
    test-Element x p y q = refl

module _ where
  open SmallCategoryVariables
  open SmallCategory
  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf D ℓQ}
    {F : Functor (C .cat) (D .cat)}
    (α : PshHet F P Q)
    where
    open SmallFibNatTrans
    PshHet→ElementFunctorᴰ :
      Functorᴰ F (Element P .catᴰ) (Element Q .catᴰ)
    PshHet→ElementFunctorᴰ =
      mkPropHomsFunctor (hasPropHomsElement Q)
        (λ (liftω p) → liftω (α .snd .N-ob _ p))
        λ {yᴰ = py} f⋆p≡p' →
          (sym $ cong (λ z → z .snd (py .Liftω.lowerω)) (N-hom' (α .snd) _))
          ∙ cong (α .snd .N-ob _) f⋆p≡p'


  module _ (F : Functor (C .cat) (D .cat))(c : C .small-ob) where
    open Functor
    Functor→ElementFunctorᴰ :
      Functorᴰ F
        (Element (C [-, c ]) .catᴰ)
        (Element (D [-, F .F-ob (liftω c) .Liftω.lowerω ]) .catᴰ)
    Functor→ElementFunctorᴰ =
      PshHet→ElementFunctorᴰ
        {Q = D [-, F-ob F (liftω c) .Liftω.lowerω ]}
        (Functor→PshHet F c)

-- module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) (α : PshHom P Q) where
--   private
--     module α = PshHom α
--   PshHom→ElementFunctorⱽ : Functorⱽ (Element P) (Element Q)
--   PshHom→ElementFunctorⱽ = PshHet→ElementFunctorᴰ (α ⋆PshHom reindPshId≅ Q .trans)

-- module _
--   {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) (Q : Presheaf D ℓQ)
--   where
--   private
--     module Q = PresheafNotation Q
--   reindPsh-intro : ∀ {P : Presheaf C ℓP}
--     → (Functorᴰ F (Element P) (Element Q))
--     → (Functorⱽ (Element P) (Element (reindPsh F Q)))
--   reindPsh-intro {P = P} Fᴰ = mkPropHomsFunctor (hasPropHomsElement $ reindPsh F Q)
--     (Fᴰ .F-obᴰ)
--     (Fᴰ .F-homᴰ)

--   reindPsh-π : Functorᴰ F (Element (reindPsh F Q)) (Element Q)
--   reindPsh-π = mkPropHomsFunctor (hasPropHomsElement Q) (λ {x} z → z) λ {x} {y} {f} {xᴰ} {yᴰ} z → z

--   reindPsh-UMPⱽ : ∀ {P : Presheaf C ℓP}
--     → Iso (Functorⱽ (Element P) (Element (reindPsh F Q)))
--           (Functorᴰ F (Element P) (Element Q))
--   reindPsh-UMPⱽ .fun = reindPsh-π ∘Fᴰⱽ_
--   reindPsh-UMPⱽ {P = P} .inv = reindPsh-intro {P = P}
--   reindPsh-UMPⱽ .rightInv Fⱽ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
--   reindPsh-UMPⱽ .leftInv Fᴰ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
