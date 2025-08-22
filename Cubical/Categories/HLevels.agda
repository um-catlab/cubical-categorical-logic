module Cubical.Categories.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open NatTrans
open NatIso
open isIso
module _ (C : Category ℓC ℓC') where
  -- alternative names: isThin, isPreorder
  hasPropHoms : Type _
  hasPropHoms = ∀ {x y} → isProp (C [ x , y ])

  module _ (isThinC : hasPropHoms) where
    mkFunctor : ∀ {D : Category ℓD ℓD'}
      → (F-ob : D .ob → C .ob)
      → (∀ {x y} → D [ x , y ] → C [ F-ob x , F-ob y ])
      → Functor D C
    mkFunctor F-ob F-hom .Functor.F-ob = F-ob
    mkFunctor F-ob F-hom .Functor.F-hom = F-hom
    mkFunctor F-ob F-hom .Functor.F-id = isThinC _ _
    mkFunctor F-ob F-hom .Functor.F-seq _ _ = isThinC _ _

    mkNatTrans : ∀ {D : Category ℓD ℓD'} {F G : Functor D C}
     → (∀ x → C [ F ⟅ x ⟆ , G ⟅ x ⟆ ])
     → F ⇒ G
    mkNatTrans α .N-ob = α
    mkNatTrans α .N-hom _ = isThinC _ _

    mkNatIso : ∀ {D : Category ℓD ℓD'} {F G : Functor D C}
       → (∀ x → C [ F ⟅ x ⟆ , G ⟅ x ⟆ ])
       → (∀ x → C [ G ⟅ x ⟆ , F ⟅ x ⟆ ])
       → F ≅ᶜ G
    mkNatIso α α⁻ .trans = mkNatTrans α
    mkNatIso α α⁻ .nIso x .inv = α⁻ x
    mkNatIso α α⁻ .nIso x .sec = isThinC _ _
    mkNatIso α α⁻ .nIso x .ret = isThinC _ _

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD')
         (F : Functor C D) (F⁻ : Functor D C)
         (ret : F⁻ ∘F F ≅ᶜ Id)
         where
  hasPropHomsIsoRetract : hasPropHoms D → hasPropHoms C
  hasPropHomsIsoRetract hasPropHomsD f f' =
    hasIsoRetraction→isFaithful F F⁻ ret _ _ f f' (hasPropHomsD _ _)
