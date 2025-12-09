
module Cubical.Categories.NaturalTransformation.Reind where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Equality
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Arrow

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open NatTrans
open NatIso
open isIsoC
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

  -- TODO: it would be a lot more ergonomic if we had the following
  -- function, but we can't because FunctorEq is an Eq between
  -- functions, so it would require function extensionality

  -- we should probably change the definition of FunctorEq to make this work!

  -- module _ (Fl Fr Gl Gr : Functor C D) where
  --   ,F-FunctorEq : FunctorEq Fl Fr → FunctorEq Gl Gr →  FunctorEq (Fl ,F Gl) (Fr ,F Gr)
  --   ,F-FunctorEq Fl≅Fr Gl≅Gr .fst = {!Fl≅Fr .fst!}
  --   ,F-FunctorEq Fl≅Fr Gl≅Gr .snd = {!!}

  open Functor
  reindNatTrans : (Fl Fr Gl Gr : Functor C D)
    → FunctorEq (Fl ,F Gl) (Fr ,F Gr)
    → Fl ⇒ Gl
    → Fr ⇒ Gr
  reindNatTrans Fl Fr Gl Gr F≡G α = ArrowReflection
    (reindS' F≡G (arrIntroS α))

  reindNatIso : (Fl Fr Gl Gr : Functor C D)
    → FunctorEq (Fl ,F Gl) (Fr ,F Gr)
    → Fl ≅ᶜ Gl
    → Fr ≅ᶜ Gr
  reindNatIso Fl Fr Gl Gr F≡G α = IsoReflection
    (reindS' F≡G (isoIntroS α))

  eqToNatTrans : {F G : Functor C D}
    → FunctorEq (F ,F F) (F ,F G) → F ⇒ G
  eqToNatTrans {F = F}{G = G} F≡G =
    reindNatTrans F F F G F≡G
    (idTrans F)

  eqToNatIso : {F G : Functor C D}
    → FunctorEq (F ,F F) (F ,F G) → F ≅ᶜ G
  eqToNatIso {F = F}{G = G} F≡G =
    reindNatIso F F F G F≡G
    (idNatIso F)
