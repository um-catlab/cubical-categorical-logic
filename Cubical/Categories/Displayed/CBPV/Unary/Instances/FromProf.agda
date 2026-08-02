-- Any profunctor 𝓞 : 𝓒 -/→ 𝓥 induces a CBPV model

-- This is also known as the "collage" or "cograph" of the profunctor
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.FromProf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

open import Cubical.Categories.Displayed.CBPV.Unary.Base

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

-- everything has to have the same levels for this to work
module _ {C : Category ℓ ℓ'}{V : Category ℓ ℓ'} (O : Profunctor C V ℓ') where
  private
    module C = Category C
    module V = Category V
    module O = RelatorNotation (CurriedToBifunctorL O)

  open Categoryᴰ
  private
    Ob : Kind → Type ℓ
    Ob 𝓥 = V.ob
    Ob 𝓒 = C.ob

    HOM[_,_][_,_] : ∀ k1 k2 → {≤Kind k1 k2} → Ob k1 → Ob k2 → Type ℓ'
    HOM[ 𝓥 , 𝓥 ][ A , A' ] = V [ A , A' ]
    HOM[ 𝓥 , 𝓒 ][ A , B  ] = O.Het[ A , B ]
    HOM[ 𝓒 , 𝓒 ][ B , B' ] = C [ B , B' ]

  Prof→CBPV : CBPVCat ℓ ℓ'
  Prof→CBPV .ob[_] = Ob
  Prof→CBPV .Hom[_][_,_] {k1}{k2} (ı k≤) = HOM[_,_][_,_] k1 k2 {k≤}
  Prof→CBPV .idᴰ {𝓥} = V.id
  Prof→CBPV .idᴰ {𝓒} = C.id
  Prof→CBPV ._⋆ᴰ_ {𝓥}{𝓥}{𝓥} = V._⋆_
  Prof→CBPV ._⋆ᴰ_ {𝓥}{𝓥}{𝓒} = O._⋆ᶜʳ_
  Prof→CBPV ._⋆ᴰ_ {𝓥}{𝓒}{𝓒} = O._⋆ʳᶜ_
  Prof→CBPV ._⋆ᴰ_ {𝓒}{𝓒}{𝓒} = C._⋆_
  Prof→CBPV .⋆IdLᴰ {𝓥}{𝓥} = V.⋆IdL
  Prof→CBPV .⋆IdLᴰ {𝓥}{𝓒} = O.⋆IdLᶜʳ
  Prof→CBPV .⋆IdLᴰ {𝓒}{𝓒} = C.⋆IdL
  Prof→CBPV .⋆IdRᴰ {𝓥}{𝓥} = V.⋆IdR
  Prof→CBPV .⋆IdRᴰ {𝓥}{𝓒} = O.⋆IdRʳᶜ
  Prof→CBPV .⋆IdRᴰ {𝓒}{𝓒} = C.⋆IdR
  Prof→CBPV .⋆Assocᴰ {𝓥}{𝓥}{𝓥}{𝓥} = V.⋆Assoc
  Prof→CBPV .⋆Assocᴰ {𝓥}{𝓥}{𝓥}{𝓒} = O.⋆Assocᶜᶜʳ
  Prof→CBPV .⋆Assocᴰ {𝓥}{𝓥}{𝓒}{𝓒} = O.⋆Assocᶜʳᶜ
  Prof→CBPV .⋆Assocᴰ {𝓥}{𝓒}{𝓒}{𝓒} = O.⋆Assocʳᶜᶜ
  Prof→CBPV .⋆Assocᴰ {𝓒}{𝓒}{𝓒}{𝓒} = C.⋆Assoc
  Prof→CBPV .isSetHomᴰ {𝓥}{𝓥} = V.isSetHom
  Prof→CBPV .isSetHomᴰ {𝓥}{𝓒} = O.isSetHet
  Prof→CBPV .isSetHomᴰ {𝓒}{𝓒} = C.isSetHom

module _ {C : Category ℓ ℓ'}{V : Category ℓ ℓ'} (U : Functor C V) where
  private
    module C = Category C
    module V = Category V

  U→CBPV : CBPVCat ℓ ℓ'
  U→CBPV = Prof→CBPV (YO ∘F U)

  hasUEq-U→CBPV : hasUEq U→CBPV
  hasUEq-U→CBPV B .fst = U ⟅ B ⟆
  hasUEq-U→CBPV B .snd .PshIsoEq.isos (𝓥 , A) = idIso
  hasUEq-U→CBPV B .snd .PshIsoEq.nat (𝓥 , A) (𝓥 , A') (_ , _ , Eq.refl) p' p Eq.refl = Eq.refl
