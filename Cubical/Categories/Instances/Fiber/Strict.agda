{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Fiber.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Strictification
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C' : Category ℓC ℓC'} where
  private
    C : Category _ _
    C = YonedaStrictify C'

  module Fibers (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
    private
      module C = Category C
      module Cᴰ = Categoryᴰ Cᴰ
      module R {a b : C.ob} {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]} =
        hSetReasoning (C [ a , b ] , C.isSetHom) Cᴰ.Hom[_][ aᴰ , bᴰ ]
        renaming
          (Prectify to rectify) hiding (_P≡[_]_)
      module ∫Cᴰ = Category (∫C Cᴰ)
    open Cᴰ public

    v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
    v[ x ] .Category.ob = ob[ x ]
    v[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
    v[ x ] .Category.id = idᴰ
    -- Removed a reind here
    v[ x ] .Category._⋆_ fⱽ gⱽ = fⱽ ⋆ᴰ gⱽ
    v[ x ] .Category.⋆IdL fⱽ = R.rectifyOut $ ∫Cᴰ.⋆IdL _
    v[ x ] .Category.⋆IdR fⱽ = R.rectifyOut $ ∫Cᴰ.⋆IdR _
    v[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ = R.rectifyOut $ ∫Cᴰ.⋆Assoc _ _ _
    v[ x ] .Category.isSetHom = isSetHomᴰ

    private
      variable
        x y z : C.ob
        xᴰ xᴰ' xᴰ'' yᴰ yᴰ' yᴰ'' zᴰ : ob[ x ]
        f g h : C [ x , y ]
        fᴰ fᴰ' gᴰ gᴰ' hᴰ hᴰ' : Cᴰ [ f ][ xᴰ , yᴰ ]
        fⱽ fⱽ' gⱽ gⱽ' hⱽ hⱽ' : v[ x ] [ xᴰ , xᴰ' ]

    open NatTrans
    HomᴰProf : (f : C [ x , y ]) → Profunctor v[ y ] v[ x ] ℓCᴰ'
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .fst = Hom[ f ][ xᴰ , yᴰ ]
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .snd = isSetHomᴰ
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-hom gⱽ fᴰ = gⱽ ⋆ᴰ fᴰ
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-id =
      funExt λ fᴰ → R.rectifyOut $ ∫Cᴰ.⋆IdL _
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-seq hⱽ gⱽ =
      funExt λ fᴰ → R.rectifyOut $ ∫Cᴰ.⋆Assoc _ _ _
    HomᴰProf f .Functor.F-hom gⱽ .N-ob x fᴰ = fᴰ ⋆ᴰ gⱽ
    HomᴰProf f .Functor.F-hom gⱽ .N-hom fⱽ =
      funExt λ hᴰ → R.rectifyOut $ ∫Cᴰ.⋆Assoc _ _ _
    HomᴰProf f .Functor.F-id = makeNatTransPath (funExt (λ _ → funExt λ fᴰ →
      R.rectifyOut $ ∫Cᴰ.⋆IdR _))
    HomᴰProf f .Functor.F-seq gⱽ hⱽ = makeNatTransPath (funExt λ _ → funExt λ fᴰ →
      sym $ R.rectifyOut $ ∫Cᴰ.⋆Assoc _ _ _)

    open R public
    open ∫Cᴰ public

    cong-reind : ∀ {a b : C.ob} {f f' g g' : C [ a , b ]}{aᴰ bᴰ}
        {fᴰ : Cᴰ [ f ][ aᴰ , bᴰ ]}
        {fᴰ' : Cᴰ [ f' ][ aᴰ , bᴰ ]}
        (p : f ≡ g)
        (p' : f' ≡ g')
      → fᴰ ∫≡ fᴰ'
      → reind p fᴰ ∫≡ reind p' fᴰ'
    cong-reind p p' fᴰ≡fᴰ' = sym (reind-filler _) ∙ fᴰ≡fᴰ' ∙ reind-filler _

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ (YonedaStrictify C) ℓCᴰ ℓCᴰ') where
  open Category
  fiber : C .ob → Category ℓCᴰ ℓCᴰ'
  fiber x = Fibers.v[_] Cᴰ x
