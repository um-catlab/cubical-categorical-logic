{-

  Given a displayed category Cᴰ over C, and any object x in C, we can
  construct the fiber category over x whose objects are the Cᴰ.ob[ x ]
  and whose morphisms are those that are over the identity.

-}

module Cubical.Categories.Instances.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module Fibers {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module R {a b : C.ob} {aᴰ : Cᴰ.ob[ a ]}{bᴰ : Cᴰ.ob[ b ]} =
      hSetReasoning (C [ a , b ] , C.isSetHom) Cᴰ.Hom[_][ aᴰ , bᴰ ]
      renaming
        (Prectify to rectify) hiding (_P≡[_]_)
    module ∫Cᴰ = Category (∫C Cᴰ)
  open Cᴰ public

  module _ (EqId⋆ : ∀ {x} → C.id {x} C.⋆ C.id {x} Eq.≡ C.id) where
    Eqv[_] : C.ob → Category ℓCᴰ ℓCᴰ'
    Eqv[ x ] .Category.ob = ob[ x ]
    Eqv[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
    Eqv[ x ] .Category.id = idᴰ
    Eqv[ x ] .Category._⋆_ fⱽ gⱽ = R.reindEq EqId⋆ (fⱽ ⋆ᴰ gⱽ)
    Eqv[ x ] .Category.⋆IdL fⱽ = R.rectifyOut (R.reindEq-filler⁻ _ ∙ ∫Cᴰ.⋆IdL _)
    Eqv[ x ] .Category.⋆IdR fⱽ = R.rectifyOut (R.reindEq-filler⁻ _ ∙ ∫Cᴰ.⋆IdR _)
    Eqv[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ = R.rectifyOut
      (R.reindEq-filler⁻ _
      ∙ ∫Cᴰ.⟨ R.reindEq-filler⁻ _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc (_ , fⱽ) (_ , gⱽ) (_ , hⱽ)
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reindEq-filler _ ⟩
      ∙ R.reindEq-filler _)
    Eqv[ x ] .Category.isSetHom = isSetHomᴰ

  module EqFibers
    (EqIdL : ∀ {x y} (f : C [ x , y ]) → C.id C.⋆ f Eq.≡ f)
    (EqIdR : ∀ {x y} (f : C [ x , y ]) → f C.⋆ C.id Eq.≡ f)
    where
    v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
    v[ x ] = Eqv[ EqIdL C.id ] x

    private
      variable
        x y : C.ob
        xᴰ xᴰ' xᴰ'' : ob[ x ]
        yᴰ yᴰ' yᴰ'' : ob[ y ]
        f : C [ x , y ]
        fᴰ : Hom[ f ][ xᴰ , yᴰ ]
        fⱽ gⱽ hⱽ : v[ x ] [ xᴰ , xᴰ' ]

    _⋆Eqⱽᴰ_ : v[ x ] [ xᴰ , xᴰ' ]
      → Hom[ f ][ xᴰ' , yᴰ ] → Hom[ f ][ xᴰ , yᴰ ]
    _⋆Eqⱽᴰ_ {f = f} gⱽ fᴰ = R.reindEq (EqIdL f) (gⱽ ⋆ᴰ fᴰ)

    _⋆ᴰEqⱽ_ : Hom[ f ][ xᴰ , yᴰ ]
      → v[ y ] [ yᴰ , yᴰ' ] → Hom[ f ][ xᴰ , yᴰ' ]
    _⋆ᴰEqⱽ_ {f = f} fᴰ gⱽ = R.reindEq (EqIdR f) (fᴰ ⋆ᴰ gⱽ)

    ⋆IdLEqⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idᴰ ⋆Eqⱽᴰ fᴰ ≡ fᴰ
    ⋆IdLEqⱽᴰ fᴰ = R.rectifyOut
      (R.reindEq-filler⁻ _ ∙ ∫Cᴰ.⋆IdL _)

    ⋆IdRᴰEqⱽ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ⋆ᴰEqⱽ idᴰ ≡ fᴰ
    ⋆IdRᴰEqⱽ fᴰ = R.rectifyOut
      (R.reindEq-filler⁻ _ ∙ ∫Cᴰ.⋆IdR _)

    ⋆AssocEqⱽⱽᴰ :
      ∀ {xᴰ₀ xᴰ₁ xᴰ₂ : ob[ x ]}
      (fⱽ : v[ x ] [ xᴰ₀ , xᴰ₁ ])
      (gⱽ : v[ x ] [ xᴰ₁ , xᴰ₂ ])
      (hᴰ : Hom[ f ][ xᴰ₂ , yᴰ ])
      → (v[ x ] .Category._⋆_ fⱽ gⱽ) ⋆Eqⱽᴰ hᴰ
        ≡ fⱽ ⋆Eqⱽᴰ (gⱽ ⋆Eqⱽᴰ hᴰ)
    ⋆AssocEqⱽⱽᴰ fⱽ gⱽ hᴰ = R.rectifyOut $
      R.reindEq-filler⁻ _
      ∙ ∫Cᴰ.⟨ R.reindEq-filler⁻ _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reindEq-filler _ ⟩
      ∙ R.reindEq-filler _

    ⋆AssocᴰEqⱽⱽ :
      ∀ {yᴰ₀ yᴰ₁ yᴰ₂ : ob[ y ]}
      (fᴰ : Hom[ f ][ xᴰ , yᴰ₀ ])
      (gⱽ : v[ y ] [ yᴰ₀ , yᴰ₁ ])
      (hⱽ : v[ y ] [ yᴰ₁ , yᴰ₂ ])
      → (fᴰ ⋆ᴰEqⱽ gⱽ) ⋆ᴰEqⱽ hⱽ
        ≡ fᴰ ⋆ᴰEqⱽ (v[ y ] .Category._⋆_ gⱽ hⱽ)
    ⋆AssocᴰEqⱽⱽ fᴰ gⱽ hⱽ = R.rectifyOut $
      R.reindEq-filler⁻ _
      ∙ ∫Cᴰ.⟨ R.reindEq-filler⁻ _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reindEq-filler _ ⟩
      ∙ R.reindEq-filler _

    ⋆AssocEqⱽᴰEqⱽ :
      ∀ {xᴰ₀ xᴰ₁ : ob[ x ]}{yᴰ₀ yᴰ₁ : ob[ y ]}
      (fⱽ : v[ x ] [ xᴰ₀ , xᴰ₁ ])
      (gᴰ : Hom[ f ][ xᴰ₁ , yᴰ₀ ])
      (hⱽ : v[ y ] [ yᴰ₀ , yᴰ₁ ])
      → (fⱽ ⋆Eqⱽᴰ gᴰ) ⋆ᴰEqⱽ hⱽ
        ≡ fⱽ ⋆Eqⱽᴰ (gᴰ ⋆ᴰEqⱽ hⱽ)
    ⋆AssocEqⱽᴰEqⱽ fⱽ gᴰ hⱽ = R.rectifyOut $
      R.reindEq-filler⁻ _
      ∙ ∫Cᴰ.⟨ R.reindEq-filler⁻ _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reindEq-filler _ ⟩
      ∙ R.reindEq-filler _

    open NatTrans
    HomᴰProf : (f : C [ x , y ]) → Profunctor v[ y ] v[ x ] ℓCᴰ'
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .fst = Hom[ f ][ xᴰ , yᴰ ]
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .snd = isSetHomᴰ
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-hom gⱽ fᴰ = gⱽ ⋆Eqⱽᴰ fᴰ
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-id = funExt ⋆IdLEqⱽᴰ
    HomᴰProf f .Functor.F-ob yᴰ .Functor.F-seq hⱽ gⱽ =
      funExt λ fᴰ → ⋆AssocEqⱽⱽᴰ gⱽ hⱽ fᴰ
    HomᴰProf f .Functor.F-hom gⱽ .N-ob xᴰ fᴰ = fᴰ ⋆ᴰEqⱽ gⱽ
    HomᴰProf f .Functor.F-hom gⱽ .N-hom fⱽ =
      funExt λ hᴰ → ⋆AssocEqⱽᴰEqⱽ fⱽ hᴰ gⱽ
    HomᴰProf f .Functor.F-id = makeNatTransPath
      (funExt (λ _ → funExt ⋆IdRᴰEqⱽ))
    HomᴰProf f .Functor.F-seq gⱽ hⱽ = makeNatTransPath
      (funExt λ _ → funExt λ fᴰ → sym $ ⋆AssocᴰEqⱽⱽ fᴰ gⱽ hⱽ)

  v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
  v[ x ] .Category.ob = ob[ x ]
  v[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
  v[ x ] .Category.id = idᴰ
  v[ x ] .Category._⋆_ fⱽ gⱽ = R.reind (C.⋆IdL _) (fⱽ ⋆ᴰ gⱽ)
  v[ x ] .Category.⋆IdL fⱽ =
    R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdL _
  v[ x ] .Category.⋆IdR fⱽ =
    R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdR _
  v[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ =
    R.rectify $ R.≡out $
      (sym $ R.reind-filler _)
      ∙ ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩
      ∙ R.reind-filler _
  v[ x ] .Category.isSetHom = isSetHomᴰ

  idⱽ : ∀ {x xᴰ} → v[ x ] [ xᴰ , xᴰ ]
  idⱽ = v[ _ ] .Category.id

  _⋆ⱽ_ : ∀ {x xᴰ xᴰ' xᴰ''} → v[ x ] [ xᴰ , xᴰ' ] → v[ x ] [ xᴰ' , xᴰ'' ]
    → v[ x ] [ xᴰ , xᴰ'' ]
  _⋆ⱽ_ = v[ _ ] .Category._⋆_
  private
    variable
      x y z : C.ob
      xᴰ xᴰ' xᴰ'' yᴰ yᴰ' yᴰ'' zᴰ : ob[ x ]
      f g h : C [ x , y ]
      fᴰ fᴰ' gᴰ gᴰ' hᴰ hᴰ' : Cᴰ [ f ][ xᴰ , yᴰ ]
      fⱽ fⱽ' gⱽ gⱽ' hⱽ hⱽ' : v[ x ] [ xᴰ , xᴰ' ]

  -- TODO: make the "reasoning machine" the default
  ⋆IdLⱽ : idⱽ ⋆ⱽ fⱽ ≡ fⱽ
  ⋆IdLⱽ = v[ _ ] .Category.⋆IdL _

  ⋆IdRⱽ : fⱽ ⋆ⱽ idⱽ ≡ fⱽ
  ⋆IdRⱽ = v[ _ ] .Category.⋆IdR _

  ⋆Assocⱽ : (fⱽ ⋆ⱽ gⱽ) ⋆ⱽ hⱽ ≡ fⱽ ⋆ⱽ (gⱽ ⋆ⱽ hⱽ)
  ⋆Assocⱽ = v[ _ ] .Category.⋆Assoc _ _ _

  isSetHomⱽ : isSet (v[ x ] [ xᴰ , xᴰ' ])
  isSetHomⱽ = isSetHomᴰ

  _⋆ᴰⱽ_ : Hom[ f ][ xᴰ , yᴰ ] → v[ y ] [ yᴰ , yᴰ' ] → Hom[ f ][ xᴰ , yᴰ' ]
  _⋆ᴰⱽ_ {f = f} fᴰ gⱽ = R.reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)
  ⋆IdLᴰⱽ : idᴰ ⋆ᴰⱽ fⱽ ≡ fⱽ
  ⋆IdLᴰⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdL _

  ⋆IdRᴰⱽ : fᴰ ⋆ᴰⱽ idⱽ ≡ fᴰ
  ⋆IdRᴰⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdR _

  ⋆Assocᴰⱽⱽ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ ≡ (fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
  ⋆Assocᴰⱽⱽ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _)
      ∙ ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩
      ∙ R.reind-filler _

  _⋆ⱽᴰ_ : v[ x ] [ xᴰ , xᴰ' ] → Hom[ f ][ xᴰ' , yᴰ ] → Hom[ f ][ xᴰ , yᴰ ]
  _⋆ⱽᴰ_ {f = f} gⱽ fᴰ = R.reind (C.⋆IdL _) (gⱽ ⋆ᴰ fᴰ)

  ⋆IdLⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idⱽ ⋆ⱽᴰ fᴰ ≡ fᴰ
  ⋆IdLⱽᴰ fᴰ = R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdL _

  ⋆IdRⱽᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) → fⱽ ⋆ⱽᴰ idᴰ ≡ fⱽ
  ⋆IdRⱽᴰ fⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdR _

  ⋆Assocⱽⱽᴰ : (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ ≡ (fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocⱽⱽᴰ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _)
      ∙ ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩
      ∙ R.reind-filler _

  ⋆Assocⱽᴰⱽ : (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ ≡ (fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
  ⋆Assocⱽᴰⱽ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _)
      ∙ ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩
      ∙ R.reind-filler _

  ⋆Assocᴰⱽᴰ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ ≡ (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocᴰⱽᴰ = R.rectify $ R.≡out $
    ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
    ∙ ∫Cᴰ.⋆Assoc _ _ _
    ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩

  ⋆Assocⱽᴰᴰ : ((fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ) R.∫≡ (fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ))
  ⋆Assocⱽᴰᴰ =
    ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
    ∙ ∫Cᴰ.⋆Assoc _ _ _
    ∙ R.reind-filler _

  ∫⋆Assocᴰⱽᴰ : ((fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ) R.∫≡ (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ∫⋆Assocᴰⱽᴰ = R.≡in ⋆Assocᴰⱽᴰ

  open NatTrans
  HomᴰProf : (f : C [ x , y ]) → Profunctor v[ y ] v[ x ] ℓCᴰ'
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .fst = Hom[ f ][ xᴰ , yᴰ ]
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .snd = isSetHomᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-hom gⱽ fᴰ = gⱽ ⋆ⱽᴰ fᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-id = funExt ⋆IdLⱽᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-seq hⱽ gⱽ = funExt λ fᴰ → ⋆Assocⱽⱽᴰ
  HomᴰProf f .Functor.F-hom gⱽ .N-ob x fᴰ = fᴰ ⋆ᴰⱽ gⱽ
  HomᴰProf f .Functor.F-hom gⱽ .N-hom fⱽ = funExt λ hᴰ → ⋆Assocⱽᴰⱽ
  HomᴰProf f .Functor.F-id = makeNatTransPath (funExt (λ _ → funExt λ fᴰ →
    ⋆IdRᴰⱽ))
  HomᴰProf f .Functor.F-seq gⱽ hⱽ = makeNatTransPath (funExt λ _ → funExt λ fᴰ →
    sym $ ⋆Assocᴰⱽⱽ)

  open R public
  open ∫Cᴰ public

  ⟨_⟩⋆ⱽᴰ⟨_⟩
    : Path Hom[ _ , _ ] (_ , fⱽ) (_ , fⱽ')
    → Path Hom[ _ , _ ] (_ , gᴰ) (_ , gᴰ')
    → Path Hom[ _ , _ ]
        (_ , fⱽ ⋆ⱽᴰ gᴰ)
        (_ , fⱽ' ⋆ⱽᴰ gᴰ')
  ⟨ fⱽ≡fⱽ' ⟩⋆ⱽᴰ⟨ gᴰ≡gᴰ' ⟩ = sym (reind-filler _) ∙ ⟨ fⱽ≡fⱽ' ⟩⋆⟨ gᴰ≡gᴰ' ⟩ ∙ reind-filler _

  ⟨⟩⋆ⱽᴰ⟨_⟩
    : Path Hom[ _ , _ ] (_ , gᴰ) (_ , gᴰ')
    → Path Hom[ _ , _ ]
        (_ , fⱽ ⋆ⱽᴰ gᴰ)
        (_ , fⱽ ⋆ⱽᴰ gᴰ')
  ⟨⟩⋆ⱽᴰ⟨ gᴰ≡gᴰ' ⟩ = ⟨ refl ⟩⋆ⱽᴰ⟨ gᴰ≡gᴰ' ⟩

  ⟨_⟩⋆ⱽᴰ⟨⟩
    : Path Hom[ _ , _ ] (_ , fⱽ) (_ , fⱽ')
    → Path Hom[ _ , _ ]
        (_ , fⱽ  ⋆ⱽᴰ gᴰ)
        (_ , fⱽ' ⋆ⱽᴰ gᴰ)
  ⟨ fⱽ≡fⱽ' ⟩⋆ⱽᴰ⟨⟩ = ⟨ fⱽ≡fⱽ' ⟩⋆ⱽᴰ⟨ refl ⟩

  cong-reind : ∀ {a b : C.ob} {f f' g g' : C [ a , b ]}{aᴰ bᴰ}
      {fᴰ : Cᴰ [ f ][ aᴰ , bᴰ ]}
      {fᴰ' : Cᴰ [ f' ][ aᴰ , bᴰ ]}
      (p : f ≡ g)
      (p' : f' ≡ g')
    → fᴰ ∫≡ fᴰ'
    → reind p fᴰ ∫≡ reind p' fᴰ'
  cong-reind p p' fᴰ≡fᴰ' = sym (reind-filler _) ∙ fᴰ≡fᴰ' ∙ reind-filler _

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  fiber : C .ob → Category ℓCᴰ ℓCᴰ'
  fiber x = Fibers.v[_] Cᴰ x

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  (EqIdL : ∀ {x y} (f : C [ x , y ])
    → Category._⋆_ C (Category.id C) f Eq.≡ f)
  (EqIdR : ∀ {x y} (f : C [ x , y ])
    → Category._⋆_ C f (Category.id C) Eq.≡ f)
  (F : Functorⱽ Cᴰ Dᴰ)
  where
  private
    module Cᴰ = Fibers.EqFibers Cᴰ EqIdL EqIdR
    module Dᴰ = Fibers.EqFibers Dᴰ EqIdL EqIdR
    module CR = Fibers Cᴰ
    module DR = Fibers Dᴰ
    module F = Functorᴰ F

  EqFiberFunctor : ∀ x → Functor Cᴰ.v[ x ] Dᴰ.v[ x ]
  EqFiberFunctor x .Functor.F-ob = F.F-obᴰ
  EqFiberFunctor x .Functor.F-hom = F.F-homᴰ
  EqFiberFunctor x .Functor.F-id = DR.rectifyOut $
    DR.reindEq-filler⁻ _
    ∙ DR.≡in F.F-idᴰ
    ∙ DR.reindEq-filler _
  EqFiberFunctor x .Functor.F-seq f g = DR.rectifyOut $
    cong (Functor.F-hom (∫F F)) (CR.reindEq-filler⁻ _)
    ∙ DR.≡in (F.F-seqᴰ f g)
    ∙ DR.reindEq-filler _
