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

  -- One proof for each of the four vertical/displayed associativity and
  -- unit laws below: they differ only in which base-level law indexes each
  -- reind, and the chain itself is the same.
  private
    reind⋆Assoc :
      ∀ {w x y z : C.ob}{wᴰ : ob[ w ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}{zᴰ : ob[ z ]}
        {f : C [ w , x ]}{g : C [ x , y ]}{h : C [ y , z ]}
        {fg : C [ w , y ]}{gh : C [ x , z ]}{u v : C [ w , z ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        (p : f C.⋆ g ≡ fg)(q : fg C.⋆ h ≡ u)
        (r : g C.⋆ h ≡ gh)(s : f C.⋆ gh ≡ v)
      → (R.reind q (R.reind p (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ))
        R.∫≡ (R.reind s (fᴰ ⋆ᴰ R.reind r (gᴰ ⋆ᴰ hᴰ)))
    reind⋆Assoc fᴰ gᴰ hᴰ p q r s =
      (sym $ R.reind-filler _)
      ∙ ∫Cᴰ.⟨ sym $ R.reind-filler _ ⟩⋆⟨ refl ⟩
      ∙ ∫Cᴰ.⋆Assoc _ _ _
      ∙ ∫Cᴰ.⟨ refl ⟩⋆⟨ R.reind-filler _ ⟩
      ∙ R.reind-filler _

    reind⋆IdL :
      ∀ {x y : C.ob}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {f : C [ x , y ]}{u : C [ x , y ]}
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])(q : C.id C.⋆ f ≡ u)
      → R.reind q (idᴰ ⋆ᴰ fᴰ) R.∫≡ fᴰ
    reind⋆IdL fᴰ q = (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdL _

    reind⋆IdR :
      ∀ {x y : C.ob}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {f : C [ x , y ]}{u : C [ x , y ]}
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])(q : f C.⋆ C.id ≡ u)
      → R.reind q (fᴰ ⋆ᴰ idᴰ) R.∫≡ fᴰ
    reind⋆IdR fᴰ q = (sym $ R.reind-filler _) ∙ ∫Cᴰ.⋆IdR _

  v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
  v[ x ] .Category.ob = ob[ x ]
  v[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
  v[ x ] .Category.id = idᴰ
  v[ x ] .Category._⋆_ fⱽ gⱽ = R.reind (C.⋆IdL _) (fⱽ ⋆ᴰ gⱽ)
  v[ x ] .Category.⋆IdL fⱽ =
    R.rectifyOut $ reind⋆IdL _ _
  v[ x ] .Category.⋆IdR fⱽ =
    R.rectifyOut $ reind⋆IdR _ _
  v[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ =
    R.rectifyOut $ reind⋆Assoc _ _ _ _ _ _ _
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
  ⋆IdLᴰⱽ = R.rectifyOut $ reind⋆IdL _ _

  ⋆IdRᴰⱽ : fᴰ ⋆ᴰⱽ idⱽ ≡ fᴰ
  ⋆IdRᴰⱽ = R.rectifyOut $ reind⋆IdR _ _

  ⋆Assocᴰⱽⱽ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ ≡ (fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
  ⋆Assocᴰⱽⱽ = R.rectifyOut $ reind⋆Assoc _ _ _ _ _ _ _

  _⋆ⱽᴰ_ : v[ x ] [ xᴰ , xᴰ' ] → Hom[ f ][ xᴰ' , yᴰ ] → Hom[ f ][ xᴰ , yᴰ ]
  _⋆ⱽᴰ_ {f = f} gⱽ fᴰ = R.reind (C.⋆IdL _) (gⱽ ⋆ᴰ fᴰ)

  ⋆IdLⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idⱽ ⋆ⱽᴰ fᴰ ≡ fᴰ
  ⋆IdLⱽᴰ fᴰ = R.rectifyOut $ reind⋆IdL _ _

  ⋆IdRⱽᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) → fⱽ ⋆ⱽᴰ idᴰ ≡ fⱽ
  ⋆IdRⱽᴰ fⱽ = R.rectifyOut $ reind⋆IdR _ _

  ⋆Assocⱽⱽᴰ : (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ ≡ (fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocⱽⱽᴰ = R.rectifyOut $ reind⋆Assoc _ _ _ _ _ _ _

  ⋆Assocⱽᴰⱽ : (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ ≡ (fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
  ⋆Assocⱽᴰⱽ = R.rectifyOut $ reind⋆Assoc _ _ _ _ _ _ _

  ⋆Assocᴰⱽᴰ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ ≡ (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocᴰⱽᴰ = R.rectifyOut $
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
