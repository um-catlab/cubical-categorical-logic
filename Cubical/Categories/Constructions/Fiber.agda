{-

  Given a displayed category Cᴰ over C, and any object x in C, we can
  construct the fiber category over x whose objects are the Cᴰ.ob[ x ]
  and whose morphisms are those that are over the identity.

-}

module Cubical.Categories.Constructions.Fiber where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
import Cubical.Categories.Displayed.Reasoning as Reasoning
import Cubical.Categories.More as CatReasoning


private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module Fibers {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module R = Reasoning Cᴰ
  open Cᴰ public

  _∫≡_ : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]}
    (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])(gᴰ : Cᴰ [ g ][ xᴰ , yᴰ ])
    → Type _
  _∫≡_ {f = f}{g} fᴰ gᴰ = (f , fᴰ) ≡ (g , gᴰ)

  infix 2 _∫≡_

  v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
  v[ x ] .Category.ob = ob[ x ]
  v[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
  v[ x ] .Category.id = idᴰ
  v[ x ] .Category._⋆_ fⱽ gⱽ = R.reind (C.⋆IdL _) (fⱽ ⋆ᴰ gⱽ)
  v[ x ] .Category.⋆IdL fⱽ =
    R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdL _
  v[ x ] .Category.⋆IdR fⱽ =
    R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdR _
  v[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ =
    R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ R.⋆Assoc _ _ _
      ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
      ∙ R.reind-filler _ _
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
  fᴰ ⋆ᴰⱽ gⱽ = R.reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

  ⋆IdLᴰⱽ : idᴰ ⋆ᴰⱽ fⱽ ≡ fⱽ
  ⋆IdLᴰⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdL _

  ⋆IdRᴰⱽ : fᴰ ⋆ᴰⱽ idⱽ ≡ fᴰ
  ⋆IdRᴰⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdR _

  ⋆Assocᴰⱽⱽ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ ≡ (fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
  ⋆Assocᴰⱽⱽ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ R.⋆Assoc _ _ _
      ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
      ∙ R.reind-filler _ _

  _⋆ⱽᴰ_ : v[ x ] [ xᴰ , xᴰ' ] → Hom[ f ][ xᴰ' , yᴰ ] → Hom[ f ][ xᴰ , yᴰ ]
  gⱽ ⋆ⱽᴰ fᴰ = R.reind (C.⋆IdL _) (gⱽ ⋆ᴰ fᴰ)

  ⋆IdLⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idⱽ ⋆ⱽᴰ fᴰ ≡ fᴰ
  ⋆IdLⱽᴰ fᴰ = R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdL _

  ⋆IdRⱽᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) → fⱽ ⋆ⱽᴰ idᴰ ≡ fⱽ
  ⋆IdRⱽᴰ fⱽ = R.rectify $ R.≡out $ (sym $ R.reind-filler _ _) ∙ R.⋆IdR _

  ⋆Assocⱽⱽᴰ : (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ ≡ (fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocⱽⱽᴰ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ R.⋆Assoc _ _ _
      ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
      ∙ R.reind-filler _ _

  ⋆Assocⱽᴰⱽ : (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ ≡ (fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
  ⋆Assocⱽᴰⱽ = R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ R.⋆Assoc _ _ _
      ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
      ∙ R.reind-filler _ _

  ⋆Assocᴰⱽᴰ : (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ ≡ (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
  ⋆Assocᴰⱽᴰ = R.rectify $ R.≡out $
    R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _
    ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩

  ⋆Assocⱽᴰᴰ :
    Path R.Hom[ _ , _ ]
     (_ , (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ)
     (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ))
  ⋆Assocⱽᴰᴰ =
    R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _ ∙ R.reind-filler _ _

  ∫⋆Assocᴰⱽᴰ :
    Path R.Hom[ _ , _ ]
      (f C.⋆ h , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ)
      (f C.⋆ h , fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
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
  open CatReasoning.Reasoning (∫C Cᴰ) public

  ⟨_⟩⋆ⱽᴰ⟨_⟩
    : Path Hom[ _ , _ ] (_ , fⱽ) (_ , fⱽ')
    → Path Hom[ _ , _ ] (_ , gᴰ) (_ , gᴰ')
    → Path Hom[ _ , _ ]
        (_ , fⱽ ⋆ⱽᴰ gᴰ)
        (_ , fⱽ' ⋆ⱽᴰ gᴰ')
  ⟨ fⱽ≡fⱽ' ⟩⋆ⱽᴰ⟨ gᴰ≡gᴰ' ⟩ = sym (reind-filler _ _) ∙ ⟨ fⱽ≡fⱽ' ⟩⋆⟨ gᴰ≡gᴰ' ⟩ ∙ reind-filler _ _

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

  reind⟨_⟩⟨_⟩⟨_⟩ : ∀ {a b : C.ob} {f f' g g' : C [ a , b ]}{aᴰ bᴰ}
      {fᴰ : Cᴰ [ f ][ aᴰ , bᴰ ]}
      {fᴰ' : Cᴰ [ f' ][ aᴰ , bᴰ ]}
      (p : f ≡ g)
      (p' : f' ≡ g')
    → Path R.Hom[ _ , _ ]
        (f , fᴰ)
        (f' , fᴰ')
    → Path R.Hom[ _ , _ ]
        (g , reind p fᴰ)
        (g' , reind p' fᴰ')
  reind⟨ p ⟩⟨ p' ⟩⟨ fᴰ≡fᴰ' ⟩ = sym (reind-filler p _) ∙ fᴰ≡fᴰ' ∙ reind-filler p' _

open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  fiber : C .ob → Category ℓCᴰ ℓCᴰ'
  fiber x = Fibers.v[_] Cᴰ x

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}(Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  private
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
  fiberF : ∀ (x : C .ob) → Functor (fiber Cᴰ x) (fiber Dᴰ (F ⟅ x ⟆))
  fiberF x .F-ob = Fᴰ .F-obᴰ
  fiberF x .F-hom fⱽ = Dᴰ.reind (F .F-id) $ Fᴰ .F-homᴰ fⱽ
  fiberF x .F-id = Dᴰ.rectify $ Dᴰ.≡out $ sym (Dᴰ.reind-filler _ _) ∙ (Dᴰ.≡in $ F-idᴰ Fᴰ)
  fiberF x .F-seq fⱽ gⱽ = Dᴰ.rectify $ Dᴰ.≡out $
    sym (Dᴰ.reind-filler _ _)
    ∙ cong (∫F Fᴰ .F-hom) (sym $ Cᴰ.reind-filler _ _)
    ∙ (Dᴰ.≡in $ F-seqᴰ Fᴰ fⱽ gⱽ)
    ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _  ⟩⋆⟨ Dᴰ.reind-filler _ _  ⟩
    ∙ Dᴰ.reind-filler _ _ 
