{-
  Alternate definition of displayed categories.

  Equivalent to a lax functor functor to a bicategory of Profunctors.

  I've sketched out the major definitions that we need for gluing, culminating in curried and uncurried variants of displayed presheaves.

  Currently I've left all of the proofs as holes.
-}
module Cubical.Categories.Displayed.Thick.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Level
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More hiding (_≡[_]_)

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear
open import Cubical.Categories.Profunctor.Homomorphism.NaturalElement
open import Cubical.Categories.Profunctor.Homomorphism.Unary

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCⱽ ℓCᴰ' ℓDᴰ ℓDⱽ ℓDᴰ' ℓP ℓP' ℓQ ℓQ' : Level

open Category
open NaturalElement

record Categoryᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCⱽ ℓCᴰ' : Type ((ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ (ℓ-max ℓCⱽ ℓCᴰ'))))) where
  no-eta-equality
  private
    module C = Category C
  field
    vCat : C.ob → Category ℓCᴰ ℓCⱽ
  module vCat {x} = Category (vCat x)
  v[_] : C.ob → Type ℓCᴰ
  v[ x ] = vCat x .ob

  vHom[_,_] : ∀ {x} → v[ x ] → v[ x ] → Type ℓCⱽ
  vHom[_,_] {x = x} = vCat x .Hom[_,_]

  field
    -- includes vertical composition etc etc
    HomᴰP : ∀ {x y} (f : C [ x , y ]) → vCat x o-[ ℓCᴰ' ]-* vCat y

  module Het {x y}{f : C [ x , y ]} = RelatorNotation (HomᴰP f)
  open Het

  Hom[_][_,_] : ∀ {x y} (f : C [ x , y ]) → v[ x ] → v[ y ] → Type _
  Hom[_][_,_] f = Het.Het[_,_] {f = f}

  field
    --
    idᴰElt : ∀ {x} → NaturalElement (HomᴰP (C.id {x}))
    ⋆ᴰBilinear : ∀ {x y z}(f : C [ x , y ])(g : C [ y , z ])
      → Bilinear (HomᴰP f) (HomᴰP g) (HomᴰP (f C.⋆ g))

  vtod : ∀ {x}{xᴰ xᴰ' : v[ x ]} (f : vHom[ xᴰ , xᴰ' ]) → Hom[ C.id ][ xᴰ , xᴰ' ]
  vtod {x} {xᴰ}{xᴰ'} = idᴰElt .N-hom xᴰ xᴰ'

  _⋆ᴰ_ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f C.⋆ g ][ xᴰ , zᴰ ]
  _⋆ᴰ_ {x}{y}{z}{f}{g} = ⋆ᴰBilinear f g .Bilinear.hom

  infixr 9 _⋆ᴰ_

  module R {x}{y}{xᴰ : v[ x ]}{yᴰ : v[ y ]} =
    hSetReasoning (C [ x , y ] , C.isSetHom) Hom[_][ xᴰ , yᴰ ]
    renaming (Prectify to rectify; _P≡[_]_ to _≡[_]_)
  open R public

  field
    ⋆ⱽᴰ≡ : ∀ {x y xᴰ xᴰ' yᴰ}{g : C [ x , y ]}(fⱽ : vHom[ xᴰ , xᴰ' ])(gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
      → (vtod fⱽ ⋆ᴰ gᴰ ) ≡[ C.⋆IdL g ] ((fⱽ Het.⋆ᶜʳ gᴰ))
    ⋆ᴰⱽ≡ : ∀ {x y xᴰ yᴰ yᴰ'}{f : C [ x , y ]}(fᴰ : Hom[ f ][ xᴰ , yᴰ ])(gⱽ : vHom[ yᴰ , yᴰ' ])
      → (fᴰ ⋆ᴰ vtod gⱽ ) ≡[ C.⋆IdR f ] (fᴰ Het.⋆ʳᶜ gⱽ)
    ⋆Assocᴰ : ∀ {x y z w} {f : C [ x , y ]} {g : C [ y , z ]}  {h : C [ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
      → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ C.⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)

    -- should this be baked in or not?
    isNormal : ∀ {x}(xᴰ yᴰ : v[ x ]) → isEquiv (idᴰElt {x} .N-hom xᴰ yᴰ)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ') where
  open Categoryᴰ
  open Bifunctor
  private module C = Category C
  private module Cᴰ = Categoryᴰ Cᴰ
  _^opᴰ : Categoryᴰ (C ^op) ℓCᴰ ℓCⱽ ℓCᴰ'
  _^opᴰ .Categoryᴰ.vCat x = Cᴰ.vCat x ^op
  _^opᴰ .HomᴰP f .Bifunctor.Bif-ob xᴰ yᴰ = Cᴰ.HomᴰP f .Bif-ob yᴰ xᴰ
  _^opᴰ .HomᴰP f .Bifunctor.Bif-homL = λ f₁ d → Cᴰ.Het.Bif-homR d f₁
  _^opᴰ .HomᴰP f .Bifunctor.Bif-homR = λ c g → Cᴰ.Het.Bif-homL g c
  _^opᴰ .HomᴰP f .Bifunctor.Bif-hom× = λ f₁ g → Cᴰ.Het.Bif-hom× g f₁
  _^opᴰ .HomᴰP f .Bifunctor.Bif-L-id = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-L-seq = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-R-id = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-R-seq = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-×-id = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-×-seq = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-L×-agree = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-R×-agree = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-LR-fuse = {!!}
  _^opᴰ .HomᴰP f .Bifunctor.Bif-RL-fuse = {!!}
  _^opᴰ .Categoryᴰ.idᴰElt = record
                             { N-ob = {!!}
                             ; N-hom = λ x y f → Cᴰ.idᴰElt .N-hom y x f
                             ; N-nat = {!!}
                             ; N-ob-determines-N-hom = {!!}
                             }
  _^opᴰ .Categoryᴰ.⋆ᴰBilinear = {!!}
  _^opᴰ .Categoryᴰ.⋆ⱽᴰ≡ = {!!}
  _^opᴰ .Categoryᴰ.⋆ᴰⱽ≡ = {!!}
  _^opᴰ .Categoryᴰ.⋆Assocᴰ = {!!}
  _^opᴰ .Categoryᴰ.isNormal = λ xᴰ yᴰ → Cᴰ.isNormal yᴰ xᴰ


  open import Cubical.HITs.Pushout
  import Cubical.Data.Equality as Eq
  open import Cubical.HITs.MappingCylinder.Base

  ∫v : ∀ x y (xᴰ : Cᴰ.v[ x ]) (yᴰ : Cᴰ.v[ y ]) → Type (ℓ-max ℓC ℓCⱽ)
  ∫v x y xᴰ yᴰ = Σ (x Eq.≡ y) λ { Eq.refl → Cᴰ.vHom[ xᴰ , yᴰ ] }

  -- This is just one possible definition of the total category, the
  -- usual one that ignores the vertical morphisms would also be fine
  -- of course, and Iso as a category to this one.
  --
  -- The MappingCylinder definition is the right one to get the right
  -- definition of an uncurried displayed presheaf.
  ∫C : Category (ℓ-max ℓC ℓCᴰ) (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCⱽ) ℓCᴰ')
  ∫C .ob = Σ[ x ∈ C.ob ] Cᴰ.v[ x ]
  ∫C .Hom[_,_] (x , xᴰ) (y , yᴰ) =
    MappingCylinder {A = ∫v _ _ xᴰ yᴰ}{B = Σ[ f ∈ (C [ x , y ]) ] Cᴰ.Hom[ f ][ xᴰ , yᴰ ]}
      λ { (Eq.refl , fⱽ) → C.id , (Cᴰ.vtod fⱽ) }
  ∫C .id = inl (Eq.refl , Cᴰ.vCat _ .id)
  ∫C ._⋆_ = {!!}
  ∫C .⋆IdL = {!!}
  ∫C .⋆IdR = {!!}
  ∫C .⋆Assoc = {!!}
  ∫C .isSetHom = {!!}

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) (Dᴰ : Categoryᴰ D ℓDᴰ ℓDⱽ ℓDᴰ') where
  open Categoryᴰ
  private module Dᴰ = Categoryᴰ Dᴰ
  reindex : Categoryᴰ C ℓDᴰ ℓDⱽ ℓDᴰ'
  reindex .vCat x = Dᴰ.vCat (F ⟅ x ⟆)
  reindex .HomᴰP f = Dᴰ.HomᴰP (F ⟪ f ⟫)
  -- I don't think we really need N-ob here...
  reindex .idᴰElt .N-ob Fxᴰ = Dᴰ.reind (sym $ F .Functor.F-id) (Dᴰ.idᴰElt .N-ob Fxᴰ)
  reindex .idᴰElt .N-hom Fxᴰ Fxᴰ' fⱽ = Dᴰ.reind (sym $ F .Functor.F-id) (Dᴰ.idᴰElt .N-hom Fxᴰ Fxᴰ' fⱽ)
  reindex .idᴰElt .N-nat = {!!}
  reindex .idᴰElt .N-ob-determines-N-hom = {!!}
  reindex .⋆ᴰBilinear f g .Bilinear.hom Ffᴰ Fgᴰ = Dᴰ.reind (sym $ F .Functor.F-seq f g)
    (Ffᴰ Dᴰ.⋆ᴰ Fgᴰ)
  reindex .⋆ᴰBilinear f g .Bilinear.natL = {!!}
  reindex .⋆ᴰBilinear f g .Bilinear.natM = {!!}
  reindex .⋆ᴰBilinear f g .Bilinear.natR = {!!}
  reindex .⋆ⱽᴰ≡ = {!!}
  reindex .⋆ᴰⱽ≡ = {!!}
  reindex .⋆Assocᴰ = {!!}
  reindex .isNormal = {!!}

record Functorᴰ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ')(Dᴰ : Categoryᴰ D ℓDᴰ ℓDⱽ ℓDᴰ')
  : Type ((ℓC ⊔ ℓC') ⊔ (ℓD ⊔ ℓD') ⊔ (ℓCᴰ ⊔ ℓCⱽ ⊔ ℓCᴰ') ⊔ (ℓDᴰ ⊔ ℓDⱽ ⊔ ℓDᴰ')) where
  no-eta-equality
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  field
    F-obⱽ : ∀ {x} → Functor (Cᴰ.vCat x) (Dᴰ.vCat (F ⟅ x ⟆))
    F-homᴰ :  ∀ {x}{y} → (f : C [ x , y ])
      → Homomorphism (Cᴰ.HomᴰP f) ((Dᴰ.HomᴰP (F ⟪ f ⟫)) ∘Flr ((F-obⱽ ^opF) , F-obⱽ))

-- Probably not necessary to have this separately from Functorᴰ
Functorⱽ : {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ')(Dᴰ : Categoryᴰ C ℓDᴰ ℓDⱽ ℓDᴰ')
  → Type (ℓ-max
          (ℓ-max
           (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCⱽ) ℓCᴰ') ℓDᴰ)
           ℓDⱽ)
          ℓDᴰ')
Functorⱽ = Functorᴰ Id

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ')(Dᴰ : Categoryᴰ C ℓDᴰ ℓDⱽ ℓDᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  ×ᴰ : Categoryᴰ C (ℓ-max ℓCᴰ ℓDᴰ) (ℓ-max ℓCⱽ ℓDⱽ) (ℓ-max ℓCᴰ' ℓDᴰ')
  ×ᴰ .Categoryᴰ.vCat x = Cᴰ.vCat x ×C Dᴰ.vCat x
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-ob (xᴰ , xᴰ') (yᴰ , yᴰ') .fst = (Cᴰ.Hom[ f ][ xᴰ , yᴰ ] × Dᴰ.Hom[ f ][ xᴰ' , yᴰ' ])
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-ob (xᴰ , xᴰ') (yᴰ , yᴰ') .snd = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-homL = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-homR = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-hom× = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L-id = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L-seq = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R-id = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R-seq = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-×-id = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-×-seq = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L×-agree = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R×-agree = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-LR-fuse = {!!}
  ×ᴰ .Categoryᴰ.HomᴰP f .Bifunctor.Bif-RL-fuse = {!!}
  ×ᴰ .Categoryᴰ.idᴰElt = {!!}
  ×ᴰ .Categoryᴰ.⋆ᴰBilinear = {!!}
  ×ᴰ .Categoryᴰ.⋆ⱽᴰ≡ = {!!}
  ×ᴰ .Categoryᴰ.⋆ᴰⱽ≡ = {!!}
  ×ᴰ .Categoryᴰ.⋆Assocᴰ = {!!}
  ×ᴰ .Categoryᴰ.isNormal = {!!}
module _ ℓ ℓ' where
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Instances.Power
  open Bifunctor
  SETᴰ : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  SETᴰ .Categoryᴰ.vCat X = PowerCategory ⟨ X ⟩ (SET ℓ')
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-ob Xᴰ Yᴰ .fst = ∀ x → ⟨ Xᴰ x ⟩ → ⟨ Yᴰ (f x) ⟩
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-ob Xᴰ Yᴰ .snd = isSetΠ λ _ → isSet→ (Yᴰ _ .snd)
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-homL = λ f₁ d z x₁ z₁ → z x₁ (f₁ x₁ z₁)
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-homR = λ c g z x₁ z₁ → g (f x₁) (z x₁ z₁)
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-hom× = λ f₁ g z x₁ z₁ → g (f x₁) (z x₁ (f₁ x₁ z₁))
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-L-id = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-L-seq = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-R-id = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-R-seq = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-×-id = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-×-seq = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-L×-agree = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-R×-agree = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-LR-fuse = {!!}
  SETᴰ .Categoryᴰ.HomᴰP f .Bif-RL-fuse = {!!}
  SETᴰ .Categoryᴰ.idᴰElt .N-ob = λ x x₂ z → z
  SETᴰ .Categoryᴰ.idᴰElt .N-hom = λ x y f x₂ → f x₂
  SETᴰ .Categoryᴰ.idᴰElt .N-nat = {!!}
  SETᴰ .Categoryᴰ.idᴰElt .N-ob-determines-N-hom = {!!}
  SETᴰ .Categoryᴰ.⋆ᴰBilinear f g .Bilinear.hom = λ z₁ z₂ x₁ z₃ → z₂ (f x₁) (z₁ x₁ z₃)
  SETᴰ .Categoryᴰ.⋆ᴰBilinear f g .Bilinear.natL = {!!}
  SETᴰ .Categoryᴰ.⋆ᴰBilinear f g .Bilinear.natM = {!!}
  SETᴰ .Categoryᴰ.⋆ᴰBilinear f g .Bilinear.natR = {!!}
  SETᴰ .Categoryᴰ.⋆ⱽᴰ≡ = {!!}
  SETᴰ .Categoryᴰ.⋆ᴰⱽ≡ = {!!}
  SETᴰ .Categoryᴰ.⋆Assocᴰ = {!!}
  SETᴰ .Categoryᴰ.isNormal = λ _ _ → idIsEquiv _

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  open import Cubical.Categories.Instances.Discrete.Eq
  import Cubical.Data.Equality as Eq
  private module P = PresheafNotation P
  -- A presheaf is a discrete opfibration
  Element : Categoryᴰ C ℓP ℓP ℓP
  Element .Categoryᴰ.vCat x = DiscreteCategory (P.p[ x ] , (isSet→isGroupoid P.isSetPsh))
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-ob px py = ((f P.⋆ py) Eq.≡ px) , {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-homL Eq.refl p = λ z → z
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-homR p Eq.refl = λ z → z
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-hom× Eq.refl Eq.refl = λ z → z
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L-id = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L-seq = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R-id = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R-seq = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-×-id = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-×-seq = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-L×-agree = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-R×-agree = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-LR-fuse = {!!}
  Element .Categoryᴰ.HomᴰP f .Bifunctor.Bif-RL-fuse = {!!}
  Element .Categoryᴰ.idᴰElt .N-ob = {!!}
  Element .Categoryᴰ.idᴰElt .N-hom _ _ Eq.refl = {!!}
  Element .Categoryᴰ.idᴰElt .N-nat = {!!}
  Element .Categoryᴰ.idᴰElt .N-ob-determines-N-hom = {!!}
  Element .Categoryᴰ.⋆ᴰBilinear = {!!}
  Element .Categoryᴰ.⋆ⱽᴰ≡ = {!!}
  Element .Categoryᴰ.⋆ᴰⱽ≡ = {!!}
  Element .Categoryᴰ.⋆Assocᴰ = {!!}
  Element .Categoryᴰ.isNormal = {!!}

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} where
  open import Cubical.Categories.Instances.Discrete.Eq
  import Cubical.Data.Equality as Eq
  private module P = PresheafNotation P

  ElementF : (α : PshHom P Q) → Functorⱽ (Element P) (Element Q)
  ElementF α .Functorᴰ.F-obⱽ .Functor.F-ob = α .PshHom.N-ob _
  ElementF α .Functorᴰ.F-obⱽ .Functor.F-hom Eq.refl = Eq.refl
  ElementF α .Functorᴰ.F-obⱽ .Functor.F-id = {!!}
  ElementF α .Functorᴰ.F-obⱽ .Functor.F-seq = {!!}
  -- TODO: naturality
  ElementF α .Functorᴰ.F-homᴰ f = {!!}

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ') (ℓPᴰ : Level) where
  import Cubical.Data.Equality as Eq
  open import Cubical.Categories.Instances.Sets
  open import Cubical.HITs.MappingCylinder.Base
  open Functor
  open Functorᴰ

  -- Intuition: a Presheafᴰ specifies
  --
  -- 1. For each x , xᴰ : Cᴰ.v[ x ] and p : P.p[ x ] a type Pᴰ.p[ p ][ xᴰ ] of "elements pᴰ of type xᴰ over p"
  -- 2. With *two* actions of composition:
  --    Vertical  composition: Given fⱽ : Cᴰ.vHom[ xᴰ' , xᴰ ]  we have fⱽ ⋆ⱽᴰ pᴰ : Pᴰ.p[ p ][ xᴰ ]
  --    Displayed composition: Given fᴰ : Cᴰ.Hom[ f ][ Γᴰ , xᴰ ]  we have fᴰ ⋆ᴰ pᴰ : Pᴰ.p[ f C.⋆ p ][ xᴰ ]
  -- 3. Satisfying every unit/associativity law you can think of.
  --
  CurriedPresheafᴰ : Type (ℓ-max
                           (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓP)) ℓCᴰ) ℓCⱽ)
                            ℓCᴰ')
                           (ℓ-suc ℓPᴰ))
  CurriedPresheafᴰ = Functorᴰ P (Cᴰ ^opᴰ) (SETᴰ ℓP ℓPᴰ)

  -- same as before I think
  UncurriedPresheafᴰ : Type (ℓ-max
                             (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCⱽ) ℓCᴰ')
                             (ℓ-suc ℓPᴰ))
  UncurriedPresheafᴰ = Presheaf (∫C (×ᴰ Cᴰ (Element P))) ℓPᴰ

  curryPshᴰ : UncurriedPresheafᴰ → CurriedPresheafᴰ
  curryPshᴰ Pᴰ .F-obⱽ {x} .F-ob xᴰ p = Pᴰ .F-ob (x , xᴰ , p)
  -- vertical composition
  curryPshᴰ Pᴰ .F-obⱽ {x} .F-hom {xᴰ}{xᴰ'} fⱽ p pᴰ = Pᴰ .F-hom (inl (Eq.refl , fⱽ , Eq.refl)) pᴰ
  curryPshᴰ Pᴰ .F-obⱽ {x} .F-id = {!!}
  curryPshᴰ Pᴰ .F-obⱽ {x} .F-seq = {!!}
  -- displayed composition
  curryPshᴰ Pᴰ .F-homᴰ {x} {y} f .Homomorphism.hom fᴰ p pᴰ = Pᴰ .F-hom (inr (f , fᴰ , Eq.refl)) pᴰ
  curryPshᴰ Pᴰ .F-homᴰ {x} {y} f .Homomorphism.natL = {!!}
  curryPshᴰ Pᴰ .F-homᴰ {x} {y} f .Homomorphism.natR = {!!}

  uncurryPshᴰ : CurriedPresheafᴰ → UncurriedPresheafᴰ
  uncurryPshᴰ Pᴰ .F-ob (x , xᴰ , p) = Pᴰ .F-obⱽ .F-ob xᴰ p
  -- vertical composition
  uncurryPshᴰ Pᴰ .F-hom (inl (Eq.refl , fⱽ , Eq.refl)) pᴰ = Pᴰ .F-obⱽ .F-hom fⱽ _ pᴰ
  -- displayed compoosition
  uncurryPshᴰ Pᴰ .F-hom (inr (f , fᴰ , Eq.refl)) pᴰ = Pᴰ .F-homᴰ f .Homomorphism.hom fᴰ _ pᴰ
  uncurryPshᴰ Pᴰ .F-hom (push a i) p = {!!}
  uncurryPshᴰ Pᴰ .F-id = {!!}
  uncurryPshᴰ Pᴰ .F-seq = {!!}

  -- These two proofs are done just enough to demonstrate that the two
  -- round trips are as definitionally well behaved as is really
  -- possible.
  curry-uncurry-sec : ∀ Pᴰ → uncurryPshᴰ (curryPshᴰ Pᴰ) ≡ Pᴰ
  curry-uncurry-sec Pᴰ i .F-ob = Pᴰ .F-ob
  curry-uncurry-sec Pᴰ i .F-hom (inl (Eq.refl , fⱽ , Eq.refl)) pᴰ = Pᴰ .F-hom (inl (Eq.refl , fⱽ , Eq.refl)) pᴰ
  curry-uncurry-sec Pᴰ i .F-hom (inr (f , fᴰ , Eq.refl)) pᴰ = Pᴰ .F-hom (inr (f , fᴰ , Eq.refl)) pᴰ
  curry-uncurry-sec Pᴰ i .F-hom (push a i₁) x₁ = {!!}
  curry-uncurry-sec Pᴰ i .F-id = {!!}
  curry-uncurry-sec Pᴰ i .F-seq = {!!}

  curry-uncurry-ret : ∀ Pᴰ → curryPshᴰ (uncurryPshᴰ Pᴰ) ≡ Pᴰ
  curry-uncurry-ret Pᴰ i .F-obⱽ {x} .F-ob = Pᴰ .F-obⱽ .F-ob
  curry-uncurry-ret Pᴰ i .F-obⱽ {x} .F-hom = Pᴰ .F-obⱽ .F-hom
  curry-uncurry-ret Pᴰ i .F-obⱽ {x} .F-id = {!!}
  curry-uncurry-ret Pᴰ i .F-obⱽ {x} .F-seq = {!!}
  curry-uncurry-ret Pᴰ i .F-homᴰ f .Homomorphism.hom = Pᴰ .F-homᴰ f .Homomorphism.hom
  curry-uncurry-ret Pᴰ i .F-homᴰ f .Homomorphism.natL = {!!}
  curry-uncurry-ret Pᴰ i .F-homᴰ f .Homomorphism.natR = {!!}

  Curried≅Uncurried : Iso CurriedPresheafᴰ UncurriedPresheafᴰ
  Curried≅Uncurried .Iso.fun = uncurryPshᴰ
  Curried≅Uncurried .Iso.inv = curryPshᴰ
  Curried≅Uncurried .Iso.sec = curry-uncurry-sec
  Curried≅Uncurried .Iso.ret = curry-uncurry-ret

  -- TODO: PshIsoᴰ/ⱽ and Yonedaᴰ/ⱽ
  -- TODO: Universal Properties: products, (op)cartesian lifts, exponentials, ∀, etc

  -- The benefit of the curried version: many constructions are just functor composition:
  -- 1. Reindexing along a natural transformation
  -- 2. Exponentiating by a locally representable presheaf
  -- 3. Universal quantifiers

module _ {C : Category ℓC ℓC'} {x : C .ob} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCⱽ ℓCᴰ') (xᴰ : Categoryᴰ.v[_] Cᴰ x)  where
  import Cubical.Data.Equality as Eq
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Instances.Sets.More
  open import Cubical.Categories.Instances.ExtraId
  open import Cubical.HITs.MappingCylinder.Base
  open Functor
  open Functorᴰ
  private module Cᴰ = Categoryᴰ Cᴰ
  -- There's something wrong here...
  --
  -- A vertical presheaf like this one should also have a notion of *vertical* element.
  [-][-,] : CurriedPresheafᴰ (C [-, x ]) Cᴰ {!!}
  [-][-,] .F-obⱽ .F-ob Γᴰ f = Cᴰ.Hom[ f ][ Γᴰ , xᴰ ] , Cᴰ.Het.Bif-ob Γᴰ xᴰ .snd
  -- ⋆ⱽᴰ
  [-][-,] .F-obⱽ .F-hom γⱽ f fᴰ = γⱽ Cᴰ.Het.⋆ᶜʳ fᴰ
  [-][-,] .F-obⱽ .F-id = {!!}
  [-][-,] .F-obⱽ .F-seq = {!!}
  -- ⋆ᴰ
  [-][-,] .F-homᴰ γ .Homomorphism.hom γᴰ f fᴰ = γᴰ Cᴰ.⋆ᴰ fᴰ
  [-][-,] .F-homᴰ γ .Homomorphism.natL = {!!}
  [-][-,] .F-homᴰ γ .Homomorphism.natR = {!!}

  [-][-,]Thick : CurriedPresheafᴰ (C [-, x ]Thick) Cᴰ {!!}
  [-][-,]Thick .F-obⱽ {.x} .F-ob Γᴰ (synId Eq.refl) = Lift ℓCᴰ' (Cᴰ.vHom[ Γᴰ , xᴰ ]) , {!!}
  [-][-,]Thick .F-obⱽ {Γ} .F-ob Γᴰ (semHom f) = Lift ℓCⱽ (Cᴰ.Hom[ f ][ Γᴰ , xᴰ ]) , {!!}
  [-][-,]Thick .F-obⱽ {Γ} .F-ob Γᴰ (synId≡id eq i) = {!!} -- requires Univalence currently
  [-][-,]Thick .F-obⱽ .F-hom fⱽ (synId Eq.refl) (lift gⱽ) = lift (fⱽ Cᴰ.vCat.⋆ gⱽ)
  [-][-,]Thick .F-obⱽ .F-hom fⱽ (semHom g) (lift gᴰ) = lift (fⱽ Cᴰ.Het.⋆ᶜʳ gᴰ)
  [-][-,]Thick .F-obⱽ .F-hom fⱽ (synId≡id eq i) = {!!}
  [-][-,]Thick .F-obⱽ .F-id = {!!}
  [-][-,]Thick .F-obⱽ .F-seq = {!!}
  [-][-,]Thick .F-homᴰ γ .Homomorphism.hom γᴰ (synId Eq.refl) (lift fⱽ) = lift (γᴰ Cᴰ.Het.⋆ʳᶜ fⱽ)
  [-][-,]Thick .F-homᴰ γ .Homomorphism.hom γᴰ (semHom f) (lift fᴰ) = lift (γᴰ Cᴰ.⋆ᴰ fᴰ)
  [-][-,]Thick .F-homᴰ γ .Homomorphism.hom γᴰ (synId≡id eq i) fᴰ = {!!}
  [-][-,]Thick .F-homᴰ γ .Homomorphism.natL = {!!}
  [-][-,]Thick .F-homᴰ γ .Homomorphism.natR = {!!}


-- a cartesian lift of f : C [ x , y ] and yᴰ : Cᴰ.v[ y ] is an object f*yᴰ : Cᴰ.v[ x ]
--
-- The spec then is a Pshᴰ (C [-, x ])
--
-- Cᴰf*yᴰ
