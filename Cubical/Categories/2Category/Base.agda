module Cubical.Categories.2Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓ ℓ' ℓ'' : Level

record 2Category ℓ ℓ' ℓ'' :
  Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where
  no-eta-equality
  field
    ob : Type ℓ
    Hom₁[_,_] : ob → ob → Type ℓ'
    Hom₂[_,_] : ∀ {x y} → Hom₁[ x , y ] → Hom₁[ x , y ] → Type ℓ''

    id₁   : ∀ {x} → Hom₁[ x , x ]
    id₂   : ∀ {x y} {f : Hom₁[ x , y ]} → Hom₂[ f , f ]

    _⋆₁_  : ∀ {x y z} (f : Hom₁[ x , y ]) (g : Hom₁[ y , z ]) → Hom₁[ x , z ]
    _⋆ⱽ_  : ∀ {x y} {f g h : Hom₁[ x , y ]} →
      Hom₂[ f , g ] → Hom₂[ g , h ] → Hom₂[ f , h ]
    _⋆ᴴ_  : ∀ {x y z} {f f' : Hom₁[ x , y ]} {g g' : Hom₁[ y , z ]} →
      Hom₂[ f , f' ] → Hom₂[ g , g' ] → Hom₂[ (f ⋆₁ g) , (f' ⋆₁ g') ]

    ⋆₁IdL : ∀ {x y} (f : Hom₁[ x , y ]) → id₁ ⋆₁ f ≡ f
    ⋆₁IdR : ∀ {x y} (f : Hom₁[ x , y ]) → f ⋆₁ id₁ ≡ f
    ⋆₁Assoc : ∀ {x y z w} (f : Hom₁[ x , y ]) (g : Hom₁[ y , z ]) (h : Hom₁[ z , w ])
           → (f ⋆₁ g) ⋆₁ h ≡ f ⋆₁ (g ⋆₁ h)

    ⋆₂IdL : ∀ {x y} {f g : Hom₁[ x , y ]} (α : Hom₂[ f , g ])
          → id₂ ⋆ⱽ α ≡ α
    ⋆₂IdR : ∀ {x y} {f g : Hom₁[ x , y ]} (α : Hom₂[ f , g ])
          → α ⋆ⱽ id₂ ≡ α
    ⋆₂Assoc : ∀ {x y} {f g h k : Hom₁[ x , y ]}
              (α : Hom₂[ f , g ]) (β : Hom₂[ g , h ]) (γ : Hom₂[ h , k ])
            → (α ⋆ⱽ β) ⋆ⱽ γ ≡ α ⋆ⱽ (β ⋆ⱽ γ)

    interchange : ∀ {x y z} {f g h : Hom₁[ x , y ]} {k l m : Hom₁[ y , z ]}
                  (α : Hom₂[ f , g ]) (β : Hom₂[ g , h ])
                  (γ : Hom₂[ k , l ]) (δ : Hom₂[ l , m ])
                → (α ⋆ⱽ β) ⋆ᴴ (γ ⋆ⱽ δ) ≡ (α ⋆ᴴ γ) ⋆ⱽ (β ⋆ᴴ δ)

    isGroupoidHom₁ : ∀ {x y} → isGroupoid Hom₁[ x , y ]
    isSetHom₂ : ∀ {x y} {f g : Hom₁[ x , y ]} → isSet (Hom₂[ f , g ])

  infixr 9 _⋆₁_
  infixr 9 _⋆ⱽ_
  infixr 9 _⋆ᴴ_

open 2Category
open NatTrans
open Functor
open Category

record GroupoidObjectsCategory ℓC ℓC' : Type (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) where
  field
     cat : Category ℓC ℓC'
     groupoid-obs : isGroupoid (cat .ob)
  open Category cat public

open GroupoidObjectsCategory

module _ {ℓC ℓC'} where
  CAT : 2Category _ _ _
  CAT .ob = GroupoidObjectsCategory ℓC ℓC'
  CAT .Hom₁[_,_] C D = Functor (C .cat) (D .cat)
  CAT .Hom₂[_,_] = NatTrans
  CAT .id₁ = Id
  CAT .id₂ = idTrans _
  CAT ._⋆₁_ F G = G ∘F F
  CAT ._⋆ⱽ_ = seqTrans
  CAT ._⋆ᴴ_ α β = whiskerTrans β α
  CAT .⋆₁IdL F = F-lUnit
  CAT .⋆₁IdR F = F-rUnit
  CAT .⋆₁Assoc _ _ _ = F-assoc
  CAT .⋆₂IdL {y = D} α =
    makeNatTransPath (funExt λ _ → D.⋆IdL _ )
    where module D = GroupoidObjectsCategory D
  CAT .⋆₂IdR {y = D} α =
    makeNatTransPath (funExt λ _ → D.⋆IdR _ )
    where module D = GroupoidObjectsCategory D
  CAT .⋆₂Assoc {y = D} _ _ _ =
    makeNatTransPath (funExt λ _ → D.⋆Assoc _ _ _ )
    where module D = GroupoidObjectsCategory D
  CAT .interchange {z = D}{k = k} α β γ δ =
    makeNatTransPath (funExt λ _ →
      (sym $ D.⋆Assoc _ _ _)
      ∙ D.⟨ D.⟨ k .F-seq _ _ ⟩⋆⟨ refl ⟩
                ∙ D.⋆Assoc _ _ _
                ∙ D.⟨ refl ⟩⋆⟨ N-hom γ (N-ob β _) ⟩
                ∙ (sym $ D.⋆Assoc _ _ _)
          ⟩⋆⟨ refl ⟩
      ∙ D.⋆Assoc _ _ _)
    where module D = GroupoidObjectsCategory D
  CAT .isGroupoidHom₁ {y = D} = isOfHLevelFunctor 1 D.groupoid-obs
    where module D = GroupoidObjectsCategory D
  CAT .isSetHom₂ = isSetNatTrans

module _ {ℓC ℓC'} (C : Category ℓC ℓC') where
  private
    module C = Category C

  Cat→2Cat : 2Category _ _ _
  Cat→2Cat .ob = C.ob
  Cat→2Cat .Hom₁[_,_] = C.Hom[_,_]
  Cat→2Cat .Hom₂[_,_] _ _ = Unit
  Cat→2Cat .id₁ = C.id
  Cat→2Cat .id₂ = tt
  Cat→2Cat ._⋆₁_ = C._⋆_
  Cat→2Cat ._⋆ⱽ_ = λ _ _ → tt
  Cat→2Cat ._⋆ᴴ_ = λ _ _ → tt
  Cat→2Cat .⋆₁IdL = C.⋆IdL
  Cat→2Cat .⋆₁IdR = C.⋆IdR
  Cat→2Cat .⋆₁Assoc = C.⋆Assoc
  Cat→2Cat .⋆₂IdL = λ _ → refl
  Cat→2Cat .⋆₂IdR = λ _ → refl
  Cat→2Cat .⋆₂Assoc = λ _ _ _ → refl
  Cat→2Cat .interchange = λ _ _ _ _ → refl
  Cat→2Cat .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
  Cat→2Cat .isSetHom₂ = isSetUnit

module _ {ℓC ℓC' ℓC''} (C : 2Category ℓC ℓC' ℓC'') where
  private
    module C = 2Category C
  _^op2 : 2Category ℓC ℓC' ℓC''
  _^op2 .ob = C.ob
  _^op2 .Hom₁[_,_] x y = C.Hom₁[ y , x ]
  _^op2 .Hom₂[_,_] f g = C.Hom₂[ g , f ]
  _^op2 .id₁ = C.id₁
  _^op2 .id₂ = C.id₂
  _^op2 ._⋆₁_ = λ f g → g C.⋆₁ f
  _^op2 ._⋆ⱽ_ = λ z z₁ → z₁ C.⋆ⱽ z
  _^op2 ._⋆ᴴ_ = λ z₁ z₂ → z₂ C.⋆ᴴ z₁
  _^op2 .⋆₁IdL = C.⋆₁IdR
  _^op2 .⋆₁IdR = C.⋆₁IdL
  _^op2 .⋆₁Assoc _ _ _ = sym $ C.⋆₁Assoc _ _ _
  _^op2 .⋆₂IdL = C.⋆₂IdR
  _^op2 .⋆₂IdR = C.⋆₂IdL
  _^op2 .⋆₂Assoc _ _ _ = sym $ C.⋆₂Assoc _ _ _
  _^op2 .interchange = λ α β γ δ → C.interchange δ γ β α
  _^op2 .isGroupoidHom₁ = C.isGroupoidHom₁
  _^op2 .isSetHom₂ = C.isSetHom₂
