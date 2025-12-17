module Cubical.Categories.2Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

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
