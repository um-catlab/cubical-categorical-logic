module Cubical.Categories.2Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
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

    ⋆ⱽIdL : ∀ {x y} {f g : Hom₁[ x , y ]} (α : Hom₂[ f , g ])
          → id₂ ⋆ⱽ α ≡ α
    ⋆ⱽIdR : ∀ {x y} {f g : Hom₁[ x , y ]} (α : Hom₂[ f , g ])
          → α ⋆ⱽ id₂ ≡ α
    ⋆ⱽAssoc : ∀ {x y} {f g h k : Hom₁[ x , y ]}
              (α : Hom₂[ f , g ]) (β : Hom₂[ g , h ]) (γ : Hom₂[ h , k ])
            → (α ⋆ⱽ β) ⋆ⱽ γ ≡ α ⋆ⱽ (β ⋆ⱽ γ)

    ⋆ᴴIdL  : ∀ {x y} {f f' : Hom₁[ x , y ]} (α : Hom₂[ f , f' ]) →
      PathP (λ i → Hom₂[ ⋆₁IdL f i , ⋆₁IdL f' i ]) (id₂ ⋆ᴴ α) α
    ⋆ᴴIdR  : ∀ {x y} {f f' : Hom₁[ x , y ]} (α : Hom₂[ f , f' ]) →
      PathP (λ i → Hom₂[ ⋆₁IdR f i , ⋆₁IdR f' i ]) (α ⋆ᴴ id₂) α
    ⋆ᴴAssoc  : ∀ {x y z w}
      {f f' : Hom₁[ x , y ]} {g g' : Hom₁[ y , z ]} {h h' : Hom₁[ z , w ]}
      (α : Hom₂[ f , f' ]) (β : Hom₂[ g , g' ]) (γ : Hom₂[ h , h' ]) →
      PathP (λ i → Hom₂[ ⋆₁Assoc f g h i , ⋆₁Assoc f' g' h' i ])
        ((α ⋆ᴴ β) ⋆ᴴ γ) (α ⋆ᴴ β ⋆ᴴ γ)

    interchange : ∀ {x y z} {f g h : Hom₁[ x , y ]} {k l m : Hom₁[ y , z ]}
                  (α : Hom₂[ f , g ]) (β : Hom₂[ g , h ])
                  (γ : Hom₂[ k , l ]) (δ : Hom₂[ l , m ])
                → (α ⋆ⱽ β) ⋆ᴴ (γ ⋆ⱽ δ) ≡ (α ⋆ᴴ γ) ⋆ⱽ (β ⋆ᴴ δ)

    isGroupoidHom₁ : ∀ {x y} → isGroupoid Hom₁[ x , y ]
    isSetHom₂ : ∀ {x y} {f g : Hom₁[ x , y ]} → isSet (Hom₂[ f , g ])

  infixr 9 _⋆₁_
  infixr 9 _⋆ⱽ_
  infixr 9 _⋆ᴴ_

  ⟨_⟩⋆₁⟨_⟩ : ∀ {x y z} {f f' : Hom₁[ x , y ]} {g g' : Hom₁[ y , z ]} →
    f ≡ f' → g ≡ g' → f ⋆₁ g ≡ f' ⋆₁ g'
  ⟨ f≡ ⟩⋆₁⟨ g≡ ⟩ = cong₂ _⋆₁_ f≡ g≡

  ⟨_⟩⋆ⱽ⟨_⟩ : ∀ {x y} {f g h : Hom₁[ x , y ]} →
    {α α' : Hom₂[ f , g ]} {β β' : Hom₂[ g , h ]} →
     α ≡ α' → β ≡ β' → α ⋆ⱽ β ≡ α' ⋆ⱽ β'
  ⟨ α≡ ⟩⋆ⱽ⟨ β≡ ⟩ = cong₂ _⋆ⱽ_ α≡ β≡

  ⟨_⟩⋆ᴴ⟨_⟩ : ∀ {x y z} {f f' : Hom₁[ x , y ]} {g g' : Hom₁[ y , z ]} →
      {α α' : Hom₂[ f , f' ]} {β β' : Hom₂[ g , g' ]} →
      α ≡ α' → β ≡ β' → α ⋆ᴴ β ≡ α' ⋆ᴴ β'
  ⟨ α≡ ⟩⋆ᴴ⟨ β≡ ⟩ = cong₂ _⋆ᴴ_ α≡ β≡

  module 2CatReasoning {x y} =
    Reasoning (Hom₁[ x , y ] × Hom₁[ x , y ]) (λ (f , g) → Hom₂[ f , g ])
  open 2CatReasoning public

  ∫⋆ᴴIdL  : ∀ {x y} {f f' : Hom₁[ x , y ]} (α : Hom₂[ f , f' ]) →
    id₂ ⋆ᴴ α ∫≡ α
  ∫⋆ᴴIdL α = ΣPathP (ΣPathP (⋆₁IdL _ , ⋆₁IdL _) , (⋆ᴴIdL α))

  ∫⋆ᴴIdR  : ∀ {x y} {f f' : Hom₁[ x , y ]} (α : Hom₂[ f , f' ]) →
    α ⋆ᴴ id₂ ∫≡ α
  ∫⋆ᴴIdR α = ΣPathP (ΣPathP (⋆₁IdR _ , ⋆₁IdR _) , (⋆ᴴIdR α))

  ∫⋆ᴴAssoc  : ∀ {x y z w}
    {f f' : Hom₁[ x , y ]} {g g' : Hom₁[ y , z ]} {h h' : Hom₁[ z , w ]}
    (α : Hom₂[ f , f' ]) (β : Hom₂[ g , g' ]) (γ : Hom₂[ h , h' ]) →
    (α ⋆ᴴ β) ⋆ᴴ γ ∫≡ α ⋆ᴴ β ⋆ᴴ γ
  ∫⋆ᴴAssoc α β γ =
    ΣPathP ((ΣPathP ((⋆₁Assoc _ _ _) , ⋆₁Assoc _ _ _)) , (⋆ᴴAssoc α β γ))


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
  CAT .⋆ⱽIdL {y = D} α =
    makeNatTransPath (funExt λ _ → D.⋆IdL _ )
    where module D = GroupoidObjectsCategory D
  CAT .⋆ⱽIdR {y = D} α =
    makeNatTransPath (funExt λ _ → D.⋆IdR _ )
    where module D = GroupoidObjectsCategory D
  CAT .⋆ⱽAssoc {y = D} _ _ _ =
    makeNatTransPath (funExt λ _ → D.⋆Assoc _ _ _ )
    where module D = GroupoidObjectsCategory D
  CAT .⋆ᴴIdL {y = D} {f = F} α =
    makeNatTransPathP _ _ (funExt λ _ → cong₂ D._⋆_ (F .F-id) refl ∙ D.⋆IdL _)
    where module D = GroupoidObjectsCategory D
  CAT .⋆ᴴIdR {y = D} α =
    makeNatTransPathP _ _ (funExt λ _ → D.⋆IdR _)
    where module D = GroupoidObjectsCategory D
  CAT .⋆ᴴAssoc {w = D} {f = F} {g = G} {h = H} _ _ _ =
    makeNatTransPathP _ _
      (funExt λ _ →
        D.⟨ H .F-seq _ _ ⟩⋆⟨ refl ⟩
        ∙ D.⋆Assoc _ _ _
      )
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
  Cat→2Cat .Hom₂[_,_] f g = f ≡ g
  Cat→2Cat .id₁ = C.id
  Cat→2Cat .id₂ = refl
  Cat→2Cat ._⋆₁_ = C._⋆_
  Cat→2Cat ._⋆ⱽ_ = _∙_
  Cat→2Cat ._⋆ᴴ_ = C.⟨_⟩⋆⟨_⟩
  Cat→2Cat .⋆₁IdL = C.⋆IdL
  Cat→2Cat .⋆₁IdR = C.⋆IdR
  Cat→2Cat .⋆₁Assoc = C.⋆Assoc
  Cat→2Cat .⋆ⱽIdL _ = C.isSetHom _ _ _ _
  Cat→2Cat .⋆ⱽIdR _ = C.isSetHom _ _ _ _
  Cat→2Cat .⋆ⱽAssoc _ _ _ = C.isSetHom _ _ _ _
  Cat→2Cat .⋆ᴴIdL _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
  Cat→2Cat .⋆ᴴIdR _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
  Cat→2Cat .⋆ᴴAssoc _ _ _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
  Cat→2Cat .interchange  _ _ _ _ = C.isSetHom _ _ _ _
  Cat→2Cat .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
  Cat→2Cat .isSetHom₂ = isSet→isGroupoid C.isSetHom _ _

--   Cat→2CatEq : 2Category _ _ _
--   Cat→2CatEq .ob = C.ob
--   Cat→2CatEq .Hom₁[_,_] = C.Hom[_,_]
--   Cat→2CatEq .Hom₂[_,_] f g = f Eq.≡ g
--   Cat→2CatEq .id₁ = C.id
--   Cat→2CatEq .id₂ = Eq.refl
--   Cat→2CatEq ._⋆₁_ = C._⋆_
--   Cat→2CatEq ._⋆ⱽ_ = Eq._∙_
--   Cat→2CatEq ._⋆ᴴ_ Eq.refl Eq.refl = Eq.refl
--   Cat→2CatEq .⋆₁IdL = C.⋆IdL
--   Cat→2CatEq .⋆₁IdR = C.⋆IdR
--   Cat→2CatEq .⋆₁Assoc = C.⋆Assoc
--   Cat→2CatEq .⋆ⱽIdL _ = refl
--   Cat→2CatEq .⋆ⱽIdR Eq.refl = refl
--   Cat→2CatEq .⋆ⱽAssoc Eq.refl Eq.refl Eq.refl = refl
--   Cat→2CatEq .interchange Eq.refl Eq.refl Eq.refl Eq.refl = refl
--   Cat→2CatEq .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
--   Cat→2CatEq .isSetHom₂ = isSetRetract Eq.eqToPath Eq.pathToEq
--     Eq.pathToEq-eqToPath (isSet→isGroupoid C.isSetHom _ _)

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
  _^op2 .⋆ⱽIdL = C.⋆ⱽIdR
  _^op2 .⋆ⱽIdR = C.⋆ⱽIdL
  _^op2 .⋆ⱽAssoc _ _ _ = sym $ C.⋆ⱽAssoc _ _ _
  _^op2 .⋆ᴴIdL = C.⋆ᴴIdR
  _^op2 .⋆ᴴIdR = C.⋆ᴴIdL
  _^op2 .⋆ᴴAssoc _ _ _ = symP $ C.⋆ᴴAssoc _ _ _
  _^op2 .interchange = λ α β γ δ → C.interchange δ γ β α
  _^op2 .isGroupoidHom₁ = C.isGroupoidHom₁
  _^op2 .isSetHom₂ = C.isSetHom₂
