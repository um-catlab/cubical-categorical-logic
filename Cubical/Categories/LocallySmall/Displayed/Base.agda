module Cubical.Categories.LocallySmall.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Σω

-- The key thing we need is to be able to iterate the ∫C construction
module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C
  -- Hom-ℓᴰ can't depend on f without making _≡[_]_ ill typed
  record Categoryᴰ (ob[_] : Cob → Typeω)(Hom-ℓᴰ : ∀ x y (xᴰ : ob[ x ])(yᴰ : ob[ y ]) → Level)
    : Typeω where
    no-eta-equality
    field
      Hom[_][_,_] : ∀ {x y}(f : C.Hom[ x , y ])(xᴰ : ob[ x ])(yᴰ : ob[ y ])
        → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)
      idᴰ : ∀ {x} {xᴰ : ob[ x ]} → Hom[ C.id ][ xᴰ , xᴰ ]
      _⋆ᴰ_ : ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]} {xᴰ yᴰ zᴰ}
        → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f C.⋆ g ][ xᴰ , zᴰ ]
    infixr 9 _⋆ᴰ_

    _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
      → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (p : f ≡ g) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
      → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)
    _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

    infix 2 _≡[_]_

    ∫Hom[_,_] : (x y : Σω Cob ob[_]) → Type _
    ∫Hom[ xxᴰ , yyᴰ ] =
      Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
      Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]

    _∫≡_ :  ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
      → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
      → Type _
    fᴰ ∫≡ gᴰ = Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ)
    infix 2 _∫≡_

    field
      ⋆IdLᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → idᴰ ⋆ᴰ fᴰ ∫≡ fᴰ
      ⋆IdRᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → fᴰ ⋆ᴰ idᴰ ∫≡ fᴰ
      ⋆Assocᴰ : ∀ {x y z w} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}  {h : C.Hom[ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
        → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ∫≡ fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
      isSetHomᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

    -- Reindexing displayed morphisms along an equality in the base
    reind : {x y : Cob}{f g : C.Hom[ x , y ]}
      {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
      (p : f ≡ g)
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → Hom[ g ][ xᴰ , yᴰ ]
    reind = subst Hom[_][ _ , _ ]

    _⋆ⱽᴰ_ : ∀ {x y} {xᴰ xᴰ' yᴰ}{g : C.Hom[ x , y ]}
      (fⱽ : Hom[ C.id ][ xᴰ , xᴰ' ])
      (gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
      → Hom[ g ][ xᴰ , yᴰ ]
    fⱽ ⋆ⱽᴰ gᴰ = reind (C.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

    _⋆ⱽ_ : ∀ {x} {xᴰ xᴰ' xᴰ''}
      (fⱽ : Hom[ C.id {x} ][ xᴰ , xᴰ' ])
      (gⱽ : Hom[ C.id ][ xᴰ' , xᴰ'' ])
      → Hom[ C.id ][ xᴰ , xᴰ'' ]
    fⱽ ⋆ⱽ gⱽ = fⱽ ⋆ⱽᴰ gⱽ

    _⋆ᴰⱽ_ : ∀ {x y} {xᴰ yᴰ yᴰ'}{f : C.Hom[ x , y ]}
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      (gᴰ : Hom[ C.id ][ yᴰ , yᴰ' ])
      → Hom[ f ][ xᴰ , yᴰ' ]
    fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

    ≡in : {x y : Cob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
      {p : f ≡ g}
      → (fᴰ ≡[ p ] gᴰ)
      → fᴰ ∫≡ gᴰ
    ≡in = λ pᴰ → ΣPathP (_ , pᴰ)
    opaque
      ⋆IdLᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
        → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → idᴰ ⋆ᴰ fᴰ ∫≡ fᴰ
      ⋆IdLᴰᴰ fᴰ = ⋆IdLᴰ fᴰ

      ⋆IdRᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
        → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ])
            (_ , (fᴰ ⋆ᴰ idᴰ))
            (_ , fᴰ)
      ⋆IdRᴰᴰ fᴰ = ⋆IdRᴰ fᴰ

      ⋆Assocᴰᴰᴰ : ∀ {w x y z wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        {g : C.Hom[ x , y ]}
        {h : C.Hom[ y , z ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ)
            (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ))
      ⋆Assocᴰᴰᴰ fᴰ gᴰ hᴰ = ⋆Assocᴰ fᴰ gᴰ hᴰ

      isSetDepHomᴰ : ∀ {x y xᴰ yᴰ} →
        isSetDep (λ (f : C.Hom[ x , y ]) → Hom[ f ][ xᴰ , yᴰ ])
      isSetDepHomᴰ = isSet→isSetDep (λ f → isSetHomᴰ)

      isSetHomᴰ' : ∀ {x y}{xᴰ}{yᴰ}
        {f g : C.Hom[ x , y ]} {p q : f ≡ g}
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (pᴰ : fᴰ ≡[ p ] gᴰ )
        (qᴰ : fᴰ ≡[ q ] gᴰ )
        → ∀ i j → Hom[  C.isSetHom f g p q i j ][ xᴰ , yᴰ ]
      isSetHomᴰ' fᴰ gᴰ pᴰ qᴰ i j = isSetDepHomᴰ fᴰ gᴰ pᴰ qᴰ (C.isSetHom _ _ _ _) i j

      ≡out : {x y : Cob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
        {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
        → (ppᴰ : Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ))
        → (fᴰ ≡[ fst (PathPΣ ppᴰ) ] gᴰ)
      ≡out e = snd (PathPΣ e)

      rectify : {x y : Cob}{f g : C.Hom[ x , y ]}{p p' : f ≡ g}
        {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
        {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
        → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
      rectify {fᴰ = fᴰ}{gᴰ} pᴰ = subst (fᴰ ≡[_] gᴰ) (C.isSetHom _ _ _ _) pᴰ

      reind-filler : {x y : Cob}{f g : C.Hom[ x , y ]}
        {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        (p : f ≡ g)
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (f , fᴰ) (g , reind p fᴰ)
      reind-filler p fᴰ = ΣPathP (p , subst-filler Hom[_][ _ , _ ] p fᴰ)

      reind-cong : ∀ {x y xᴰ yᴰ}{f f' g g' : C.Hom[ x , y ]}
        {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
        {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
        (p : f ≡ f')
        (q : g ≡ g')
        → Path ∫Hom[ _ , _ ]
            (_ , fᴰ)
            (_ , gᴰ)
        → Path ∫Hom[ _ , _ ]
            (_ , reind p fᴰ)
            (_ , reind q gᴰ)
      reind-cong p q fᴰ≡gᴰ = sym (reind-filler _ _) ∙ fᴰ≡gᴰ ∙ reind-filler _ _

    -- TODO move to LocallySmall.Constructions?
    ∫C : Category (Σω[ x ∈ Cob ] ob[ x ]) _
    ∫C .Hom[_,_] = ∫Hom[_,_]
    ∫C .id = _ , idᴰ
    ∫C ._⋆_ ffᴰ ggᴰ = _ , (ffᴰ .snd ⋆ᴰ ggᴰ .snd)
    ∫C .⋆IdL ffᴰ = ⋆IdLᴰᴰ _
    ∫C .⋆IdR ffᴰ = ⋆IdRᴰᴰ _
    ∫C .⋆Assoc ffᴰ ggᴰ hhᴰ = ⋆Assocᴰᴰᴰ _ _ _
    ∫C .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

    private
      module ∫C = CategoryNotation ∫C
    opaque
      ⋆IdLⱽᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
        → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → idᴰ ⋆ⱽᴰ fᴰ ∫≡ fᴰ
      ⋆IdLⱽᴰ fᴰ = sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

      ⋆IdLⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → idᴰ ⋆ⱽ fⱽ ∫≡ fⱽ
      ⋆IdLⱽⱽ = ⋆IdLⱽᴰ

      ⋆IdLᴰⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → idᴰ ⋆ᴰⱽ fⱽ ∫≡ fⱽ
      ⋆IdLᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

      ⋆IdRᴰⱽ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}(fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → fᴰ ⋆ᴰⱽ idᴰ ∫≡ fᴰ
      ⋆IdRᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

      ⋆IdRⱽᴰ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → fⱽ ⋆ⱽᴰ idᴰ ∫≡ fⱽ
      ⋆IdRⱽᴰ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

      ⋆IdRⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → fⱽ ⋆ⱽ idᴰ ∫≡ fⱽ
      ⋆IdRⱽⱽ fⱽ = ⋆IdRⱽᴰ fⱽ

      ⋆Assocⱽᴰᴰ : ∀ {x y z wᴰ xᴰ yᴰ zᴰ}
        {g : C.Hom[ x , y ]}
        {h : C.Hom[ y , z ]}
        (fⱽ : Hom[ C.id {x} ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ ∫≡ fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ)
      ⋆Assocⱽᴰᴰ _ _ _ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ reind-filler _ _

      ⋆Assocᴰⱽᴰ : ∀ {w x z wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        {h : C.Hom[ x , z ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ)
            (_ , fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
      ⋆Assocᴰⱽᴰ fᴰ gⱽ hᴰ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

      ⋆Assocᴰᴰⱽ : ∀ {w x y wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        {g : C.Hom[ x , y ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰⱽ hⱽ)
            (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰⱽ hⱽ))
      ⋆Assocᴰᴰⱽ fᴰ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

      ⋆Assocⱽⱽᴰ : ∀ {y z wᴰ xᴰ yᴰ zᴰ}
        {h : C.Hom[ y , z ]}
        (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ)
            (_ , fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
      ⋆Assocⱽⱽᴰ fⱽ gⱽ hᴰ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocⱽᴰⱽ : ∀ {x y wᴰ xᴰ yᴰ zᴰ}
        {g : C.Hom[ x , y ]}
        (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ)
            (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
      ⋆Assocⱽᴰⱽ fⱽ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocᴰⱽⱽ : ∀ {w x wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ)
            (_ , fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
      ⋆Assocᴰⱽⱽ fᴰ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocⱽⱽⱽ : ∀ {x wᴰ xᴰ yᴰ zᴰ}
        (fⱽ : Hom[ C .id {x} ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C .id ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C .id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽ hⱽ)
            (_ , fⱽ ⋆ⱽ (gⱽ ⋆ⱽ hⱽ))
      ⋆Assocⱽⱽⱽ fⱽ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

    v[_] : (x : Cob) → Category ob[ x ] (Hom-ℓᴰ x x)
    v[ x ] .Hom[_,_] = Hom[ C.id ][_,_]
    v[ x ] .id = idᴰ
    v[ x ] ._⋆_ fⱽ gⱽ = fⱽ ⋆ⱽ gⱽ
    v[ x ] .⋆IdL fⱽ = rectify $ ≡out $ ⋆IdLⱽⱽ _
    v[ x ] .⋆IdR fⱽ = rectify $ ≡out $ ⋆IdRⱽⱽ _
    v[ x ] .⋆Assoc fⱽ gⱽ hⱽ = rectify $ ≡out $ ⋆Assocⱽⱽⱽ _ _ _
    v[ x ] .isSetHom = isSetHomᴰ

    module Cⱽ {x : Cob} = Category (v[ x ])
    open ∫C public

open Categoryᴰ

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
   private
     module Cᴰ = Categoryᴰ Cᴰ
   _^opᴰ : Categoryᴰ (C ^op) Cobᴰ λ x y xᴰ yᴰ → CHom-ℓᴰ y x yᴰ xᴰ
   _^opᴰ .Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ yᴰ , xᴰ ]
   _^opᴰ .idᴰ = Cᴰ.idᴰ
   _^opᴰ ._⋆ᴰ_ fᴰ gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
   _^opᴰ .⋆IdLᴰ = Cᴰ.⋆IdRᴰ
   _^opᴰ .⋆IdRᴰ = Cᴰ.⋆IdLᴰ
   _^opᴰ .⋆Assocᴰ _ _ _ = sym (Cᴰ.⋆Assocᴰ _ _ _ )
   _^opᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

-- Displayed categories whose fibers are *small* categories.
-- This means:
-- 1. The type of displayed objects over any fixed object is small
-- 2. The type of displayed hom sets is small and the level only
-- depends on the base objects.
module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C
  module _ (obᴰ-ℓ : Cob → Level) (obᴰ : ∀ x → Type (obᴰ-ℓ x))
    (Homᴰ-ℓ : ∀ (x y : Cob) → Level) where
    SmallFibersCategoryᴰ : Typeω
    SmallFibersCategoryᴰ = Categoryᴰ C (λ x → Liftω (obᴰ x)) λ x y _ _ → Homᴰ-ℓ x y

module _ {C : Category Cob CHom-ℓ}
  {Cᴰ-ℓ}{Cobᴰ}{CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  SmallFiber : (x : Cob) → Small.Category (Cᴰ-ℓ x) (CHom-ℓᴰ x x)
  SmallFiber x = SmallLocallySmallCategory→SmallCategory ((liftω (Cobᴰ x)) , Cᴰ.v[ x ])

module _ ((Cob , C) : SmallCategory ℓC ℓC') ℓCᴰ ℓCᴰ' where
  private
    module C = Category C

  SmallCategoryᴰ : Typeω
  SmallCategoryᴰ =
    Σω[ (liftω obᴰ) ∈ Liftω (Cob .Liftω.lowerω → Type ℓCᴰ) ]
      Categoryᴰ C (λ c → Liftω (obᴰ (c .Liftω.lowerω)))
        λ _ _ _ _ → ℓCᴰ'
