module Cubical.Categories.2Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓ ℓ' ℓ'' ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' ℓE ℓE' ℓE'' : Level

record LaxFunctor (C : 2Category ℓC ℓC' ℓC'') (D : 2Category ℓD ℓD' ℓD'') :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD''))
    where
  no-eta-equality

  private
    module C = 2Category C
    module D = 2Category D

  field
    F₀ : C.ob → D.ob
    F₁ : ∀ {x y} → C.Hom₁[ x , y ] → D.Hom₁[ F₀ x , F₀ y ]
    F₂ : ∀ {x y} {f g : C.Hom₁[ x , y ]}
       → C.Hom₂[ f , g ] → D.Hom₂[ F₁ f , F₁ g ]

    F-id : ∀ {x} → D.Hom₂[ D.id₁ , F₁ (C.id₁ {x}) ]

    F-seq : ∀ {x y z} (f : C.Hom₁[ x , y ]) (g : C.Hom₁[ y , z ])
          → D.Hom₂[ (F₁ f) D.⋆₁ (F₁ g) , F₁ (f C.⋆₁ g) ]

    F-id₂ : ∀ {x y} {f : C.Hom₁[ x , y ]}
          → F₂ (C.id₂ {f = f}) ≡ D.id₂ {f = F₁ f}

    F-seqⱽ : ∀ {x y} {f g h : C.Hom₁[ x , y ]}
             (α : C.Hom₂[ f , g ]) (β : C.Hom₂[ g , h ])
           → F₂ (α C.⋆ⱽ β) ≡ (F₂ α) D.⋆ⱽ (F₂ β)

    F-seqᴴ : ∀ {x y z} {f f' : C.Hom₁[ x , y ]} {g g' : C.Hom₁[ y , z ]}
             (α : C.Hom₂[ f , f' ]) (β : C.Hom₂[ g , g' ])
           → (F-seq f g) D.⋆ⱽ F₂ (α C.⋆ᴴ β)
             ≡ ((F₂ α) D.⋆ᴴ (F₂ β)) D.⋆ⱽ (F-seq f' g')

    F-unitality-l : ∀ {x y} (f : C.Hom₁[ x , y ])
                  → PathP (λ i → D.Hom₂[ D.⋆₁IdL (F₁ f) i , F₁ (C.⋆₁IdL f i) ])
                          ((F-id D.⋆ᴴ D.id₂) D.⋆ⱽ (F-seq C.id₁ f))
                          (F₂ C.id₂)

    F-unitality-r : ∀ {x y} (f : C.Hom₁[ x , y ])
                  → PathP (λ i → D.Hom₂[ D.⋆₁IdR (F₁ f) i , F₁ (C.⋆₁IdR f i) ])
                          ((D.id₂ D.⋆ᴴ F-id) D.⋆ⱽ (F-seq f C.id₁))
                          (F₂ C.id₂)

    F-associativity : ∀ {w x y z} (f : C.Hom₁[ w , x ])
                        (g : C.Hom₁[ x , y ]) (h : C.Hom₁[ y , z ])
                    → PathP (λ i → D.Hom₂[ D.⋆₁Assoc (F₁ f) (F₁ g) (F₁ h) i
                                         , F₁ (C.⋆₁Assoc f g h i) ])
                            ((F-seq f g D.⋆ᴴ D.id₂) D.⋆ⱽ F-seq (f C.⋆₁ g) h)
                            ((D.id₂ D.⋆ᴴ (F-seq g h)) D.⋆ⱽ F-seq f (g C.⋆₁ h))

open 2Category
module _ (C : 2Category ℓ ℓ' ℓ'') where
  private module C = 2Category C
  record isIso2Cell {x y : C.ob}
    {f g : C.Hom₁[ x , y ]} (α : C.Hom₂[ f , g ]) : Type ℓ'' where
    field
      inv : C.Hom₂[ g , f ]
      sec : α C.⋆ⱽ inv ≡ C.id₂
      ret : inv C.⋆ⱽ α ≡ C.id₂

record isPseudo {C : 2Category ℓC ℓC' ℓC''} {D : 2Category ℓD ℓD' ℓD''}
                (F : LaxFunctor C D) :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD'')) where
  private
    module F = LaxFunctor F
    module C = 2Category C
    module D = 2Category D
  field
    F-id-iso : ∀ {x} → isIso2Cell D (F.F-id {x})
    F-seq-iso : ∀ {x y z} (f : C.Hom₁[ x , y ]) (g : C.Hom₁[ y , z ])
              → isIso2Cell D (F.F-seq f g)

record PseudoFunctor (C : 2Category ℓC ℓC' ℓC'') (D : 2Category ℓD ℓD' ℓD'') :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD'')) where
  field
    lax : LaxFunctor C D
    pseudo : isPseudo lax
  open LaxFunctor lax public

open LaxFunctor

module _
  {C : 2Category ℓC ℓC' ℓC''}
  {D : 2Category ℓD ℓD' ℓD''}
  {E : 2Category ℓE ℓE' ℓE''}
  (F : LaxFunctor C D)
  (G : LaxFunctor D E)
  where

  private
    module C = 2Category C
    module D = 2Category D
    module E = 2Category E
    module F = LaxFunctor F
    module G = LaxFunctor G

  seqLaxFunctor : LaxFunctor C E
  seqLaxFunctor .F₀ = λ z → G.F₀ (F.F₀ z)
  seqLaxFunctor .F₁ = λ z → G.F₁ (F.F₁ z)
  seqLaxFunctor .F₂ = λ z → G.F₂ (F.F₂ z)
  seqLaxFunctor .F-id = G.F-id E.⋆ⱽ G.F₂ F.F-id
  seqLaxFunctor .F-seq = λ f g → G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ⱽ G.F₂ (F.F-seq f g)
  seqLaxFunctor .F-id₂ = cong G.F₂ F.F-id₂ ∙ G.F-id₂
  seqLaxFunctor .F-seqⱽ α β =
    cong G.F₂ (F.F-seqⱽ α β)
    ∙ G.F-seqⱽ (F.F₂ α) (F.F₂ β)
  seqLaxFunctor .F-seqᴴ α β =
    E.⋆ⱽAssoc _ _ _
    ∙ cong₂ E._⋆ⱽ_ refl
        ((sym $ G.F-seqⱽ _ _)
         ∙ cong G.F₂ (F.F-seqᴴ α β))
    ∙ cong₂ E._⋆ⱽ_ refl (G.F-seqⱽ _ _)
    ∙ (sym $ E.⋆ⱽAssoc _ _ _)
    ∙ cong₂ E._⋆ⱽ_ (G.F-seqᴴ (F.F₂ α) (F.F₂ β)) refl
    ∙ E.⋆ⱽAssoc _ _ _
  seqLaxFunctor .F-unitality-l f =
    -- Gross proof that I outsourced to Claude
    -- I would hope there is a better way to write this
      unitality-l-pre
    ◁ (λ i → G.F-unitality-l (F.F₁ f) i E.⋆ⱽ G.F₂ (F.F-unitality-l f i))
    ▷ unitality-post
    where
    unitality-l-pre :
        (((G.F-id E.⋆ⱽ G.F₂ F.F-id) E.⋆ᴴ E.id₂) E.⋆ⱽ
         (G.F-seq (F.F₁ C.id₁) (F.F₁ f) E.⋆ⱽ G.F₂ (F.F-seq C.id₁ f)))
      ≡ (((G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ G.F-seq D.id₁ (F.F₁ f)) E.⋆ⱽ
         G.F₂ ((F.F-id D.⋆ᴴ D.id₂) D.⋆ⱽ F.F-seq C.id₁ f))
    unitality-l-pre =
        cong (λ δ → ((G.F-id E.⋆ⱽ G.F₂ F.F-id) E.⋆ᴴ δ) E.⋆ⱽ
                    (G.F-seq (F.F₁ C.id₁) (F.F₁ f) E.⋆ⱽ
                     G.F₂ (F.F-seq C.id₁ f)))
             (sym (E.⋆ⱽIdL E.id₂))
      ∙ cong (E._⋆ⱽ (G.F-seq (F.F₁ C.id₁) (F.F₁ f) E.⋆ⱽ
                     G.F₂ (F.F-seq C.id₁ f)))
             (E.interchange G.F-id (G.F₂ F.F-id) E.id₂ E.id₂)
      ∙ E.⋆ⱽAssoc (G.F-id E.⋆ᴴ E.id₂) (G.F₂ F.F-id E.⋆ᴴ E.id₂)
                  (G.F-seq (F.F₁ C.id₁) (F.F₁ f) E.⋆ⱽ
                   G.F₂ (F.F-seq C.id₁ f))
      ∙ cong ((G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ_)
             (sym (E.⋆ⱽAssoc (G.F₂ F.F-id E.⋆ᴴ E.id₂)
                             (G.F-seq (F.F₁ C.id₁) (F.F₁ f))
                             (G.F₂ (F.F-seq C.id₁ f))))
      ∙ cong (λ δ → (G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (((G.F₂ F.F-id E.⋆ᴴ δ) E.⋆ⱽ
                      G.F-seq (F.F₁ C.id₁) (F.F₁ f)) E.⋆ⱽ
                     G.F₂ (F.F-seq C.id₁ f)))
             (sym G.F-id₂)
      ∙ cong (λ r → (G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (r E.⋆ⱽ G.F₂ (F.F-seq C.id₁ f)))
             (sym (G.F-seqᴴ F.F-id D.id₂))
      ∙ cong ((G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ_)
             (E.⋆ⱽAssoc (G.F-seq D.id₁ (F.F₁ f))
                        (G.F₂ (F.F-id D.⋆ᴴ D.id₂))
                        (G.F₂ (F.F-seq C.id₁ f)))
      ∙ cong (λ r → (G.F-id E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (G.F-seq D.id₁ (F.F₁ f) E.⋆ⱽ r))
             (sym (G.F-seqⱽ (F.F-id D.⋆ᴴ D.id₂) (F.F-seq C.id₁ f)))
      ∙ sym (E.⋆ⱽAssoc (G.F-id E.⋆ᴴ E.id₂)
                       (G.F-seq D.id₁ (F.F₁ f))
                       (G.F₂ ((F.F-id D.⋆ᴴ D.id₂) D.⋆ⱽ F.F-seq C.id₁ f)))

    unitality-post : (G.F₂ D.id₂ E.⋆ⱽ G.F₂ (F.F₂ {f = f} C.id₂))
                     ≡ G.F₂ (F.F₂ {f = f} C.id₂)
    unitality-post = cong (E._⋆ⱽ G.F₂ (F.F₂ C.id₂)) G.F-id₂
                   ∙ E.⋆ⱽIdL _
  seqLaxFunctor .F-unitality-r f =
    -- Claude
      unitality-r-pre
    ◁ (λ i → G.F-unitality-r (F.F₁ f) i E.⋆ⱽ G.F₂ (F.F-unitality-r f i))
    ▷ unitality-post
    where
    unitality-r-pre :
        ((E.id₂ E.⋆ᴴ (G.F-id E.⋆ⱽ G.F₂ F.F-id)) E.⋆ⱽ
         (G.F-seq (F.F₁ f) (F.F₁ C.id₁) E.⋆ⱽ G.F₂ (F.F-seq f C.id₁)))
      ≡ (((E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ G.F-seq (F.F₁ f) D.id₁) E.⋆ⱽ
         G.F₂ ((D.id₂ D.⋆ᴴ F.F-id) D.⋆ⱽ F.F-seq f C.id₁))
    unitality-r-pre =
        cong (λ δ → (δ E.⋆ᴴ (G.F-id E.⋆ⱽ G.F₂ F.F-id)) E.⋆ⱽ
                    (G.F-seq (F.F₁ f) (F.F₁ C.id₁) E.⋆ⱽ
                     G.F₂ (F.F-seq f C.id₁)))
             (sym (E.⋆ⱽIdL E.id₂))
      ∙ cong (E._⋆ⱽ (G.F-seq (F.F₁ f) (F.F₁ C.id₁) E.⋆ⱽ
                     G.F₂ (F.F-seq f C.id₁)))
             (E.interchange E.id₂ E.id₂ G.F-id (G.F₂ F.F-id))
      ∙ E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F-id) (E.id₂ E.⋆ᴴ G.F₂ F.F-id)
                  (G.F-seq (F.F₁ f) (F.F₁ C.id₁) E.⋆ⱽ
                   G.F₂ (F.F-seq f C.id₁))
      ∙ cong ((E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ_)
             (sym (E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F₂ F.F-id)
                             (G.F-seq (F.F₁ f) (F.F₁ C.id₁))
                             (G.F₂ (F.F-seq f C.id₁))))
      ∙ cong (λ δ → (E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ
                    (((δ E.⋆ᴴ G.F₂ F.F-id) E.⋆ⱽ
                      G.F-seq (F.F₁ f) (F.F₁ C.id₁)) E.⋆ⱽ
                     G.F₂ (F.F-seq f C.id₁)))
             (sym G.F-id₂)
      ∙ cong (λ r → (E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ
                    (r E.⋆ⱽ G.F₂ (F.F-seq f C.id₁)))
             (sym (G.F-seqᴴ D.id₂ F.F-id))
      ∙ cong ((E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ_)
             (E.⋆ⱽAssoc (G.F-seq (F.F₁ f) D.id₁)
                        (G.F₂ (D.id₂ D.⋆ᴴ F.F-id))
                        (G.F₂ (F.F-seq f C.id₁)))
      ∙ cong (λ r → (E.id₂ E.⋆ᴴ G.F-id) E.⋆ⱽ
                    (G.F-seq (F.F₁ f) D.id₁ E.⋆ⱽ r))
             (sym (G.F-seqⱽ (D.id₂ D.⋆ᴴ F.F-id) (F.F-seq f C.id₁)))
      ∙ sym (E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F-id)
                       (G.F-seq (F.F₁ f) D.id₁)
                       (G.F₂ ((D.id₂ D.⋆ᴴ F.F-id) D.⋆ⱽ F.F-seq f C.id₁)))

    unitality-post : (G.F₂ D.id₂ E.⋆ⱽ G.F₂ (F.F₂ {f = f} C.id₂))
                     ≡ G.F₂ (F.F₂ {f = f} C.id₂)
    unitality-post = cong (E._⋆ⱽ G.F₂ (F.F₂ C.id₂)) G.F-id₂
                   ∙ E.⋆ⱽIdL _
  seqLaxFunctor .F-associativity f g h =
    -- Claude
      assoc-pre
    ◁ (λ i → G.F-associativity (F.F₁ f) (F.F₁ g) (F.F₁ h) i
             E.⋆ⱽ G.F₂ (F.F-associativity f g h i))
    ▷ assoc-post
    where
    assoc-pre :
        (((G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ⱽ G.F₂ (F.F-seq f g)) E.⋆ᴴ E.id₂) E.⋆ⱽ
         (G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h) E.⋆ⱽ
          G.F₂ (F.F-seq (f C.⋆₁ g) h)))
      ≡ (((G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ
          G.F-seq (F.F₁ f D.⋆₁ F.F₁ g) (F.F₁ h)) E.⋆ⱽ
         G.F₂ ((F.F-seq f g D.⋆ᴴ D.id₂) D.⋆ⱽ F.F-seq (f C.⋆₁ g) h))
    assoc-pre =
        cong (λ δ → ((G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ⱽ G.F₂ (F.F-seq f g)) E.⋆ᴴ δ)
                    E.⋆ⱽ
                    (G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h) E.⋆ⱽ
                     G.F₂ (F.F-seq (f C.⋆₁ g) h)))
             (sym (E.⋆ⱽIdL E.id₂))
      ∙ cong (E._⋆ⱽ (G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h) E.⋆ⱽ
                     G.F₂ (F.F-seq (f C.⋆₁ g) h)))
             (E.interchange (G.F-seq (F.F₁ f) (F.F₁ g)) (G.F₂ (F.F-seq f g))
                            E.id₂ E.id₂)
      ∙ E.⋆ⱽAssoc (G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂)
                  (G.F₂ (F.F-seq f g) E.⋆ᴴ E.id₂)
                  (G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h) E.⋆ⱽ
                   G.F₂ (F.F-seq (f C.⋆₁ g) h))
      ∙ cong ((G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ_)
             (sym (E.⋆ⱽAssoc (G.F₂ (F.F-seq f g) E.⋆ᴴ E.id₂)
                             (G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h))
                             (G.F₂ (F.F-seq (f C.⋆₁ g) h))))
      ∙ cong (λ δ → (G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (((G.F₂ (F.F-seq f g) E.⋆ᴴ δ) E.⋆ⱽ
                      G.F-seq (F.F₁ (f C.⋆₁ g)) (F.F₁ h)) E.⋆ⱽ
                     G.F₂ (F.F-seq (f C.⋆₁ g) h)))
             (sym G.F-id₂)
      ∙ cong (λ r → (G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (r E.⋆ⱽ G.F₂ (F.F-seq (f C.⋆₁ g) h)))
             (sym (G.F-seqᴴ (F.F-seq f g) D.id₂))
      ∙ cong ((G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ_)
             (E.⋆ⱽAssoc (G.F-seq (F.F₁ f D.⋆₁ F.F₁ g) (F.F₁ h))
                        (G.F₂ (F.F-seq f g D.⋆ᴴ D.id₂))
                        (G.F₂ (F.F-seq (f C.⋆₁ g) h)))
      ∙ cong (λ r → (G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂) E.⋆ⱽ
                    (G.F-seq (F.F₁ f D.⋆₁ F.F₁ g) (F.F₁ h) E.⋆ⱽ r))
             (sym (G.F-seqⱽ (F.F-seq f g D.⋆ᴴ D.id₂) (F.F-seq (f C.⋆₁ g) h)))
      ∙ sym (E.⋆ⱽAssoc (G.F-seq (F.F₁ f) (F.F₁ g) E.⋆ᴴ E.id₂)
                       (G.F-seq (F.F₁ f D.⋆₁ F.F₁ g) (F.F₁ h))
                       (G.F₂ ((F.F-seq f g D.⋆ᴴ D.id₂) D.⋆ⱽ
                              F.F-seq (f C.⋆₁ g) h)))

    assoc-post :
        (((E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ
          G.F-seq (F.F₁ f) (F.F₁ g D.⋆₁ F.F₁ h)) E.⋆ⱽ
         G.F₂ ((D.id₂ D.⋆ᴴ F.F-seq g h) D.⋆ⱽ F.F-seq f (g C.⋆₁ h)))
      ≡ ((E.id₂ E.⋆ᴴ (G.F-seq (F.F₁ g) (F.F₁ h) E.⋆ⱽ G.F₂ (F.F-seq g h))) E.⋆ⱽ
         (G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h)) E.⋆ⱽ
          G.F₂ (F.F-seq f (g C.⋆₁ h))))
    assoc-post =
        E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h))
                  (G.F-seq (F.F₁ f) (F.F₁ g D.⋆₁ F.F₁ h))
                  (G.F₂ ((D.id₂ D.⋆ᴴ F.F-seq g h) D.⋆ⱽ F.F-seq f (g C.⋆₁ h)))
      ∙ cong ((E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ_)
             (cong (G.F-seq (F.F₁ f) (F.F₁ g D.⋆₁ F.F₁ h) E.⋆ⱽ_)
                   (G.F-seqⱽ (D.id₂ D.⋆ᴴ F.F-seq g h) (F.F-seq f (g C.⋆₁ h))))
      ∙ cong ((E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ_)
             (sym (E.⋆ⱽAssoc (G.F-seq (F.F₁ f) (F.F₁ g D.⋆₁ F.F₁ h))
                             (G.F₂ (D.id₂ D.⋆ᴴ F.F-seq g h))
                             (G.F₂ (F.F-seq f (g C.⋆₁ h)))))
      ∙ cong (λ r → (E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ
                    (r E.⋆ⱽ G.F₂ (F.F-seq f (g C.⋆₁ h))))
             (G.F-seqᴴ D.id₂ (F.F-seq g h))
      ∙ cong (λ δ → (E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ
                    (((δ E.⋆ᴴ G.F₂ (F.F-seq g h)) E.⋆ⱽ
                      G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h))) E.⋆ⱽ
                     G.F₂ (F.F-seq f (g C.⋆₁ h))))
             G.F-id₂
      ∙ cong ((E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h)) E.⋆ⱽ_)
             (E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F₂ (F.F-seq g h))
                        (G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h)))
                        (G.F₂ (F.F-seq f (g C.⋆₁ h))))
      ∙ sym (E.⋆ⱽAssoc (E.id₂ E.⋆ᴴ G.F-seq (F.F₁ g) (F.F₁ h))
                       (E.id₂ E.⋆ᴴ G.F₂ (F.F-seq g h))
                       (G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h)) E.⋆ⱽ
                        G.F₂ (F.F-seq f (g C.⋆₁ h))))
      ∙ cong (E._⋆ⱽ (G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h)) E.⋆ⱽ
                     G.F₂ (F.F-seq f (g C.⋆₁ h))))
             (sym (E.interchange E.id₂ E.id₂
                                 (G.F-seq (F.F₁ g) (F.F₁ h))
                                 (G.F₂ (F.F-seq g h))))
      ∙ cong (λ δ → (δ E.⋆ᴴ (G.F-seq (F.F₁ g) (F.F₁ h) E.⋆ⱽ
                             G.F₂ (F.F-seq g h)))
                    E.⋆ⱽ
                    (G.F-seq (F.F₁ f) (F.F₁ (g C.⋆₁ h)) E.⋆ⱽ
                     G.F₂ (F.F-seq f (g C.⋆₁ h))))
             (E.⋆ⱽIdL E.id₂)


module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F

  Functor→LaxFunctor : LaxFunctor (Cat→2Cat C) (Cat→2Cat D)
  Functor→LaxFunctor .F₀ = F.F-ob
  Functor→LaxFunctor .F₁ = F.F-hom
  Functor→LaxFunctor .F₂ = cong F.F-hom
  Functor→LaxFunctor .F-id = sym F.F-id
  Functor→LaxFunctor .F-seq f g = sym $ F.F-seq f g
  Functor→LaxFunctor .F-id₂ = D.isSetHom _ _ _ _
  Functor→LaxFunctor .F-seqⱽ = λ _ _ → D.isSetHom _ _ _ _
  Functor→LaxFunctor .F-seqᴴ = λ _ _ → D.isSetHom _ _ _ _
  Functor→LaxFunctor .F-unitality-l _ = isProp→PathP (λ _ → D.isSetHom _ _) _ _
  Functor→LaxFunctor .F-unitality-r _ = isProp→PathP (λ _ → D.isSetHom _ _) _ _
  Functor→LaxFunctor .F-associativity _ _ _ = isProp→PathP (λ _ → D.isSetHom _ _) _ _
