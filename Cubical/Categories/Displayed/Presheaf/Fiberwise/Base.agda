{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Fiberwise.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ
open Iso
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) ((Cᴰ , isFib) : Fibration C ℓCᴰ ℓCᴰ')
  where
  private
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFib = FibrationNotation isFib
  record Presheafᶠ (ℓPᴰ : Level)
    : Type (ℓ-max ℓPᴰ $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓP $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-suc ℓPᴰ) where
    constructor presheafᶠ
    field
      P-obᶠ  : ∀ {x} (p : P.p[ x ]) → Presheaf Cᴰ.v[ x ] ℓPᴰ

    p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
    p[ p ][ xᴰ ] = ⟨ P-obᶠ p ⟅ xᴰ ⟆ ⟩


    _≡[_]_ : ∀ {x xᴰ} {f g : P.p[ x ]} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
      → Type ℓPᴰ
    _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ = PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

    _∫≡_ : ∀ {x xᴰ} {f g : P.p[ x ]}(fᴰ : p[ f ][ xᴰ ])(gᴰ : p[ g ][ xᴰ ])
      → Type _
    _∫≡_ {x}{xᴰ}{f}{g} fᴰ gᴰ = (f , fᴰ) ≡ (g , gᴰ)

    infix 2 _∫≡_

    isSetPshᶠ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet (p[ p ][ xᴰ ])
    isSetPshᶠ {x}{p}{xᴰ} = (P-obᶠ p ⟅ xᴰ ⟆) .snd

    module Pⱽ {x}{p : P.p[ x ]} = PresheafNotation (P-obᶠ p)

    _⋆ⱽᴰ_ : ∀ {x xᴰ yᴰ}{p : P.p[ x ]}(fⱽ : Cᴰ.v[ x ] [ xᴰ , yᴰ ])(pᴰ : p[ p ][ yᴰ ])
      → p[ p ][ xᴰ ]
    fⱽ ⋆ⱽᴰ pᴰ = fⱽ Pⱽ.⋆ pᴰ

    -- ⋆IdLⱽᴰ : 

    reind : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → p[ f ][ xᴰ ] → p[ g ][ xᴰ ]
    reind = subst p[_][ _ ]

    ≡in : ∀ {x} {p q : P.p[ x ]} {xᴰ}
         {pᴰ : p[ p ][ xᴰ ]}
         {qᴰ : p[ q ][ xᴰ ]}
         {p≡q : p ≡ q}
       → (pᴰ ≡[ p≡q ] qᴰ)
       → pᴰ ∫≡ qᴰ
    ≡in pᴰ≡qᴰ = ΣPathP (_ , pᴰ≡qᴰ)

    ≡out : ∀ {x} {p q : P.p[ x ]} {xᴰ}
         {pᴰ : p[ p ][ xᴰ ]}
         {qᴰ : p[ q ][ xᴰ ]}
       → (e : pᴰ ∫≡ qᴰ)
       → (pᴰ ≡[ fst (PathPΣ e) ] qᴰ)
    ≡out e = snd $ PathPΣ e


    field
      P-homᶠ : ∀ {x y} (f : C [ y , x ])(p : P.p[ x ])
        → PshHom (P-obᶠ p) (restrictPsh (f isFib.*F) (P-obᶠ (f P.⋆ p)))

    _*_ : ∀ {x y}{xᴰ}{p : P.p[ x ]} (f : C [ y , x ])(pᴰ : p[ p ][ xᴰ ])
      → p[ f P.⋆ p ][ f isFib.* xᴰ ]
    f * pᴰ = P-homᶠ f _ .N-ob _ pᴰ

    infixr 9 _*_

    -- *-naturality is like functoriality of f *
    *-natural : ∀ {x y}{xᴰ xᴰ'}{p : P.p[ x ]} (f : C [ y , x ])(fⱽ : Cᴰ.v[ x ] [ xᴰ' , xᴰ ])(pᴰ : p[ p ][ xᴰ ])
      → f * (fⱽ Pⱽ.⋆ pᴰ) ≡
        ((f isFib.*F) ⟪ fⱽ ⟫) Pⱽ.⋆ (f * pᴰ)
    *-natural {x}{y}{xᴰ}{xᴰ'}{p} f fⱽ pᴰ =
      P-homᶠ f p .N-hom xᴰ' xᴰ fⱽ pᴰ
    -- ⟨_⟩*⟨_⟩ : ∀ {x y}{xᴰ}{p q : P.p[ x ]} {f g : C [ y , x ]}{pᴰ : p[ p ][ xᴰ ]}{qᴰ : p[ q ][ xᴰ ]}
    --   (f≡g : f ≡ g)
    --   (pᴰ≡qᴰ : pᴰ ∫≡ qᴰ)
    --   → (f * pᴰ) ∫≡ (pathToIso (cong (_* _) (sym f≡g)) .fst Pⱽ.⋆ (g * qᴰ))
    -- ⟨_⟩*⟨_⟩ = {!!}

    field
      -- Just going to specify this manually for now, probably should
      -- make it some kind of natural trans equality or sthg
      P-idᶠ :  ∀ {x}{xᴰ} {p : P.p[ x ]} (pᴰ : p[ p ][ xᴰ ] )
        → (C.id * pᴰ)
            ∫≡
          (isFib.π Pⱽ.⋆ pᴰ)
      P-seqᶠ : ∀ {x y z xᴰ}{p : P.p[ x ]}(g : C [ z , y ])(f : C [ y , x ])(pᴰ : p[ p ][ xᴰ ])
        →
          ((g C.⋆ f) * pᴰ)
            ∫≡
          (isFib.introⱽ (isFib.introᴰ isFib.π) Pⱽ.⋆ (g * f * pᴰ))

    opaque
      reind-filler : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
        → (fᴰ : p[ f ][ xᴰ ])
        → fᴰ ∫≡ reind f≡g fᴰ
      reind-filler f≡g fᴰ = ΣPathP (f≡g , (subst-filler p[_][ _ ] f≡g fᴰ))

      rectify :
        ∀ {x}{p p' : P.p[ x ]}{p≡p' p≡p'' : p ≡ p'}{xᴰ}
        {pᴰ : p[ p ][ xᴰ ]}
        {pᴰ' : p[ p' ][ xᴰ ]}
        → pᴰ ≡[ p≡p' ] pᴰ'
        → pᴰ ≡[ p≡p'' ] pᴰ'
      rectify {pᴰ = pᴰ}{pᴰ'} = subst (pᴰ ≡[_] pᴰ') (P.isSetPsh _ _ _ _)

      ⟨_⟩⋆ⱽᴰ⟨_⟩ : ∀ {x xᴰ yᴰ}{p p' : P.p[ x ]}{fⱽ fⱽ' : Cᴰ.v[ x ] [ xᴰ , yᴰ ]}{pᴰ : p[ p ][ yᴰ ]}{pᴰ' : p[ p' ][ yᴰ ]}
        (fⱽ≡fⱽ' : fⱽ Cᴰ.∫≡ fⱽ')(pᴰ≡pᴰ' : pᴰ ∫≡ pᴰ')
        → (fⱽ Pⱽ.⋆ pᴰ) ∫≡ (fⱽ' Pⱽ.⋆ pᴰ')
      ⟨_⟩⋆ⱽᴰ⟨_⟩ {fⱽ = fⱽ}{fⱽ' = fⱽ'} fⱽ≡fⱽ' pᴰ≡pᴰ' = ≡in $ λ i → fⱽ≡fⱽ'' i Pⱽ.⋆ pᴰ≡pᴰ' i .snd
        where 
          fⱽ≡fⱽ'' : fⱽ ≡ fⱽ'
          fⱽ≡fⱽ'' = Cᴰ.rectify $ Cᴰ.≡out $ fⱽ≡fⱽ' 

    _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p : P.p[ y ]}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])(pᴰ : p[ p ][ yᴰ ])
      → p[ f P.⋆ p ][ xᴰ ]
    -- I can convert fᴰ to a Cᴰ.v[ x ][ xᴰ , f*yᴰ ]
    _⋆ᴰ_ {f = f} fᴰ pᴰ =
      isFib.introⱽ fᴰ Pⱽ.⋆ (f * pᴰ)

    opaque
      ∫⋆IdLᴰ : ∀ {x xᴰ}{p : P.p[ x ]}(pᴰ : p[ p ][ xᴰ ])
        → (Cᴰ.idᴰ ⋆ᴰ pᴰ) ∫≡ pᴰ
      ∫⋆IdLᴰ pᴰ = ⟨ refl ⟩⋆ⱽᴰ⟨ P-idᶠ pᴰ ⟩
        ∙ ≡in (sym (Pⱽ.⋆Assoc _ _ _) ∙ Pⱽ.⟨ isFib.UMPⱽ .leftInv Cᴰ.idᴰ ⟩⋆⟨⟩ ∙ Pⱽ.⋆IdL pᴰ)

      ∫⋆Assocᴰ : ∀ {x y z xᴰ yᴰ zᴰ}{f : C [ z , y ]}{g : C [ y , x ]}{p : P.p[ x ]}
        (fᴰ : Cᴰ [ f ][ zᴰ , yᴰ ])(gᴰ : Cᴰ [ g ][ yᴰ , xᴰ ])(pᴰ : p[ p ][ xᴰ ])
        → ((fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ pᴰ) ∫≡ (fᴰ ⋆ᴰ (gᴰ ⋆ᴰ pᴰ))
      ∫⋆Assocᴰ {f = f}{g}{p} fᴰ gᴰ pᴰ = ⟨ refl ⟩⋆ⱽᴰ⟨ P-seqᶠ _ _ pᴰ ⟩
        ∙ (≡in $
          (isFib.introⱽ (fᴰ Cᴰ.⋆ᴰ gᴰ) Pⱽ.⋆ (isFib.introⱽ (isFib.introᴰ isFib.π) Pⱽ.⋆ (f * g * pᴰ)))
            ≡⟨ sym (Pⱽ.⋆Assoc _ _ _) ∙ Pⱽ.⟨
              (isFib.introⱽ (fᴰ Cᴰ.⋆ᴰ gᴰ) Cᴰ.⋆ⱽ isFib.introⱽ {f = f} (isFib.introᴰ isFib.π))
                ≡⟨ isoInvInjective isFib.UMPⱽ _ _
                  (Cᴰ.⋆Assocⱽⱽᴰ ∙ (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⟨⟩⋆ⱽᴰ⟨ Cᴰ.≡in $ isFib.UMPⱽ .leftInv _ ⟩)
                  ∙ isoInvInjective isFib.UMP _ _
                    (Cᴰ.rectify $ Cᴰ.≡out $
                      Cᴰ.⋆Assocⱽᴰᴰ ∙ Cᴰ.⟨⟩⋆ⱽᴰ⟨ Cᴰ.≡in $ isFib.UMP .leftInv _ ⟩
                      ∙ (Cᴰ.≡in $ isFib.UMPⱽ .leftInv _)
                      ∙ Cᴰ.⟨ Cᴰ.≡in $ sym $ isFib.UMPⱽ .leftInv _ ⟩⋆⟨ Cᴰ.≡in $ sym $ isFib.UMPⱽ .leftInv _ ⟩
                      ∙ (Cᴰ.≡in $ sym Cᴰ.⋆Assocᴰⱽᴰ))
                  ∙ Cᴰ.⋆Assocⱽᴰⱽ
                  ∙ (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⟨⟩⋆ⱽᴰ⟨ sym $ Cᴰ.≡in $ isFib.UMPⱽ .leftInv _ ⟩)
                  ∙ sym Cᴰ.⋆Assocⱽⱽᴰ
                  )
                 ⟩
               (isFib.introⱽ fᴰ Cᴰ.⋆ⱽ isFib.introⱽ {f = f} (isFib.π Cᴰ.⋆ᴰⱽ isFib.introⱽ gᴰ))
                ∎
              ⟩⋆⟨⟩ ∙ Pⱽ.⋆Assoc _ _ _  ⟩
          (isFib.introⱽ fᴰ Pⱽ.⋆ ((f isFib.*F) ⟪ isFib.introⱽ gᴰ ⟫ Pⱽ.⋆ (f * g * pᴰ)))
            ≡⟨ Pⱽ.⟨⟩⋆⟨ sym $ *-natural _ _ _ ⟩ ⟩
          (isFib.introⱽ fᴰ Pⱽ.⋆ (f * (isFib.introⱽ gᴰ Pⱽ.⋆ (g * pᴰ))))
            ∎)

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (isFib : isFibration Cᴰ)
  where
  private
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFib = FibrationNotation isFib
  module _ (Pᶠ : Presheafᶠ P (Cᴰ , isFib) ℓPᴰ) where
    private
      module Pᶠ = Presheafᶠ Pᶠ
    Presheafᶠ→Presheafᴰ : Presheafᴰ P Cᴰ ℓPᴰ
    Presheafᶠ→Presheafᴰ .F-obᴰ xᴰ p = Pᶠ.p[ p ][ xᴰ ] , Pᶠ.isSetPshᶠ
    Presheafᶠ→Presheafᴰ .F-homᴰ fᴰ p pᴰ = fᴰ Pᶠ.⋆ᴰ pᴰ
    Presheafᶠ→Presheafᴰ .F-idᴰ = funExt λ p → funExt λ pᴰ → Pᶠ.rectify $ Pᶠ.≡out $ Pᶠ.∫⋆IdLᴰ pᴰ
    Presheafᶠ→Presheafᴰ .F-seqᴰ gᴰ fᴰ = funExt λ p → funExt λ pᴰ → Pᶠ.rectify $ Pᶠ.≡out $ Pᶠ.∫⋆Assocᴰ fᴰ gᴰ pᴰ

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    open Presheafᶠ hiding (reind)
    Presheafᴰ→Presheafᶠ : Presheafᶠ P (Cᴰ , isFib) ℓPᴰ
    Presheafᴰ→Presheafᶠ .P-obᶠ p = Pᴰ.restrict p
    Presheafᴰ→Presheafᶠ .P-homᶠ f p .N-ob xᴰ pᴰ = isFib.π Pᴰ.⋆ᴰ pᴰ
    Presheafᴰ→Presheafᶠ .P-homᶠ f p .N-hom xᴰ xᴰ' fⱽ pᴰ =
      (isFib.π Pᴰ.⋆ᴰ (fⱽ Pᴰ.⋆ⱽᴰ pᴰ))
        ≡⟨ (Pᴰ.rectify $ Pᴰ.≡out $
          sym (Pᴰ.⋆Assocᴰⱽᴰ _ _ _)
          ∙ Pᴰ.⟨ Cᴰ.≡in (sym (isFib.UMPⱽ .leftInv _)) ⟩⋆⟨⟩
          ∙ Pᴰ.⋆Assocⱽᴰᴰ _ _ _)
         ⟩
      ( (f isFib.*F) ⟪ fⱽ ⟫ Pᴰ.⋆ⱽᴰ (isFib.π Pᴰ.⋆ᴰ pᴰ))
        ∎
    Presheafᴰ→Presheafᶠ .P-idᶠ pᴰ = Pᴰ.reind-filler _ _
    Presheafᴰ→Presheafᶠ .P-seqᶠ f g pᴰ =
      _ , isFib.π Pᴰ.⋆ᴰ pᴰ
        ≡⟨ ((Pᴰ.⟨ Cᴰ.≡in (sym (isFib.UMP .leftInv _)) ⟩⋆⟨⟩ ∙ Pᴰ.⋆Assoc _ _ _) ∙ Pᴰ.⟨ Cᴰ.≡in (sym (isFib.UMPⱽ .leftInv _)) ⟩⋆⟨⟩) ∙ Pᴰ.⋆Assocⱽᴰᴰ _ _ _ ⟩
      _ , (isFib.introⱽ (isFib.introᴰ isFib.π) Pᴰ.⋆ⱽᴰ (isFib.π Pᴰ.⋆ᴰ (isFib.π Pᴰ.⋆ᴰ pᴰ)))
        ∎
