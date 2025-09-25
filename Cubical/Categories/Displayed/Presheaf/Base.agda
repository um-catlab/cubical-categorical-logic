{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality.More
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Functorᴰ

Presheafᴰ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (D : Categoryᴰ C ℓD ℓD')
          → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} P D ℓPᴰ = Functorᴰ P (D ^opᴰ) (SETᴰ ℓP ℓPᴰ)

PRESHEAFᴰ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓP ℓPᴰ : Level) → Categoryᴰ (PresheafCategory C ℓP) _ _
PRESHEAFᴰ Cᴰ ℓP ℓPᴰ = FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓP ℓPᴰ)

-- The "classical" equivalent of a Presheafᴰ is a presheaf on
-- TotalCat.∫C with a Fst. The advantage to it being displayed is that
-- it is definitionally homomorphic
∫P : {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
     → {P : Presheaf C ℓP} → {ℓPᴰ : Level}
     → Presheafᴰ P D ℓPᴰ
     → Presheaf (TotalCat.∫C D) (ℓ-max ℓP ℓPᴰ)
∫P Pᴰ = ΣF ∘F TotalCat.∫F Pᴰ

open PshHom
Fst : {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
     → {P : Presheaf C ℓP} → {ℓPᴰ : Level}
     → (Pᴰ : Presheafᴰ P D ℓPᴰ)
     → PshHet TotalCat.Fst (∫P Pᴰ) P
Fst Pᴰ .N-ob x x₁ = x₁ .fst
Fst Pᴰ .N-hom x y f p = refl

-- TODO: Snd?, Intro?

module PresheafᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_
  infix 2 _≡[_]_

  pob[_] : C.ob → Type ℓP
  pob[ x ] = P.p[ x ]

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ f ][ xᴰ ] = ⟨ Pᴰ .F-obᴰ xᴰ f ⟩

  isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
  isSetPshᴰ {x} {p} {xᴰ} = Pᴰ .F-obᴰ xᴰ p .snd

  _≡[_]_ : ∀ {x xᴰ} {f g : P.p[ x ]} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
    → Type ℓPᴰ
  _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ =
    PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

  reind : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → p[ f ][ xᴰ ] → p[ g ][ xᴰ ]
  reind = subst p[_][ _ ]

  reind-filler : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
    → (fᴰ : p[ f ][ xᴰ ])
    → (f , fᴰ) ≡ (g , reind f≡g fᴰ)
  reind-filler f≡g fᴰ = ΣPathP (f≡g , (subst-filler p[_][ _ ] f≡g fᴰ))

  ≡in : {a : C.ob} {f g : P.p[ a ]}
        {aᴰ : Cᴰ.ob[ a ]}
        {fᴰ : p[ f ][ aᴰ ]}
        {gᴰ : p[ g ][ aᴰ ]}
        {p : f ≡ g}
      → (fᴰ ≡[ p ] gᴰ)
      → (f , fᴰ) ≡ (g , gᴰ)
  ≡in e = ΣPathP (_ , e)

  ≡out : {a : C.ob} {f g : P.p[ a ]}
         {aᴰ : Cᴰ.ob[ a ]}
         {fᴰ : p[ f ][ aᴰ ]}
         {gᴰ : p[ g ][ aᴰ ]}
       → (e : (f , fᴰ) ≡ (g , gᴰ))
       → (fᴰ ≡[ fst (PathPΣ e) ] gᴰ)
  ≡out e = snd (PathPΣ e)

  rectify : {a : C.ob} {f g : P.p[ a ]} {p p' : f ≡ g}
      {aᴰ : Cᴰ.ob[ a ]}
      {fᴰ : p[ f ][ aᴰ ]}
      {gᴰ : p[ g ][ aᴰ ]}
    → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
  rectify {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡[_] gᴰ) (P.isSetPsh _ _ _ _)

  open PresheafNotation (∫P Pᴰ) public

  reind⟨_⟩⟨_⟩ : ∀ {x : C.ob} {f g : P.p[ x ]}{xᴰ}
      {fᴰ fᴰ' : p[ f ][ xᴰ ]}
      (f≡g : f ≡ g)
    → Path p[ _ ]
        (f , fᴰ)
        (f , fᴰ')
    → Path p[ _ ]
        (g , reind f≡g fᴰ)
        (g , reind f≡g fᴰ')
  reind⟨ f≡g ⟩⟨ fᴰ≡fᴰ' ⟩ = ≡in (cong (reind f≡g) (rectify (≡out fᴰ≡fᴰ')))

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{g}
     → Cᴰ [ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ]
     → p[ f P.⋆ g ][ xᴰ ]
  fᴰ ⋆ᴰ gᴰ = ((_ , fᴰ) ⋆ (_ , gᴰ)) .snd

  ⋆Assocᴰ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}  {h : P.p[ z ]} {xᴰ yᴰ zᴰ}
      (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ]) (hᴰ : p[ h ][ zᴰ ])
      → (fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ P.⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
  ⋆Assocᴰ fᴰ gᴰ hᴰ = rectify $ ≡out $ ⋆Assoc (_ , fᴰ) (_ , gᴰ) (_ , hᴰ)

  ⋆IdLᴰ : ∀ {x} {f : P.p[ x ]} {xᴰ} (fᴰ : p[ f ][ xᴰ ]) → Cᴰ.idᴰ ⋆ᴰ fᴰ ≡[ P.⋆IdL f ] fᴰ
  ⋆IdLᴰ fᴰ = rectify $ ≡out $ ⋆IdL (_ , fᴰ)

  _⋆ⱽᴰ_ : ∀ {x xᴰ xᴰ'}{g}
     → Cᴰ [ C.id {x} ][ xᴰ , xᴰ' ] → p[ g ][ xᴰ' ]
     → p[ g ][ xᴰ ]
  fⱽ ⋆ⱽᴰ gᴰ = reind (P.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

  -- Should it just be fⱽ ≡ fⱽ' instead since that's more "vertical"?
  ⟨_⟩⋆ⱽᴰ⟨_⟩ :
    ∀ {x xᴰ xᴰ'}{g g'}
    {fⱽ fⱽ' : Cᴰ.v[ x ] [ xᴰ , xᴰ' ]}
    {gᴰ gᴰ'}
    → Path (Cᴰ.Hom[ _ , _ ]) (_ , fⱽ) (_ , fⱽ')
    → Path p[ _ ] (g , gᴰ) (g' , gᴰ')
    → Path p[ _ ] (_ , fⱽ ⋆ⱽᴰ gᴰ) (_ , fⱽ' ⋆ⱽᴰ gᴰ')
  ⟨_⟩⋆ⱽᴰ⟨_⟩ {fⱽ = fⱽ}{fⱽ'} p q = ≡in (λ i → p' i ⋆ⱽᴰ q i .snd) where
    p' : fⱽ ≡ fⱽ'
    p' = Cᴰ.rectify $ Cᴰ.≡out p
  opaque
    ⋆Assocᴰⱽᴰ : ∀ {x y} {f : C [ x , y ]} {h : P.p[ y ]} {xᴰ yᴰ yᴰ'}
        (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gⱽ : Cᴰ.v[ y ] [ yᴰ , yᴰ' ]) (hᴰ : p[ h ][ yᴰ' ])
        → Path p[ _ ]
            (_ , ((fᴰ Cᴰ.⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ))
            (_ , (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ)))
    ⋆Assocᴰⱽᴰ fᴰ gⱽ hᴰ =
      ⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _
      ∙ ⟨ refl ⟩⋆⟨ reind-filler _ _ ⟩

    ⋆Assocⱽⱽᴰ : ∀ {x}{h : P.p[ x ]}{xᴰ xᴰ' xᴰ''}
        (fⱽ : Cᴰ.v[ x ] [ xᴰ , xᴰ' ]) (gⱽ : Cᴰ.v[ x ] [ xᴰ' , xᴰ'' ]) (hᴰ : p[ h ][ xᴰ'' ])
        → Path p[ _ ]
            (_ , ((fⱽ Cᴰ.⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ))
            (_ , (fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ)))
    ⋆Assocⱽⱽᴰ fⱽ gⱽ hᴰ =
      (sym $ reind-filler _ _) ∙
      ⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
      ∙ ⋆Assoc _ _ _
      ∙ ⟨⟩⋆⟨ reind-filler _ _ ⟩
      ∙ reind-filler _ _

    ⋆Assocⱽᴰᴰ : ∀ {x y} {g : C [ x , y ]}  {h : P.p[ y ]} {xᴰ xᴰ' yᴰ}
      (fⱽ : Cᴰ.v[ x ] [ xᴰ , xᴰ' ]) (gᴰ : Cᴰ [ g ][ xᴰ' , yᴰ ]) (hᴰ : p[ h ][ yᴰ ])
      → Path p[ _ ]
          (_ , (fⱽ Cᴰ.⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ)
          (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ))
    ⋆Assocⱽᴰᴰ fⱽ gᴰ hᴰ =
      ⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
      ∙ ⋆Assoc _ _ _
      ∙ reind-filler _ _

    ⋆ⱽIdL : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{g}
      → (gᴰ : p[ g ][ xᴰ ])
      → Cᴰ.idᴰ ⋆ⱽᴰ gᴰ ≡ gᴰ
    ⋆ⱽIdL gᴰ = rectify $ ≡out $ (sym $ reind-filler _ _) ∙ ⋆IdL _

    ∫⋆ⱽIdL : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{g}
      → (gᴰ : p[ g ][ xᴰ ])
      → Path p[ _ ]
          (_ , Cᴰ.idᴰ ⋆ⱽᴰ gᴰ)
          (_ , gᴰ)
    ∫⋆ⱽIdL gᴰ = sym (reind-filler _ _) ∙ ⋆IdL _

    toPathPPshᴰ
      : ∀ {x xᴰ yᴰ}{p q : P.p[ x ]}{p≡q : p ≡ q}
      → {pᴰ : p[ p ][ xᴰ ]}
      → (xᴰ≡yᴰ : xᴰ ≡ yᴰ)
      → {qᴰ : p[ q ][ yᴰ ]}
      → Path (p[ _ ]) (_ , pathToCatIsoⱽ Cᴰ (sym xᴰ≡yᴰ) .fst ⋆ᴰ pᴰ) (_ , qᴰ)
      → PathP (λ i → p[ p≡q i ][ xᴰ≡yᴰ i ]) pᴰ qᴰ
    toPathPPshᴰ {x} {xᴰ} {yᴰ} {p} {q} {p≡q} {pᴰ} = J
      (λ yᴰ xᴰ≡yᴰ →  ∀ {qᴰ : p[ q ][ yᴰ ]}
      → Path (p[ _ ]) (_ , pathToCatIsoⱽ Cᴰ (sym xᴰ≡yᴰ) .fst ⋆ᴰ pᴰ) (_ , qᴰ)
      → PathP (λ i → p[ p≡q i ][ xᴰ≡yᴰ i ]) pᴰ qᴰ)
      (λ {qᴰ} idᴰ⋆ᴰpᴰ≡qᴰ →
        rectify $ ≡out $ (sym (⋆IdL _) ∙ ⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩ ) ∙ idᴰ⋆ᴰpᴰ≡qᴰ)

    fromPathPPshᴰ
      : ∀ {x xᴰ yᴰ}{p q : P.p[ x ]}{p≡q : p ≡ q}
      → {pᴰ : p[ p ][ xᴰ ]}
      → (xᴰ≡yᴰ : xᴰ ≡ yᴰ)
      → {qᴰ : p[ q ][ yᴰ ]}
      → PathP (λ i → p[ p≡q i ][ xᴰ≡yᴰ i ]) pᴰ qᴰ
      → Path (p[ _ ]) (_ , pathToCatIsoⱽ Cᴰ (sym xᴰ≡yᴰ) .fst ⋆ᴰ pᴰ) (_ , qᴰ)
    fromPathPPshᴰ {x}{xᴰ}{yᴰ}{p}{q}{p≡q}{pᴰ} = J (λ yᴰ xᴰ≡yᴰ →  ∀ {qᴰ : p[ q ][ yᴰ ]}
      → PathP (λ i → p[ p≡q i ][ xᴰ≡yᴰ i ]) pᴰ qᴰ
      → Path (p[ _ ]) (_ , pathToCatIsoⱽ Cᴰ (sym xᴰ≡yᴰ) .fst ⋆ᴰ pᴰ) (_ , qᴰ))
      λ pᴰ≡qᴰ → ⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ ≡in pᴰ≡qᴰ ⟩
        ∙ ⋆IdL _

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (c : C .Category.ob) (D : Categoryᴰ C ℓD ℓD')
          → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ {C = C} c D = Presheafᴰ (C [-, c ]) D

module PresheafⱽNotation
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c} {ℓPᴰ} (P : Presheafⱽ c Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    variable
      x y z : C.ob
      f g h : C [ x , y ]
      cᴰ : Cᴰ.ob[ c ]
      xᴰ yᴰ zᴰ : Cᴰ.ob[ x ]
  open PresheafᴰNotation P public

  pⱽ[_] : (cᴰ : Cᴰ.ob[ c ]) → Type ℓPᴰ
  pⱽ[ cᴰ ] = p[ C.id ][ cᴰ ]

  _⋆ᴰⱽ_ :
      Cᴰ [ f ][ xᴰ , cᴰ ] → pⱽ[ cᴰ ]
      → p[ f ][ xᴰ ]
  fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

  _⋆ⱽ_ :
    Cᴰ.v[ c ] [ xᴰ , cᴰ ] → pⱽ[ cᴰ ]
    → pⱽ[ xᴰ ]
  fⱽ ⋆ⱽ pⱽ = fⱽ ⋆ᴰⱽ pⱽ

  opaque
    ⋆ᴰid≡⋆ᴰⱽ : ∀ (fᴰ : Cᴰ [ f ][ xᴰ , cᴰ ]) (gⱽ : pⱽ[ cᴰ ])
      → fᴰ ⋆ᴰ gⱽ ≡[ C.⋆IdR f ] fᴰ ⋆ᴰⱽ gⱽ
    ⋆ᴰid≡⋆ᴰⱽ fᴰ gⱽ = λ i → reind-filler (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ) i .snd

    ⋆Assocᴰᴰⱽ :
      ∀ (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])(gᴰ : Cᴰ [ g ][ yᴰ , cᴰ ])(pⱽ : pⱽ[ cᴰ ])
      → (fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰⱽ pⱽ ≡ fᴰ ⋆ᴰ (gᴰ ⋆ᴰⱽ pⱽ)
    ⋆Assocᴰᴰⱽ fᴰ gᴰ pⱽ = rectify $ ≡out $
      sym (reind-filler _ _)
      ∙ ⋆Assoc _ _ _
      ∙ ⟨⟩⋆⟨ reind-filler _ _ ⟩

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Cᴰ = Categoryᴰ Cᴰ

  PresheafᴰEq : Type _
  PresheafᴰEq =
    Σ[ tyEq ∈ Eq ((∀ {x} (p : P.p[ x ]) (xᴰ : Cᴰ.ob[ x ]) → Type ℓPᴰ )) Pᴰ.p[_][_] Qᴰ.p[_][_] ]
    Eq.HEq (Eq.ap (λ p[_][_] → (∀ {x y}{f : C [ y , x ]}{xᴰ}{yᴰ}
      → {p : P.p[ x ]}
      → Cᴰ [ f ][ yᴰ , xᴰ ]
      → p[ p ][ xᴰ ]
      → p[ f P.⋆ p ][ yᴰ ]))
      tyEq)
      Pᴰ._⋆ᴰ_
      Qᴰ._⋆ᴰ_
