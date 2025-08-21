{-# OPTIONS --safe --lossy-unification #-}
-- TODO: move this to Displayed.Presheaf.Base
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Functor
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

Fst : {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
     → {P : Presheaf C ℓP} → {ℓPᴰ : Level}
     → (Pᴰ : Presheafᴰ P D ℓPᴰ)
     → PshHet TotalCat.Fst (∫P Pᴰ) P
Fst Pᴰ .fst x x₁ = x₁ .fst
Fst Pᴰ .snd x y f p = refl

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

    ⋆ⱽIdL : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{g}
      → (gᴰ : p[ g ][ xᴰ ])
      → Cᴰ.idᴰ ⋆ⱽᴰ gᴰ ≡ gᴰ
    ⋆ⱽIdL gᴰ = rectify $ ≡out $ (sym $ reind-filler _ _) ∙ ⋆IdL _

    -- TODO: ⋆ⱽAssoc but it relies on the definition _⋆ⱽ_ in the fiber

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHom P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  record PshHomᴰ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓC) where
    no-eta-equality
    field
      N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .fst x p ][ xᴰ ]
      N-homᴰ :
        ∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
        → {f : C [ x , y ]}{p : P.p[ y ]}
        → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
        → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
            Qᴰ.≡[ α .snd x y f p ]
          (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ)

    ∫PshHomᴰ : PshHom (∫P Pᴰ) (∫P Qᴰ)
    ∫PshHomᴰ .fst (x , xᴰ) (p , pᴰ) = (α .fst _ p) , (N-obᴰ pᴰ)
    ∫PshHomᴰ .snd _ _ (f , fᴰ) (p , pᴰ) = ΣPathP ((α .snd _ _ f p) , N-homᴰ)

  isPshIsoᴰ : PshHomᴰ → isPshIso {P = P}{Q = Q} α → Type _
  isPshIsoᴰ αᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
      → isIsoOver (isIsoToIso (αIsIso x)) Pᴰ.p[_][ xᴰ ] Qᴰ.p[_][ xᴰ ]
          (λ _ → αᴰ .PshHomᴰ.N-obᴰ)

  isPshEquivOver : PshHomᴰ → Type _
  isPshEquivOver αᴰ = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
    → isEquivOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}{f = α .fst x}
        λ _ → αᴰ .PshHomᴰ.N-obᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshIsoᴰ : Type _
  PshIsoᴰ =
    Σ[ αᴰ ∈ PshHomᴰ (α .fst) Pᴰ Qᴰ ] isPshIsoᴰ (α .fst) Pᴰ Qᴰ αᴰ (α .snd)
  open IsoOver
  mkPshIsoᴰEquivOver : ∀ (αᴰ : PshHomᴰ (α .fst) Pᴰ Qᴰ)
    → isPshEquivOver (α .fst) Pᴰ Qᴰ αᴰ
    → PshIsoᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .fst = αᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .snd {x}{xᴰ} =
    isisoover (α-isoOver .inv) (α-isoOver .rightInv)
      λ p pᴰ → Pᴰ.rectify $ α-isoOver .leftInv p pᴰ
    where
    α-isoOver = equivOver→IsoOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}
                  (isoToEquiv (isIsoToIso (α .snd x)))
      (λ a → αᴰ .PshHomᴰ.N-obᴰ)
      isPshEqv

  open isIsoOver
  ∫PshIsoᴰ : PshIsoᴰ → PshIso (∫P Pᴰ) (∫P Qᴰ)
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .fst = PshHomᴰ.∫PshHomᴰ αᴰ
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .fst (q , qᴰ) = _ , αᴰIsPshIsoᴰ .inv q qᴰ
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .snd .fst (q , qᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .rightInv q qᴰ)
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .snd .snd (p , pᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .leftInv p pᴰ)

-- We can use paths if the presheaves are of the same level
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓP}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) {x : C.ob} where
    open PshHomᴰ
    open isIsoᴰ
    open isIsoOver
    private
      α⟨x⟩ : CatIso (SET ℓP) (P .F-ob x) (Q .F-ob x)
      α⟨x⟩ = PshIso→SETIso P Q α x
    PshIsoᴰ→SETᴰIsoᴰ : ∀ xᴰ → CatIsoᴰ (SETᴰ ℓP ℓPᴰ) α⟨x⟩ (Pᴰ .F-obᴰ xᴰ) (Qᴰ .F-obᴰ xᴰ)
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .fst p pᴰ = αᴰ .fst .N-obᴰ pᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .invᴰ q qᴰ = αᴰ .snd .inv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .secᴰ = funExt λ q → funExt λ qᴰ →
      αᴰ .snd .rightInv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .retᴰ = funExt λ p → funExt λ pᴰ →
      αᴰ .snd .leftInv p pᴰ
  -- Maybe we can just get this from PshIso→Path for ∫αᴰ ?
  PshIsoᴰ→PathP
      : ∀ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
      → PathP (λ i → Presheafᴰ (PshIso→Path P Q α i) Cᴰ ℓPᴰ) Pᴰ Qᴰ
  PshIsoᴰ→PathP αᴰ =
    Functorᴰ≡
      (λ xᴰ → CatIsoᴰ→P≡Q (PshIso→SETIso P Q α _) (PshIsoᴰ→SETᴰIsoᴰ αᴰ xᴰ))
      λ {x = x}{xᴰ = xᴰ} fᴰ →
        toPathP (funExt (λ q → funExt (λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _ _)
          ∙ cong (∫αᴰ .fst .fst _) Pᴰ.⟨ refl ⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ⟩
          ∙ ∫αᴰ .fst .snd _ _ _ _
          ∙ Qᴰ.⟨ refl ⟩⋆⟨ cong (∫αᴰ .fst .fst _) (cong (∫αᴰ .snd _ .fst) (sym $ Qᴰ.reind-filler _ _))
                 ∙ ∫αᴰ .snd _ .snd .fst _ ⟩
        )))
    where
      ∫αᴰ : PshIso (∫P Pᴰ) (∫P Qᴰ)
      ∫αᴰ = ∫PshIsoᴰ _ _ _ αᴰ

-- Displayed Yoneda
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  open PshHomᴰ
  yoRecᴰ : ∀ {c}{cᴰ : Cᴰ.ob[ c ]} {p : P.p[ c ]}
    → (pᴰ : Pᴰ.p[ p ][ cᴰ ]) → PshHomᴰ (yoRec P p) (Cᴰ [-][-, cᴰ ]) Pᴰ
  yoRecᴰ pᴰ .N-obᴰ fᴰ = fᴰ Pᴰ.⋆ᴰ pᴰ
  yoRecᴰ pᴰ .N-homᴰ = Pᴰ.⋆Assocᴰ _ _ _

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (ue : UniversalElement C P) (Pᴰ : Presheafᴰ P D ℓPᴰ) where
  private
    module D = Fibers D
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  record UniversalElementᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    field
      vertexᴰ : D.ob[ vertex ]
      elementᴰ : Pᴰ.p[ element ][ vertexᴰ ]
      universalᴰ :
        isPshIsoᴰ (yoRec P element) (D [-][-, vertexᴰ ]) Pᴰ
          (yoRecᴰ Pᴰ elementᴰ) ⋆element-isPshIso

    introᴰ : ∀ {x xᴰ} {p : P.p[ x ]}
        → Pᴰ.p[ p ][ xᴰ ]
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ = universalᴰ .isIsoOver.inv _

    ∫ue : UniversalElement (TotalCat.∫C D) (∫P Pᴰ)
    ∫ue .UniversalElement.vertex = vertex , vertexᴰ
    ∫ue .UniversalElement.element = element , elementᴰ
    ∫ue .UniversalElement.universal (v , vᴰ) =
      isIsoToIsEquiv (isIsoOver→isIsoΣ universalᴰ)

    module ∫ue = UniversalElementNotation ∫ue
    module Pshᴰ = PresheafᴰNotation Pᴰ

    -- We only provide the ∫ versions of these because working with
    -- the PathP versions is extremely slow.
    introᴰ≡ = ∫ue.intro≡
    introᴰ-natural = ∫ue.intro-natural
    extensionalityᴰ = ∫ue.extensionality
    βᴰ = ∫ue.β
    ηᴰ = ∫ue.η
    weak-ηᴰ = ∫ue.weak-η

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} ((x , yx≅P) : RepresentationPshIso P)
         (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  RepresentationPshIsoᴰ : Type _
  RepresentationPshIsoᴰ =
    Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] PshIsoᴰ yx≅P (Cᴰ [-][-, xᴰ ]) Pᴰ

  open UniversalElementᴰ
  open PshHomᴰ
  open isIsoOver
  module _  ((xᴰ , yxᴰ≅Pᴰ) : RepresentationPshIsoᴰ) where
    private
      ∫repr→ue : UniversalElement (TotalCat.∫C Cᴰ) (∫P Pᴰ)
      ∫repr→ue = RepresentationPshIso→UniversalElement
        (∫P Pᴰ)
        (_ , (∫PshIsoᴰ yx≅P (Cᴰ [-][-, xᴰ ]) Pᴰ yxᴰ≅Pᴰ))
      module ∫repr→ue = UniversalElementNotation ∫repr→ue

    RepresentationPshIsoᴰ→UniversalElementᴰ :
      UniversalElementᴰ Cᴰ
        (RepresentationPshIso→UniversalElement P (x , yx≅P))
        Pᴰ
    RepresentationPshIsoᴰ→UniversalElementᴰ .vertexᴰ  = ∫repr→ue.vertex .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .elementᴰ = ∫repr→ue.element .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .inv p pᴰ = ∫repr→ue.intro (p , pᴰ) .snd
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .rightInv p pᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫repr→ue.β
    RepresentationPshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $ sym $ ∫repr→ue.η

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {P : Presheaf C ℓC'} (Pᴰ : Presheafᴰ P Cᴰ ℓCᴰ')
  where
  private
    module Cᴰ = Fibers Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
  Representsᵁᴰ : ∀ {x} → Representsᵁ C P x → (xᴰ : Cᴰ.ob[ x ]) → Type _
  Representsᵁᴰ yx≡P xᴰ =
    PathP (λ i → Presheafᴰ (yx≡P i) Cᴰ ℓCᴰ')
      (Cᴰ [-][-, xᴰ ])
      Pᴰ

  Representationᵁᴰ : Representationᵁ C P → Type _
  Representationᵁᴰ (x , yx≡P) = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Representsᵁᴰ yx≡P xᴰ
  -- same but uglier:
  -- fiberOver {Q = λ P → Presheafᴰ P Cᴰ ℓCᴰ'} (x , yx≡P) (λ _ → Cᴰ [-][-,_]) Pᴰ

  ∫Reprᵁ : ∀ {repr : Representationᵁ C P} → Representationᵁᴰ repr → Representationᵁ (TotalCat.∫C Cᴰ) (∫P Pᴰ)
  ∫Reprᵁ {repr} reprᴰ .fst = repr .fst , reprᴰ .fst
  ∫Reprᵁ {repr} reprᴰ .snd = Functor≡
    (λ (c , cᴰ) → ΣPathP ((λ i → Σ (repr .snd i .F-ob c .fst) λ x → reprᴰ .snd i .F-obᴰ cᴰ x .fst) , isProp→PathP (λ _ → isPropIsSet) _ _))
    λ (f , fᴰ) → λ i (x , xᴰ) → (repr .snd i .F-hom f x) , reprᴰ .snd i .F-homᴰ fᴰ x xᴰ

  UniversalElementᴰ→Representationᵁᴰ :
    ∀ {ue : UniversalElement C P}
    → UniversalElementᴰ Cᴰ ue Pᴰ
    → Representationᵁᴰ (UniversalElement→Representationᵁ C P ue)
  UniversalElementᴰ→Representationᵁᴰ {ue} ueᴰ = ueᴰ.vertexᴰ
    , PshIsoᴰ→PathP _ _ _
    ( yoRecᴰ Pᴰ ueᴰ.elementᴰ
    , (isisoover
         (λ _ → ueᴰ.introᴰ)
         (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ ueᴰ.βᴰ)
         λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueᴰ.ηᴰ))
    where
      module ueᴰ = UniversalElementᴰ ueᴰ

  module _ {repr : Representationᵁ C P} (reprᴰ : Representationᵁᴰ repr) where
    private
      ∫repr : Representationᵁ (TotalCat.∫C Cᴰ) (∫P Pᴰ)
      ∫repr = ∫Reprᵁ reprᴰ

      ∫reprpshiso = Representationᵁ→RepresentationPshIso (TotalCat.∫C Cᴰ) (∫P Pᴰ) ∫repr

    open PshHomᴰ
    open isIsoOver
    Representationᵁᴰ→RepresentationPshIsoᴰ
      : RepresentationPshIsoᴰ Cᴰ (Representationᵁ→RepresentationPshIso C P repr) Pᴰ
    Representationᵁᴰ→RepresentationPshIsoᴰ .fst = reprᴰ .fst
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .fst .N-obᴰ pᴰ = ∫reprpshiso .snd .fst .fst _ (_ , pᴰ) .snd
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .fst .N-homᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫reprpshiso .snd .fst .snd _ _ _ _
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .inv p pᴰ =
      ∫reprpshiso .snd .snd _ .fst (p , pᴰ) .snd
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .rightInv p pᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $ ∫reprpshiso .snd .snd _ .snd .fst (p , pᴰ)
    Representationᵁᴰ→RepresentationPshIsoᴰ .snd .snd .leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $ ∫reprpshiso .snd .snd _ .snd .snd (f , fᴰ)

    Representationᵁᴰ→UniversalElementᴰ :
      UniversalElementᴰ Cᴰ (Representationᵁ→UniversalElement C P repr) Pᴰ
    Representationᵁᴰ→UniversalElementᴰ =
      RepresentationPshIsoᴰ→UniversalElementᴰ Cᴰ (Representationᵁ→RepresentationPshIso C P repr) Pᴰ
        Representationᵁᴰ→RepresentationPshIsoᴰ

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (c : C .Category.ob) (D : Categoryᴰ C ℓD ℓD')
          → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ {C = C} c D = Presheafᴰ (YO {C = C} ⟅ c ⟆) D

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshHomⱽ : Type _
  PshHomⱽ = PshHomᴰ idPshHom Pᴰ Qᴰ
  PshIsoⱽ : Type _
  PshIsoⱽ = PshIsoᴰ idPshIso Pᴰ Qᴰ

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

  -- opaque or transparent?
  pⱽ[_] : (cᴰ : Cᴰ.ob[ c ]) → Type ℓPᴰ
  pⱽ[ cᴰ ] = p[ C.id ][ cᴰ ]

  _⋆ᴰⱽ_ :
      Cᴰ [ f ][ xᴰ , cᴰ ] → pⱽ[ cᴰ ]
      → p[ f ][ xᴰ ]
  fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

  ⋆ᴰid≡⋆ᴰⱽ : ∀ (fᴰ : Cᴰ [ f ][ xᴰ , cᴰ ]) (gⱽ : pⱽ[ cᴰ ])
    → fᴰ ⋆ᴰ gⱽ ≡[ C.⋆IdR f ] fᴰ ⋆ᴰⱽ gⱽ
  ⋆ᴰid≡⋆ᴰⱽ fᴰ gⱽ = λ i → reind-filler (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ) i .snd

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafⱽNotation Pⱽ

  -- A UniversalElementⱽ is equivalent to a UniversalElementᴰ but
  -- stated in terms of Pⱽ.⋆ᴰⱽ instead of Pⱽ.⋆ᴰ, so the universality
  -- property is simpler.

  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.pⱽ[ vertexⱽ ]
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]) → fᴰ Pⱽ.⋆ᴰⱽ elementⱽ

    toUniversalᴰ : UniversalElementᴰ Cᴰ (selfUnivElt C x) Pⱽ
    toUniversalᴰ .UniversalElementᴰ.vertexᴰ = vertexⱽ
    toUniversalᴰ .UniversalElementᴰ.elementᴰ = elementⱽ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.inv f fᴰ =
      universalⱽ .fst fᴰ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.rightInv f fᴰ =
      Pⱽ.rectify $ Pⱽ.≡out $
        (Pⱽ.≡in $ Pⱽ.⋆ᴰid≡⋆ᴰⱽ _ _)
        ∙ (Pⱽ.≡in $ universalⱽ .snd .fst fᴰ)
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        (Cᴰ.≡in $ (λ i → universalⱽ .fst (Pⱽ.⋆ᴰid≡⋆ᴰⱽ fᴰ elementⱽ i)))
        ∙ (Cᴰ.≡in $ universalⱽ .snd .snd fᴰ)

    open UniversalElementᴰ toUniversalᴰ hiding (module Pshᴰ) public
    module Pshⱽ = PresheafⱽNotation Pⱽ

    introⱽ : ∀ {xᴰ} → Pⱽ.p[ C.id ][ xᴰ ] → Cᴰ.v[ x ] [ xᴰ , vertexᴰ ]
    introⱽ = introᴰ

    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : Pⱽ.p[ f ][ yᴰ ]}
      → introᴰ pᴰ Pⱽ.⋆ᴰⱽ elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introᴰ (fᴰ Pⱽ.⋆ᴰⱽ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {c} (Pⱽ : Presheafⱽ c Cᴰ ℓCᴰ')
  where
  Representationᵁⱽ : Type _
  Representationᵁⱽ = Representationᵁᴰ Cᴰ Pⱽ (_ , refl)

  -- UniversalElementⱽ→Representationᵁⱽ : UniversalElementⱽ Cᴰ c Pⱽ → Representationᵁⱽ
  -- UniversalElementⱽ→Representationᵁⱽ ueⱽ =
  --   subst (λ p → Representationᵁᴰ Cᴰ Pⱽ p)
  --     (ΣPathP (refl , {!!}))
  --     (UniversalElementᴰ→Representationᵁᴰ Cᴰ Pⱽ ueⱽ.toUniversalᴰ)
  --   where
  --     module ueⱽ = UniversalElementⱽ ueⱽ

-- Kinds of composition:
-- seqPshHomᴰ/seqPshIoᴰ
-- seqPshHom/Isoⱽᴰ, seqPshHom/Isoᴰⱽ, seqPshHom/Isoⱽ
-- seqEltPshHom, seqUEPshIso
-- invPshIsoᴰ, invPshIsoⱽ
