{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHom
open PshIso

_/_ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP) → Category _ _
Cᴰ / P = ∫C (Cᴰ ×ᴰ EqElement P)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/Fᴰ_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHetEq F P Q)
    → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fᴰ α = ∫F {F = F} (Fᴰ ×ᴰF PshHetEq→ElementFunctorᴰ α)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{P : Presheaf C ℓP} where
  open Category
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  Hom/≡ : ∀ {Δ3 Γ3 : (Cᴰ / P).ob}
    {f g : (Cᴰ / P) [ Δ3 , Γ3 ]}
    → (p2 : f .snd .fst Cᴰ.∫≡ g .snd .fst)
    → f ≡ g
  Hom/≡ p2 = ΣPathP ((PathPΣ p2 .fst) , (ΣPathPProp (λ _ → Eq.isSet→isSetEq P.isSetPsh)
    (PathPΣ p2 .snd)))

--   Hom/-elim : ∀ {Δ3@(Δ , Δᴰ , γp) Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob} {M : (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → Type ℓ}
--     → (split : (γ : C [ Δ , Γ ])
--         → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
--         → (γ⋆p≡γp : PathEq (γ P.⋆ p) γp)
--         → M (γ , γᴰ , γ⋆p≡γp)
--         )
--     → (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → M f3
--   Hom/-elim {ℓ}{M} split (γ , γᴰ , tri) = split γ γᴰ tri

--   Hom/-rec : ∀ {M : Type ℓ}
--     → {Δ3@(Δ , Δᴰ , γp) Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob}
--     → (split :
--         (γ : C [ Δ , Γ ])
--         → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
--         → (γ⋆p≡γp : PathEq (γ P.⋆ p) γp)
--         → M
--         )
--     → (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → M
--   Hom/-rec = Hom/-elim

Presheafᴰ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           → (ℓPᴰ : Level)
           → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCᴰ') (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} P Cᴰ ℓPᴰ = Presheaf (Cᴰ / P) ℓPᴰ

module PresheafᴰNotation
  {C : Category ℓC ℓC'} {P : Presheaf C ℓP} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ f ][ xᴰ ] = ⟨ Pᴰ .F-ob (_ , xᴰ , f) ⟩

  isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
  isSetPshᴰ {x} {p} {xᴰ} = Pᴰ .F-ob (x , xᴰ , p) .snd
  module _ {x}{xᴰ : Cᴰ.ob[ x ]} where
    open hSetReasoning (P .F-ob x) p[_][ xᴰ ] renaming (_P≡[_]_ to _≡[_]_; Prectify to rectify) public

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (pᴰ : p[ p ][ yᴰ ])
    → p[ f P.⋆ p ][ xᴰ ]
  fᴰ ⋆ᴰ pᴰ = Pᴰ .F-hom (_ , fᴰ , Eq.refl) pᴰ

  opaque
    ⋆ᴰ-reindᴰ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (f⋆p≡q : (f P.⋆ p) Eq.≡ q) (pᴰ : p[ p ][ yᴰ ])
      → PathP (λ i → ⟨ Pᴰ .F-ob (x , xᴰ , Eq.eqToPath f⋆p≡q i ) ⟩)
        (fᴰ ⋆ᴰ pᴰ)
        (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
    ⋆ᴰ-reindᴰ {x} {y} {xᴰ} {yᴰ} {f} {p} {q} fᴰ Eq.refl pᴰ = refl
  ⋆ᴰ-reind : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}{fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : p[ p ][ yᴰ ]}
    → (f⋆p≡q : (f P.⋆ p) Eq.≡ q)
    → (fᴰ ⋆ᴰ pᴰ) ∫≡ (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
  ⋆ᴰ-reind f⋆p≡q = ≡in $ ⋆ᴰ-reindᴰ _ f⋆p≡q _

  ⋆IdLᴰ :
    ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p}
    {pᴰ : p[ p ][ xᴰ ]}
    → Cᴰ.idᴰ ⋆ᴰ pᴰ ∫≡ pᴰ
  ⋆IdLᴰ = ⋆ᴰ-reind _ ∙ (≡in $ funExt⁻ (Pᴰ .F-id) _)

  ⋆Assocᴰ : ∀ {x y z}{xᴰ yᴰ zᴰ}{f : C [ z , y ]}{g : C [ y , x ]}{p : P.p[ x ]}
    (fᴰ : Cᴰ [ f ][ zᴰ , yᴰ ])
    (gᴰ : Cᴰ [ g ][ yᴰ , xᴰ ])
    (pᴰ : p[ p ][ xᴰ ])
    → ((fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ pᴰ) ∫≡ (fᴰ ⋆ᴰ gᴰ ⋆ᴰ pᴰ)
  ⋆Assocᴰ {x} {y} {z} {xᴰ} {yᴰ} {zᴰ} {f} {g} {p} fᴰ gᴰ pᴰ =
    (⋆ᴰ-reind _)
    ∙ ≡in (funExt⁻ (Pᴰ .F-seq (g , gᴰ , _) (f , fᴰ , _)) pᴰ)

  formal-reind-filler :
    ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p q}
    {pᴰ : p[ p ][ xᴰ ]}
    (pf : (P .F-hom (C .id) p) Eq.≡ q)
    → pᴰ ∫≡ Pᴰ .F-hom (_ , Cᴰ.idᴰ , pf) pᴰ
  formal-reind-filler pf = (sym $ ⋆IdLᴰ) ∙ ⋆ᴰ-reind pf

  ∫ : Presheaf (∫C Cᴰ) (ℓ-max ℓP ℓPᴰ)
  ∫ .F-ob (x , xᴰ) .fst = Σ _ p[_][ xᴰ ]
  ∫ .F-ob (x , xᴰ) .snd = isSetΣ P.isSetPsh (λ _ → isSetPshᴰ)
  ∫ .F-hom (f , fᴰ) (p , pᴰ) = _ , fᴰ ⋆ᴰ pᴰ
  ∫ .F-id = funExt λ _ → ⋆IdLᴰ
  ∫ .F-seq f g = funExt λ _ → ⋆Assocᴰ _ _ _

  open PresheafNotation ∫ public

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module P = PresheafNotation P
  module _ (Pᴰ : Curried.Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = Curried.PresheafᴰNotation Pᴰ
    UncurryPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ
    UncurryPshᴰ .F-ob ob/@(Γ , Γᴰ , p) = Pᴰ .F-obᴰ Γᴰ p
    UncurryPshᴰ .F-hom hom/@(γ , γᴰ , tri) pᴰ = Pᴰ.reindEq tri (γᴰ Pᴰ.⋆ᴰ pᴰ)
    UncurryPshᴰ .F-id {x = x} = funExt (λ pᴰ → Pᴰ.rectifyOut $
      sym (Pᴰ.reindEq-filler (Eq.pathToEq $ P.⋆IdL _))
      ∙ Pᴰ.⋆IdL _)
    UncurryPshᴰ .F-seq f/@(δ , δᴰ , Eq.refl) g/@(γ , γᴰ , Eq.refl) = funExt λ pᴰ → Pᴰ.rectifyOut $
      (sym (Pᴰ.reindEq-filler (Eq.pathToEq $ P.⋆Assoc _ _ _)) ∙ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reindEq-filler _ ⟩) ∙ Pᴰ.reindEq-filler _

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    CurryPshᴰ : Curried.Presheafᴰ P Cᴰ ℓPᴰ
    CurryPshᴰ .F-obᴰ {Γ} Γᴰ p = Pᴰ .F-ob (Γ , Γᴰ , p)
    CurryPshᴰ .F-homᴰ γᴰ p pᴰ = γᴰ Pᴰ.⋆ᴰ pᴰ
    CurryPshᴰ .F-idᴰ = funExt λ p → funExt λ pᴰ → Pᴰ.rectifyOut $ Pᴰ.⋆IdL _
    CurryPshᴰ .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ pᴰ → Pᴰ.rectifyOut $ Pᴰ.⋆Assoc _ _ _

  CurryPshᴰIso : Iso (Presheafᴰ P Cᴰ ℓPᴰ) (Curried.Presheafᴰ P Cᴰ ℓPᴰ)
  CurryPshᴰIso .Iso.fun = CurryPshᴰ
  CurryPshᴰIso .Iso.inv = UncurryPshᴰ
  CurryPshᴰIso .Iso.sec Pᴰ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
  CurryPshᴰIso .Iso.ret Pᴰ = Functor≡ (λ _ → refl) λ { (_ , _ , Eq.refl ) → refl }

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  module _ (Fᴰ : Functorⱽ Cᴰ Dᴰ) (α : PshHomEq P Q) where
    _/Fⱽ_ :  Functor (Cᴰ / P) (Dᴰ / Q)
    _/Fⱽ_ = Fᴰ /Fᴰ (α ⋆PshHomEq (PshIsoEq.toPshHomEq $ reindPshEqId≅ Q))

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  _*Presheafᴰ_ : (α : PshHomEq P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) → Presheafᴰ P Cᴰ ℓQᴰ
  α *Presheafᴰ Qᴰ = reindPsh (Idᴰ /Fⱽ α) Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} where
  UnitⱽPsh : Presheafᴰ P Cᴰ ℓ-zero
  UnitⱽPsh = UnitPsh

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  UnitᴰPsh : Presheafᴰ UnitPsh Cᴰ ℓ-zero
  UnitᴰPsh = UnitPsh

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} where
  _×ⱽPsh_ : Presheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ P Cᴰ ℓQᴰ → Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
  _×ⱽPsh_ = _×Psh_
-- module _
--   {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ} where
--   -- This is why we Eq
--   _×ᴰPsh_ : Presheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ Q Cᴰ ℓQᴰ → Presheafᴰ (P ×Psh Q) Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
--   Pᴰ ×ᴰPsh Qᴰ = reindᴰRedundPshHom (π₁Strict P Q) Pᴰ ×ⱽPsh reindᴰRedundPshHom (π₂Strict P Q) Qᴰ

--   module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
--     private
--       module Cᴰ = Fibers Cᴰ
--       module P = PresheafNotation P
--       module Q = PresheafNotation Q
--       module Pᴰ = PresheafᴰNotation Pᴰ
--       module Qᴰ = PresheafᴰNotation Qᴰ
--       module Pᴰ×ᴰQᴰ = PresheafᴰNotation (Pᴰ ×ᴰPsh Qᴰ)
--       -- this was my original motivation: to make this be refl.
--       -- compare test×ᴰPsh in Displayed.Presheaf.Uncurried.Constructions
--       test×ᴰPsh : ∀ {Γ x}{Γᴰ : Cᴰ.ob[ Γ ]}{xᴰ : Cᴰ.ob[ x ]}
--         (p : P.p[ x ])(q : Q.p[ x ])
--         (f : C [ Γ , x ])
--         (fᴰ : Cᴰ [ f ][ Γᴰ , xᴰ ])
--         (pᴰ : Pᴰ.p[ p ][ xᴰ ])(qᴰ : Qᴰ.p[ q ][ xᴰ ])
--         → (fᴰ Pᴰ×ᴰQᴰ.⋆ᴰ (pᴰ , qᴰ)) ≡ ((fᴰ Pᴰ.⋆ᴰ pᴰ) , (fᴰ Qᴰ.⋆ᴰ qᴰ))
--       test×ᴰPsh p q f fᴰ pᴰ qᴰ = refl

module _ {C : Category ℓC ℓC'} {x : C .ob} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
  _[-][-,_] : (xᴰ : Cᴰ.ob[ x ]) → Presheafᴰ (C [-, x ]) Cᴰ ℓCᴰ'
  _[-][-,_] xᴰ = UncurryPshᴰ (Cᴰ Setᴰ.[-][-, xᴰ ])

module _ {C : Category ℓC ℓC'} (x : C .ob) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
  Presheafⱽ : (ℓPᴰ : Level) → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') (ℓ-suc ℓPᴰ))
  Presheafⱽ = Presheafᴰ (C [-, x ]) Cᴰ

EqAssoc : (C : Category ℓC ℓC') → Type (ℓ-max ℓC ℓC')
EqAssoc C = ∀ {w x y z} (f : C [ w , x ])(g : C [ x , y ])(h : C [ y , z ]) → (f C.⋆ g) C.⋆ h Eq.≡ (f C.⋆ (g C.⋆ h))
  where module C = Category C

ReprEqAssoc : (C : Category ℓC ℓC') → Type (ℓ-max ℓC ℓC')
ReprEqAssoc C = ∀ x → PshAssocEq (C [-, x ])

EqIdR : (C : Category ℓC ℓC') → Type (ℓ-max ℓC ℓC')
EqIdR C = ∀ {x y} (f : C [ x , y ]) → f C.⋆ C.id Eq.≡ f
  where module C = Category C

EqIdL : (C : Category ℓC ℓC') → Type (ℓ-max ℓC ℓC')
EqIdL C = ∀ {x y} (f : C [ x , y ]) → C.id C.⋆ f Eq.≡ f
  where module C = Category C

module _ {C : Category ℓC ℓC'} {x : C .ob} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafᴰNotation Pⱽ

  Reprⱽ : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ)
  Reprⱽ = Σ[ v ∈ Cᴰ.ob[ x ] ] PshIsoEq (Cᴰ [-][-, v  ]) Pⱽ
  module _ (C⋆IdR : EqIdR C) where
    yoRecⱽ : ∀ {xᴰ}
      → Pⱽ.p[ C.id ][ xᴰ ]
      → PshHomEq (Cᴰ [-][-, xᴰ ]) Pⱽ
    -- there are two choices here: we can either eliminate C⋆IdR f ourselves or pass it to Pⱽ to do so.
    yoRecⱽ pⱽ .PshHomEq.N-ob ob/@(Γ , Γᴰ , f) fᴰ = Pⱽ .F-hom (f , fᴰ , C⋆IdR f) pⱽ
    -- opaque reindEq stuck on Eq.refl noooo
    yoRecⱽ pⱽ .PshHomEq.N-hom Δ3 Γ3 f@(γ , γᴰ , Eq.refl) p' p = {!Pⱽ.⋆Assoc _ _ _!}

    record UEⱽ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
      no-eta-equality
      field
        v : Cᴰ.ob[ x ]
        e : Pⱽ.p[ C.id ][ v ]
        universal : isPshIsoEq (Cᴰ [-][-, v ]) Pⱽ (yoRecⱽ e)

    open UEⱽ
    UEⱽ→Reprⱽ : UEⱽ → Reprⱽ
    UEⱽ→Reprⱽ ueⱽ .fst = ueⱽ .v
    UEⱽ→Reprⱽ ueⱽ .snd .PshIsoEq.isos ob/@(Γ , Γᴰ , f) .Iso.fun = λ z → Pⱽ .F-hom (f , z , C⋆IdR f) (ueⱽ .e)
    UEⱽ→Reprⱽ ueⱽ .snd .PshIsoEq.isos ob/@(Γ , Γᴰ , f) .Iso.inv = ueⱽ .universal .isPshIsoEq.nIso (Γ , Γᴰ , f) .fst
    UEⱽ→Reprⱽ ueⱽ .snd .PshIsoEq.isos ob/@(Γ , Γᴰ , f) .Iso.sec = ueⱽ .universal .isPshIsoEq.nIso (Γ , Γᴰ , f) .snd .fst
    UEⱽ→Reprⱽ ueⱽ .snd .PshIsoEq.isos ob/@(Γ , Γᴰ , f) .Iso.ret = ueⱽ .universal .isPshIsoEq.nIso (Γ , Γᴰ , f) .snd .snd
    UEⱽ→Reprⱽ ueⱽ .snd .PshIsoEq.nat = yoRecⱽ (ueⱽ .e) .PshHomEq.N-hom



module _ {C : Category ℓC ℓC'} {x : C .ob} (bp : BinProductsWith C x) where
  private
    module C = Category C
    module bp = BinProductsWithNotation bp
  π₁NatEq : Type _
  π₁NatEq = ∀ {Δ Γ} (γ : C [ Δ , Γ ]) → bp.×aF ⟪ γ ⟫ C.⋆ bp.π₁ Eq.≡ bp.π₁ C.⋆ γ

  ×aF-seq : Type _
  ×aF-seq = ∀ {Θ}{Δ}{Γ}(δ : C [ Θ , Δ ])(γ : C [ Δ , Γ ]) → bp.×aF ⟪ δ C.⋆ γ ⟫ Eq.≡ (bp.×aF ⟪ δ ⟫ C.⋆ bp.×aF ⟪ γ ⟫)

module _ {C : Category ℓC ℓC'} (bp : BinProducts C) where
  Allπ₁NatEq : Type _
  Allπ₁NatEq = ∀ x → π₁NatEq {x = x} (λ c → bp (c , x))
  All×aF-seq : Type _
  All×aF-seq = ∀ x → ×aF-seq {x = x} (λ c → bp (c , x))

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  Terminalsⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  Terminalsⱽ = ∀ (x : C.ob) → Reprⱽ (UnitⱽPsh {Cᴰ = Cᴰ}{P = C [-, x ]})

  BinProductsⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  BinProductsⱽ = ∀ {x : C.ob} (xᴰ yᴰ : Cᴰ.ob[ x ]) → Reprⱽ ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ]))

  module _ (C⋆IdR : EqIdR C) where
    BinProductsⱽUE : Type _
    BinProductsⱽUE = ∀ {x : C.ob} (xᴰ yᴰ : Cᴰ.ob[ x ]) → UEⱽ ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ])) C⋆IdR

  module _ (C⋆Assoc : ReprEqAssoc C) where
    Fibration : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    Fibration = ∀ {x y} (f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ])
      → Reprⱽ (yoRecEq (C [-, y ]) (C⋆Assoc y) f *Presheafᴰ (Cᴰ [-][-, yᴰ ]))

    LRⱽ : {x : C.ob} (xᴰ : Cᴰ.ob[ x ]) → Type _
    LRⱽ {x} xᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (f : C [ Γ , x ])
      → Reprⱽ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh (yoRecEq _ (C⋆Assoc x) f *Presheafᴰ (Cᴰ [-][-, xᴰ ])))

    AllLRⱽ : Type _
    AllLRⱽ = ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → LRⱽ xᴰ

    BPⱽ+Fibration→AllLRⱽ : BinProductsⱽ → Fibration → AllLRⱽ
    BPⱽ+Fibration→AllLRⱽ _×ⱽ_ _*_ xᴰ Γᴰ f .fst = (Γᴰ ×ⱽ (f * xᴰ) .fst) .fst
    BPⱽ+Fibration→AllLRⱽ _×ⱽ_ _*_ xᴰ Γᴰ f .snd =
      -- One of these things has a transport, but which one(!)
      (Γᴰ ×ⱽ (f * xᴰ) .fst) .snd
      ⋆PshIsoEq ×PshIsoEq idPshIsoEq ((f * xᴰ) .snd)

    module _ (C⋆IdL : EqIdL C) {x : C.ob} (xᴰ : Cᴰ.ob[ x ]) (_×ⱽ_*xᴰ : LRⱽ xᴰ) where
      LRⱽFⱽ : Functorⱽ (Cᴰ ×ᴰ EqElement (C [-, x ])) Cᴰ
      LRⱽFⱽ .F-obᴰ ob/@(Γᴰ , f) = (Γᴰ ×ⱽ f *xᴰ) .fst
      LRⱽFⱽ .F-homᴰ {Δ} {Γ} {γ} {(Δᴰ , g)} {Γᴰ , f} (γᴰ , Eq.refl) =
        (Γᴰ ×ⱽ f *xᴰ) .snd .PshIsoEq.isos _ .Iso.inv
          ( Cᴰ.reindEq (C⋆IdL γ) (Iso.fun
                             ((Δᴰ ×ⱽ (C [-, x ]) .F-hom γ f *xᴰ) .snd .PshIsoEq.isos
                              (Δ , F-obᴰ LRⱽFⱽ (Δᴰ , (C [-, x ]) .F-hom γ f) , C.id))
                             Cᴰ.idᴰ .fst Cᴰ.⋆ᴰ γᴰ)
          , Cᴰ.reindEq (C⋆IdL (γ C.⋆ f)) (Iso.fun
                             ((Δᴰ ×ⱽ (C [-, x ]) .F-hom γ f *xᴰ) .snd .PshIsoEq.isos
                              (Δ , (Δᴰ ×ⱽ (C [-, x ]) .F-hom γ f *xᴰ) .fst , C.id))
                             Cᴰ.idᴰ .snd))
      LRⱽFⱽ .F-idᴰ = {!!}
      LRⱽFⱽ .F-seqᴰ = {!!}

      -- Technically this could be implemented as bp.×aF but I'm not sure if it would be as nice definitionally.
      -- TODO: experiment and see if we can make bp.×aF compute nicely
      LRⱽF : Functor (Cᴰ / (C [-, x ])) (Cᴰ / (C [-, x ]))
      LRⱽF = ∫F {F = Id} (LRⱽFⱽ ,Fⱽ (Sndⱽ Cᴰ (EqElement (C [-, x ]))))

      Exponentiatingⱽ : Type _
      Exponentiatingⱽ = ∀ (yᴰ : Cᴰ.ob[ x ]) → Reprⱽ (reindPsh LRⱽF (Cᴰ [-][-, yᴰ ]))

      ExponentiatingⱽUE : (C⋆IdR : EqIdR C)  → Type _
      ExponentiatingⱽUE C⋆IdR = ∀ (yᴰ : Cᴰ.ob[ x ]) → UEⱽ (reindPsh LRⱽF (Cᴰ [-][-, yᴰ ])) C⋆IdR
    Exponentialsⱽ : (C⋆IdL : EqIdL C) → AllLRⱽ → Type _
    Exponentialsⱽ C⋆IdL allLRⱽ = ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Exponentiatingⱽ C⋆IdL xᴰ (allLRⱽ xᴰ)
  module _ (C⋆IdL : EqIdL C)(C⋆Assoc : ReprEqAssoc C) (isFib : Fibration C⋆Assoc) x (bp : BinProductsWith C x) where
    private
      module bp = BinProductsWithNotation bp

    module _ (π₁NatEqC : π₁NatEq bp) where
      π1*F : Functorᴰ bp.×aF Cᴰ Cᴰ
      π1*F .F-obᴰ {Γ} Γᴰ = isFib bp.π₁ Γᴰ .fst
--       -- γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]
--       -- -----------------------
--       -- π1*.π ⋆ γᴰ : Cᴰ [ (π₁ ⋆ γ , π₂) ⋆ π₁ ][ π₁* Δᴰ , Γᴰ ]
--       -- -----------------------
--       -- π₁*-intro : Cᴰ [ (π₁ ⋆ γ , π₂) ][ π₁* Δᴰ , π₁* Γᴰ ]
      π1*F .F-homᴰ {Δ} {Γ} {γ} {Δᴰ} {Γᴰ} γᴰ = isFib bp.π₁ Γᴰ .snd .PshIsoEq.isos _ .Iso.inv
        (Cᴰ.reindEq (Eq.sym $ π₁NatEqC γ) (Cᴰ.reindEq (C⋆IdL (bp.×ue.element .fst)) (isFib (bp.×ue.element .fst) Δᴰ .snd .PshIsoEq.isos
                                                            (bp.×ue.vertex , isFib (bp.×ue.element .fst) Δᴰ .fst , C.id) .Iso.fun Cᴰ.idᴰ) Cᴰ.⋆ᴰ γᴰ))
      π1*F .F-idᴰ = {!!}
      π1*F .F-seqᴰ = {!!}
      module _ (×aF-seqC : ×aF-seq bp) where
        module _ Γ where
          wkPshHetEq : PshHetEq bp.×aF (C [-, Γ ]) (C [-, Γ bp.×a ])
          wkPshHetEq .PshHomEq.N-ob = λ Δ γ → (bp.π₁ C.⋆ γ) bp.,p bp.π₂
          wkPshHetEq .PshHomEq.N-hom Θ Δ δ γ p Eq.refl = Eq.sym $ ×aF-seqC δ γ

          wkF : Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, Γ bp.×a ]))
          wkF = π1*F /Fᴰ wkPshHetEq

        UniversallyQuantifiable : Type _
        UniversallyQuantifiable = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ bp.×a ]) → Reprⱽ (reindPsh (wkF Γ) (Cᴰ [-][-, Γᴰ ]))
  module _ (C⋆IdL : EqIdL C)(C⋆Assoc : ReprEqAssoc C) (isFib : Fibration C⋆Assoc) (bp : BinProducts C) (π₁NatEqC : Allπ₁NatEq bp)(×aF-F-homC : All×aF-seq bp) where
    UniversalQuantifiers : Type _
    UniversalQuantifiers = ∀ x → UniversallyQuantifiable C⋆IdL C⋆Assoc isFib x (λ c → bp (c , x)) (π₁NatEqC x) (×aF-F-homC x)

module _ {C : Category ℓC ℓC'} (⋆AssocC : ReprEqAssoc C) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  isCartesianⱽ : Type _
  isCartesianⱽ = Σ[ termsⱽ ∈ Terminalsⱽ Cᴰ ] Σ[ bpⱽ ∈ BinProductsⱽ Cᴰ ] Fibration Cᴰ ⋆AssocC

  isCartesianClosedⱽ : (⋆IdLC : EqIdL C) (bp : BinProducts C) (π₁NatEqC : Allπ₁NatEq bp)(×aF-F-homC : All×aF-seq bp) → Type _
  isCartesianClosedⱽ ⋆IdLC bp π₁NatEqC ×aF-F-homC =
    Σ[ (termsⱽ , bpⱽ , cartLifts) ∈ isCartesianⱽ ]
    Exponentialsⱽ Cᴰ ⋆AssocC ⋆IdLC (BPⱽ+Fibration→AllLRⱽ Cᴰ ⋆AssocC bpⱽ cartLifts)
    × UniversalQuantifiers Cᴰ ⋆IdLC ⋆AssocC cartLifts bp π₁NatEqC ×aF-F-homC
