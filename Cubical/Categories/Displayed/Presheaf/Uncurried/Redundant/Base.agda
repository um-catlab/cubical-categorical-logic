{-

  Currently, uncurried and curried presheaves have complementary advantages.

  1. The composition operation of curried presheaves is better because it doesn't involve a path
  2. Reindexing constructions for implementing exponentialⱽ are much simpler with uncurried
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base where

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
open import Cubical.HITs.PathEq as PathEq
open import Cubical.HITs.Join as Join
open import Cubical.HITs.Join.More as Join

open import Cubical.Categories.Category.Base
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
Cᴰ / P = ∫C (Cᴰ ×ᴰ RedundElement P)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/Fᴰ_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHet' F P Q)
    → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fᴰ α = ∫F {F = F} (Fᴰ ×ᴰF PshHet'→ElementFunctorᴰ α)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{P : Presheaf C ℓP} where
  open Category
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  Hom/≡ : ∀ {Δ3 Γ3 : (Cᴰ / P).ob}
    {f g : (Cᴰ / P) [ Δ3 , Γ3 ]}
    → (p2 : f .snd .fst Cᴰ.∫≡ g .snd .fst)
    → f ≡ g
  Hom/≡ p2 = ΣPathP ((PathPΣ p2 .fst) , (ΣPathPProp (λ _ → isPropPathEq P.isSetPsh)
    (PathPΣ p2 .snd)))

  Hom/-elim : ∀ {Δ3@(Δ , Δᴰ , γp) Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob} {M : (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → Type ℓ}
    → (split : (γ : C [ Δ , Γ ])
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (γ⋆p≡γp : PathEq (γ P.⋆ p) γp)
        → M (γ , γᴰ , γ⋆p≡γp)
        )
    → (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → M f3
  Hom/-elim {ℓ}{M} split (γ , γᴰ , tri) = split γ γᴰ tri

  Hom/-rec : ∀ {M : Type ℓ}
    → {Δ3@(Δ , Δᴰ , γp) Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob}
    → (split :
        (γ : C [ Δ , Γ ])
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (γ⋆p≡γp : PathEq (γ P.⋆ p) γp)
        → M
        )
    → (f3 : (Cᴰ / P) [ Δ3 , Γ3 ]) → M
  Hom/-rec = Hom/-elim

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
  fᴰ ⋆ᴰ pᴰ = Pᴰ .F-hom (_ , fᴰ , inr Eq.refl) pᴰ

  opaque
    ⋆ᴰ-reindᴰ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (f⋆p≡q : PathEq (f P.⋆ p) q) (pᴰ : p[ p ][ yᴰ ])
      → PathP (λ i → ⟨ Pᴰ .F-ob (x , xᴰ , PathEq→Path P.isSetPsh f⋆p≡q i ) ⟩)
        (fᴰ ⋆ᴰ pᴰ)
        (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
    ⋆ᴰ-reindᴰ {x} {y} {xᴰ} {yᴰ} {f} {p} {q} fᴰ = elimPropEq P.isSetPsh
      (λ _ → isPropΠ (λ _ → isOfHLevelPathP' 1 isSetPshᴰ (fᴰ ⋆ᴰ _) (Pᴰ .F-hom (f , fᴰ , _) _)))
      λ { Eq.refl → λ _ → refl }
  ⋆ᴰ-reind : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}{fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : p[ p ][ yᴰ ]}
    → (f⋆p≡q : PathEq (f P.⋆ p) q)
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
    (pf : PathEq (P .F-hom (id C) p) q)
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
    UncurryPshᴰ .F-hom = Hom/-rec λ γ γᴰ → Join.elim
      (λ tri pᴰ → Pᴰ.reind tri (γᴰ Pᴰ.⋆ᴰ pᴰ))
      (λ { Eq.refl → γᴰ Pᴰ.⋆ᴰ_ })
      λ { tri Eq.refl → funExt λ pᴰ → Pᴰ.rectifyOut $ sym $ Pᴰ.reind-filler _ }
    UncurryPshᴰ .F-id {x} = funExt λ pᴰ → Pᴰ.rectifyOut $
      (sym $ Pᴰ.reind-filler _)
      ∙ Pᴰ.⋆IdL _
    -- clean up?
    UncurryPshᴰ .F-seq = Hom/-elim (λ γ γᴰ → elimPropPath P.isSetPsh
      (λ _ → isPropΠ (λ _ → isSet→ Pᴰ.isSetPshᴰ _ _))
      λ tri → Hom/-elim (λ δ δᴰ → elimPropPath P.isSetPsh (λ _ → isSet→ Pᴰ.isSetPshᴰ _ _)
      (λ tri' → funExt λ pᴰ → Pᴰ.rectifyOut $
        (sym $ Pᴰ.reind-filler _)
        ∙ Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ ⟩ ∙ Pᴰ.reind-filler _)))

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    CurryPshᴰ : Curried.Presheafᴰ P Cᴰ ℓPᴰ
    CurryPshᴰ .F-obᴰ {Γ} Γᴰ p = Pᴰ .F-ob (Γ , Γᴰ , p)
    CurryPshᴰ .F-homᴰ γᴰ p pᴰ = Pᴰ .F-hom (_ , (γᴰ , inr Eq.refl)) pᴰ
    CurryPshᴰ .F-idᴰ = funExt (λ p → funExt (λ pᴰ → Pᴰ.rectifyOut $ Pᴰ.⋆IdL _))
    CurryPshᴰ .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ pᴰ →
      Pᴰ.rectifyOut $ Pᴰ.⋆Assoc _ _ _

  CurryPshᴰIso : Iso (Presheafᴰ P Cᴰ ℓPᴰ) (Curried.Presheafᴰ P Cᴰ ℓPᴰ)
  CurryPshᴰIso .Iso.fun = CurryPshᴰ
  CurryPshᴰIso .Iso.inv = UncurryPshᴰ
  CurryPshᴰIso .Iso.sec Pᴰ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
  CurryPshᴰIso .Iso.ret Pᴰ = Functor≡ (λ _ → refl)
    (Hom/-elim (λ γ γᴰ → elimPropEq P.isSetPsh (λ _ → isSet→ Pᴰ.isSetPshᴰ _ _) λ { Eq.refl → refl }))
    where module Pᴰ = PresheafᴰNotation Pᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} (α : PshHom' P Q) where
  private
    module α = PshHom' α
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  Id/Fⱽ_ : Functor (Cᴰ / P) (Cᴰ / Q)
  Id/Fⱽ_ .F-ob ob/@(Γ , Γᴰ , p) = Γ , Γᴰ , α.N-ob Γ p
  Id/Fⱽ_ .F-hom = Hom/-elim (λ γ γᴰ → Join.elim
    (λ tri → γ , γᴰ , inl ((PathEq→Path Q.isSetPsh $ symPE Q.isSetPsh (α.N-hom _ _ _ _)) ∙ cong (α.N-ob _) tri))
    (λ { Eq.refl → γ , (γᴰ , symPE Q.isSetPsh (α.N-hom _ _ _ _)) })
    λ { pth Eq.refl → Hom/≡ refl })
  Id/Fⱽ_ .F-id = Hom/≡ refl
  Id/Fⱽ_ .F-seq = Hom/-elim λ f fᴰ → elimPropPath P.isSetPsh (λ _ → isPropΠ (λ _ → (Cᴰ / Q) .isSetHom _ _))
    λ ftri → Hom/-elim λ g gᴰ → elimPropPath P.isSetPsh (λ _ → (Cᴰ / Q) .isSetHom _ _) (λ gtri → Hom/≡ refl)

  module _ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    reindᴰRedundPshHom : Presheafᴰ P Cᴰ ℓQᴰ
    reindᴰRedundPshHom = reindPsh Id/Fⱽ_ Qᴰ

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
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ} where
  _×ᴰPsh_ : Presheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ Q Cᴰ ℓQᴰ → Presheafᴰ (P ×Psh Q) Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
  Pᴰ ×ᴰPsh Qᴰ = reindᴰRedundPshHom (π₁Strict P Q) Pᴰ ×ⱽPsh reindᴰRedundPshHom (π₂Strict P Q) Qᴰ

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    private
      module Cᴰ = Fibers Cᴰ
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Pᴰ×ᴰQᴰ = PresheafᴰNotation (Pᴰ ×ᴰPsh Qᴰ)
      -- this was my original motivation: to make this be refl.
      -- compare test×ᴰPsh in Displayed.Presheaf.Uncurried.Constructions
      test×ᴰPsh : ∀ {Γ x}{Γᴰ : Cᴰ.ob[ Γ ]}{xᴰ : Cᴰ.ob[ x ]}
        (p : P.p[ x ])(q : Q.p[ x ])
        (f : C [ Γ , x ])
        (fᴰ : Cᴰ [ f ][ Γᴰ , xᴰ ])
        (pᴰ : Pᴰ.p[ p ][ xᴰ ])(qᴰ : Qᴰ.p[ q ][ xᴰ ])
        → (fᴰ Pᴰ×ᴰQᴰ.⋆ᴰ (pᴰ , qᴰ)) ≡ ((fᴰ Pᴰ.⋆ᴰ pᴰ) , (fᴰ Qᴰ.⋆ᴰ qᴰ))
      test×ᴰPsh p q f fᴰ pᴰ qᴰ = refl

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

module _ {C : Category ℓC ℓC'} {x : C .ob} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafᴰNotation Pⱽ
  -- UniversalElementⱽ : Type {!!}
  -- UniversalElementⱽ = Σ[ v ∈ Cᴰ.ob[ x ] ] Σ[ e ∈ Pⱽ.p[ C.id ][ v ] ] ?

  Reprⱽ : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ)
  Reprⱽ = Σ[ v ∈ Cᴰ.ob[ x ] ] PshIso' (Cᴰ [-][-, v  ]) Pⱽ

EqAssoc : (C : Category ℓC ℓC') → Type (ℓ-max ℓC ℓC')
EqAssoc C = ∀ {w x y z} (f : C [ w , x ])(g : C [ x , y ])(h : C [ y , z ]) → (f C.⋆ g) C.⋆ h Eq.≡ (f C.⋆ (g C.⋆ h))
  where module C = Category C

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  Terminalsⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  Terminalsⱽ = ∀ (x : C.ob) → Reprⱽ (UnitⱽPsh {Cᴰ = Cᴰ}{P = C [-, x ]})

  BinProductsⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  BinProductsⱽ = ∀ {x : C.ob} (xᴰ yᴰ : Cᴰ.ob[ x ]) → Reprⱽ ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ]))

  Fibration : EqAssoc C → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  Fibration C⋆Assoc = ∀ {x y} (f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ]) → Reprⱽ (reindᴰRedundPshHom (⋆f f) (Cᴰ [-][-, yᴰ ]))
    where
      ⋆f : ∀ {x y} (f : C [ x , y ]) → PshHom' (C [-, x ]) (C [-, y ])
      ⋆f f .PshHom'.N-ob c = C._⋆ f
      ⋆f f .PshHom'.N-hom c c' δ γ = inr (C⋆Assoc δ γ f)
