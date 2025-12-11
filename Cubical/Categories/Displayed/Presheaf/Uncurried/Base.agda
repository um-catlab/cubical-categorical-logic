{-

  Our main definition of a displayed presheaf Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ
  is a displayed functor over the presheaf P:

  Pᴰ : Cᴰ ^opᴰ → Setᴰ ℓPᴰ
  |    |          |
  P  : C  ^op → Set ℓP

  This formulation makes defining "displayed" constructions very easy, e.g., see the displayed exponential, which can be modeled directly on the exponential of Presheaves.

  However, certain constructions on displayed presheaves are quite awkward when formulated this way, especially the *vertical* exponentials and the universal quantifier.

  The difficulty is that the output displayed presheaf depends on not just objects x : C and xᴰ : Cᴰ.ob[ x ], but also on an element p : P.p[ x ]. Constructions like the vertical exponential use the element p in a non-trivial way by reindexing a presheaf. But there doesn't seem to be any way to directly express that reindexing as itself some kind of functor in a way we can use with this formulation, because the dependency on p is part of the definition of Setᴰ.

  What we need is an "uncurried" definition of a displayed presheaf, where the p : P.p[ x ] part is expressed in the domain of an ordinary presheaf:

    Pᴰ : (x : C , xᴰ : Cᴰ.ob[ x ], p : P.p[ x ])^op → Set ℓPᴰ

  The category in the domain here can be defined using compositional constructions: the category of elements of P displayed over C, vertical product of displayed categories and total categories.

  Then we can define an isomorphism between our original "curried" definition and this "uncurried" one.
  Further, this extends to an isomorphism of categories: natural transformations between uncurried displayed presheaves correspond to *vertical* natural transformations between curried displayed presheaves. This means that all *vertical* universal properties can be expressed in terms of either curried or uncurried displayed presheaves.

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt as Alt
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
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

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
open NatTrans
open NatIso
open PshHom
open PshIso

-- TODO: better name?
_/_ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP) → Category _ _
Cᴰ / P = ∫C (Cᴰ ×ᴰ Element P)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/Fᴰ_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHet F P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fᴰ α = ∫F {F = F} (Fᴰ ×ᴰF PshHet→ElementFunctorᴰ α)
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}{Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}{R : Presheaf E ℓR}
  {F : Functor C D}{G : Functor D E}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (α : PshHet F P Q)
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
  (β : PshHet G Q R)
  where
  /Fᴰ-seq : (Gᴰ /Fᴰ β) ∘F (Fᴰ /Fᴰ α) ≡ ((Gᴰ ∘Fᴰ Fᴰ) /Fᴰ (α ⋆PshHet β))
  /Fᴰ-seq = Functor≡ (λ _ → refl) (λ (f , fᴰ , f⋆p≡p') →
    ΣPathP (refl , (ΣPathPProp (λ _ → PresheafNotation.isSetPsh R _ _) refl)) )

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  where
  _/FᴰYo_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (x : C .ob) → Functor (Cᴰ / (C [-, x ])) (Dᴰ / (D [-, F ⟅ x ⟆ ]))
  Fᴰ /FᴰYo x = Fᴰ /Fᴰ Functor→PshHet F x

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  _/Fⱽ_ : (Fᴰ : Functorⱽ Cᴰ Dᴰ) (α : PshHom P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fⱽ α = Fᴰ /Fᴰ (α ⋆PshHom reindPshId≅ Q .trans)
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{D : Category ℓD ℓD'} {P : Presheaf C ℓP}
  where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  -- TODO: generalize to ×ᴰ
  /NatTrans : {F G : Functor D (Cᴰ / P)}
    → (α : NatTrans (Fst ∘F F) (Fst ∘F G))
    → (αᴰ : NatTransᴰ α (Fstⱽ Cᴰ (Element P) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd F)) (Fstⱽ Cᴰ (Element P) ∘Fⱽᴰ (Unitᴰ.recᴰ (compSectionFunctor Snd G))))
    → (αP : ∀ x → α .N-ob x P.⋆ (G ⟅ x ⟆) .snd .snd ≡ (F ⟅ x ⟆) .snd .snd )
    → NatTrans F G
  /NatTrans α αᴰ αP .N-ob x = (α .N-ob x) , (αᴰ .NatTransᴰ.N-obᴰ tt) , (αP x)
  /NatTrans α αᴰ αP .N-hom {x}{y} f = ΣPathP ((N-hom α f) , (ΣPathPProp (λ _ → P.isSetPsh _ _)
    (αᴰ .NatTransᴰ.N-homᴰ tt)))

  /NatIso : {F G : Functor D (Cᴰ / P)}
    → (α : NatIso (Fst ∘F F) (Fst ∘F G))
    → (αᴰ : NatIsoᴰ α (Fstⱽ Cᴰ (Element P) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd F)) (Fstⱽ Cᴰ (Element P) ∘Fⱽᴰ (Unitᴰ.recᴰ (compSectionFunctor Snd G))))
    → (αP : ∀ x → α .trans .N-ob x P.⋆ (G ⟅ x ⟆) .snd .snd ≡ (F ⟅ x ⟆) .snd .snd )
    → NatIso F G
  /NatIso α αᴰ αP = record { trans = /NatTrans (α .trans) (αᴰ .NatIsoᴰ.transᴰ) αP
    ; nIso = λ x → isiso ((α .nIso x .isIso.inv) , ((αᴰ .NatIsoᴰ.nIsoᴰ tt .isIsoᴰ.invᴰ)
      , ((P.⟨⟩⋆⟨ sym $ αP x ⟩ ∙ (sym $ P.⋆Assoc _ _ _)) ∙ P.⟨ α .nIso x .isIso.sec ⟩⋆⟨⟩) ∙ P.⋆IdL _))
      (ΣPathP ((α .nIso x .isIso.sec) , (ΣPathPProp (λ _ → P.isSetPsh _ _) (αᴰ .NatIsoᴰ.nIsoᴰ tt .isIsoᴰ.secᴰ))))
      (ΣPathP ((α .nIso x .isIso.ret) , (ΣPathPProp (λ _ → P.isSetPsh _ _) (αᴰ .NatIsoᴰ.nIsoᴰ tt .isIsoᴰ.retᴰ))))
    }

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  where
  /FⱽId : Idᴰ {Cᴰ = Cᴰ} /Fⱽ idPshHom {P = P} ≡ Id
  /FⱽId = Functor≡ (λ _ → refl) (λ f → ΣPathP (refl , (ΣPathPProp (λ _ → PresheafNotation.isSetPsh P _ _) refl)))

-- Interestingly, this one is at a lower universe level than Curried.Presheafᴰ
-- Use modules to distinguish this from Curried.Presheafᴰ
Presheafᴰ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           → (ℓPᴰ : Level)
           → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCᴰ') (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} P Cᴰ ℓPᴰ = Presheaf (Cᴰ / P) ℓPᴰ

PresheafᴰCategory : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') → (ℓPᴰ : Level)
  → Category _ _
PresheafᴰCategory P Cᴰ ℓPᴰ = PresheafCategory (Cᴰ / P) ℓPᴰ

Presheafⱽ : {C : Category ℓC ℓC'} (x : C .ob)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           → (ℓPᴰ : Level)
           → Type _
Presheafⱽ {C = C} x = Presheafᴰ (C [-, x ])

module PresheafᴰNotation {C : Category ℓC ℓC'}
  -- Cᴰ and P *must* be supplied, Cᴰ for type-checking and P for performance.
  -- revisit this once no-eta-equality for categories is turned on
  (Cᴰ : Categoryᴰ C ℓD ℓD')
  (P : Presheaf C ℓP)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ p ][ xᴰ ] = ⟨ Pᴰ .F-ob (_ , xᴰ , p) ⟩

  isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
  isSetPshᴰ = Pᴰ .F-ob _ .snd

  module pReasoning {x}{xᴰ : Cᴰ.ob[ x ]} = hSetReasoning (P .F-ob x) p[_][ xᴰ ]
  open pReasoning renaming (_P≡[_]_ to _≡[_]_; Prectify to rectify) public

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (pᴰ : p[ p ][ yᴰ ])
    → p[ f P.⋆ p ][ xᴰ ]
  fᴰ ⋆ᴰ pᴰ = Pᴰ .F-hom (_ , fᴰ , refl) pᴰ

  formal-reind : ∀ {x xᴰ}{p p' : P.p[ x ]}(p≡p' : p ≡ p')(pᴰ : p[ p ][ xᴰ ])
    → p[ p' ][ xᴰ ]
  formal-reind {p = p} p≡p' = Pᴰ .F-hom (C.id , Cᴰ.idᴰ , P.⋆IdL p ∙ p≡p')

  opaque
    ⋆ᴰ-reindᴰ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (f⋆p≡q : f P.⋆ p ≡ q) (pᴰ : p[ p ][ yᴰ ])
      → PathP (λ i → ⟨ Pᴰ .F-ob (x , xᴰ , f⋆p≡q i ) ⟩)
        (fᴰ ⋆ᴰ pᴰ)
        (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
    ⋆ᴰ-reindᴰ {x}{y}{xᴰ}{yᴰ} {f = f}{p}{q} fᴰ f⋆p≡q pᴰ i = Pᴰ .F-hom (f , fᴰ , λ j → f⋆p≡q (i ∧ j)) pᴰ

    -- TODO: make this ⋆ᴰ-reind
    ⋆ᴰ-reind : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (f⋆p≡q : f P.⋆ p ≡ q) (pᴰ : p[ p ][ yᴰ ])
      → Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ ∫≡ (fᴰ ⋆ᴰ pᴰ)
    ⋆ᴰ-reind fᴰ f⋆p≡q pᴰ =
      sym $ ≡in $ ⋆ᴰ-reindᴰ fᴰ f⋆p≡q pᴰ

    ⋆IdLᴰ : ∀ {x}{xᴰ}{p : P.p[ x ]}(pᴰ : p[ p ][ xᴰ ])
      → (Pᴰ .F-hom (C.id , Cᴰ.idᴰ , refl {x = C.id P.⋆ p}) pᴰ) ∫≡ pᴰ
    ⋆IdLᴰ {x}{xᴰ}{p} pᴰ =
      (sym $ ⋆ᴰ-reind Cᴰ.idᴰ _ pᴰ)
      ∙ (≡in $ funExt⁻ (Pᴰ .F-id) pᴰ)

    formal-reind-filler : ∀ {x xᴰ}{p q : P.p[ x ]}(id⋆p≡q : C.id P.⋆ p ≡ q) (pᴰ : p[ p ][ xᴰ ])
      → Pᴰ .F-hom (C.id , Cᴰ.idᴰ , id⋆p≡q) pᴰ ∫≡ pᴰ
    formal-reind-filler {x} {xᴰ} {p} {q} id⋆p≡q pᴰ = ⋆ᴰ-reind Cᴰ.idᴰ id⋆p≡q pᴰ ∙ ⋆IdLᴰ pᴰ

    ⋆Assocᴰ : ∀ {x y z}{xᴰ yᴰ zᴰ}{f : C [ z , y ]}{g : C [ y , x ]}{p : P.p[ x ]}
      (fᴰ : Cᴰ [ f ][ zᴰ , yᴰ ])
      (gᴰ : Cᴰ [ g ][ yᴰ , xᴰ ])
      (pᴰ : p[ p ][ xᴰ ])
      → ((fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ pᴰ) ∫≡ (fᴰ ⋆ᴰ gᴰ ⋆ᴰ pᴰ)
    ⋆Assocᴰ {x} {y} {z} {xᴰ} {yᴰ} {zᴰ} {f} {g} {p} fᴰ gᴰ pᴰ =
      (sym $ ⋆ᴰ-reind (fᴰ Cᴰ.⋆ᴰ gᴰ) _ pᴰ)
      ∙ ≡in (funExt⁻ (Pᴰ .F-seq (g , gᴰ , refl) (f , fᴰ , refl)) pᴰ)

  ∫ : Presheaf (∫C Cᴰ) (ℓ-max ℓP ℓPᴰ)
  ∫ .F-ob (x , xᴰ) .fst = Σ[ p ∈ _ ] p[ p ][ xᴰ ]
  ∫ .F-ob (x , xᴰ) .snd = isSetΣ P.isSetPsh (λ _ → isSetPshᴰ)
  ∫ .F-hom (f , fᴰ) (p , pᴰ) = (f P.⋆ p) , (fᴰ ⋆ᴰ pᴰ)
  ∫ .F-id = funExt λ _ → ⋆IdLᴰ _
  ∫ .F-seq _ _ = funExt λ _ → ⋆Assocᴰ _ _ _

  open PresheafNotation ∫ public

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshHomⱽ : Type _
  PshHomⱽ = PshHom Pᴰ Qᴰ

  PshIsoⱽ : Type _
  PshIsoⱽ = PshIso Pᴰ Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  reindPshᴰNatTrans : Presheafᴰ P Cᴰ ℓQᴰ
  reindPshᴰNatTrans = reindPsh (Idᴰ /Fⱽ α) Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHom P Q)(β : PshHom Q R) (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ) where
  private
    module Rᴰ = PresheafᴰNotation Cᴰ R Rᴰ
  reindPshᴰNatTrans-seq : PshIso (reindPshᴰNatTrans (α ⋆PshHom β) Rᴰ) (reindPshᴰNatTrans α $ reindPshᴰNatTrans β Rᴰ)
  reindPshᴰNatTrans-seq = Isos→PshIso (λ _ → idIso) λ _ _ →
    λ _ _ → Rᴰ.rectify $ Rᴰ.≡out $ Rᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Rᴰ.⋆ᴰ-reind _ _ _)

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (α : PshHom P P) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
  reindPshᴰNatTrans-id : PshIso (reindPshᴰNatTrans idPshHom Pᴰ) Pᴰ
  reindPshᴰNatTrans-id = Isos→PshIso (λ _ → idIso) λ _ _ _ _ → Pᴰ.rectify $ Pᴰ.≡out $
    Pᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Pᴰ.⋆ᴰ-reind _ _ _)

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} (α β : PshHom P Q) (α≡β : α ≡ β) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  private
    module Q = PresheafNotation Q
    module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ
  reindPshᴰNatTrans-Path : PshIso (reindPshᴰNatTrans α Qᴰ) (reindPshᴰNatTrans β Qᴰ)
  reindPshᴰNatTrans-Path = reindNatIsoPsh (pathToNatIso (cong₂ _/Fⱽ_ refl α≡β)) Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf D ℓP}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ)
  where
  reindPshᴰFunctor : Presheafᴰ (reindPsh F P) Cᴰ ℓPᴰ
  reindPshᴰFunctor = reindPsh (Fᴰ /Fᴰ idPshHom) Pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHom P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  -- Constructing a fibration from its fibers and restrictions
  PshHomᴰ : Type _
  PshHomᴰ = PshHomⱽ Pᴰ (reindPshᴰNatTrans α Qᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  isPshIsoⱽ : PshHomⱽ Pᴰ Qᴰ → Type _
  isPshIsoⱽ = isPshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
  idPshIsoⱽ : PshIsoⱽ Pᴰ Pᴰ
  idPshIsoⱽ = idPshIso

  idPshHomⱽ : PshHomⱽ Pᴰ Pᴰ
  idPshHomⱽ = idPshHom

  idPshHomᴰ : PshHomᴰ idPshHom Pᴰ Pᴰ
  idPshHomᴰ = invPshIso (reindPshᴰNatTrans-id idPshHom Pᴰ) .trans
  -- idPshHomᴰ .N-ob = λ c z → z
  -- idPshHomᴰ .N-hom c c' f p =
  --   Pᴰ.rectify $ Pᴰ.≡out $
  --     Pᴰ.⋆ᴰ-reind _ _ _
  --     ∙ (sym $ Pᴰ.⋆ᴰ-reind _ _ _)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
  where
  invPshIsoⱽ : PshIsoⱽ Pᴰ Qᴰ → PshIsoⱽ Qᴰ Pᴰ
  invPshIsoⱽ = invPshIso

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
  where
  _⋆PshHomⱽ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomⱽ Pᴰ Rᴰ
  _⋆PshHomⱽ_ = _⋆PshHom_

  _⋆PshIsoⱽ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoⱽ Pᴰ Rᴰ
  _⋆PshIsoⱽ_ = _⋆PshIso_

  infixr 9 _⋆PshHomⱽ_
  infixr 9 _⋆PshIsoⱽ_

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
    module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ
    module Rᴰ = PresheafᴰNotation Cᴰ R Rᴰ

  _⋆PshHomᴰ_ :
    {α : PshHom P Q}
    {β : PshHom Q R} →
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
    (βᴰ : PshHomᴰ β Qᴰ Rᴰ) →
    PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
  -- (αᴰ ⋆PshHomᴰ βᴰ) .N-ob c x =
  --   βᴰ .N-ob _ (αᴰ .N-ob c x)
  -- (αᴰ ⋆PshHomᴰ βᴰ) .N-hom c c' f p =
  --   Rᴰ.rectify $ Rᴰ.≡out $
  --     (Rᴰ.≡in $ cong (βᴰ .N-ob _) (αᴰ .N-hom c c' f p))
  --     ∙ (Rᴰ.≡in $ βᴰ .N-hom _ _ _ (αᴰ .N-ob _ p))
  --     ∙ Rᴰ.⋆ᴰ-reind _ _ _
  --     ∙ (sym $ Rᴰ.⋆ᴰ-reind _ _ _)
  (αᴰ ⋆PshHomᴰ βᴰ) =
    αᴰ
    ⋆PshHomⱽ reindPshHom (Idᴰ /Fⱽ _) βᴰ
    ⋆PshHomⱽ invPshIso (reindPshᴰNatTrans-seq _ _ Rᴰ) .trans

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P

  module _
    {α β : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
    (βᴰ : PshHomᴰ β Pᴰ Qᴰ)
    where
    private
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
      module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ

    PshHomᴰPathP : α ≡ β → Type _
    PshHomᴰPathP α≡β = PathP (λ i → PshHomᴰ (α≡β i) Pᴰ Qᴰ) αᴰ βᴰ

    makePshHomᴰPathP :
      (α≡β : α ≡ β) →
      (PathP (λ i → ((x , xᴰ , p) : ob (Cᴰ / P)) → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α≡β i .N-ob x p ][ xᴰ ])
          (αᴰ .N-ob) (βᴰ .N-ob)) →
      PshHomᴰPathP α≡β
    makePshHomᴰPathP α≡β αᴰ≡βᴰ i .N-ob = αᴰ≡βᴰ i
    makePshHomᴰPathP α≡β αᴰ≡βᴰ i .N-hom c c' f p =
      isSet→SquareP (λ j k → Qᴰ.isSetPshᴰ)
        (αᴰ .N-hom c c' f p)
        (βᴰ .N-hom c c' f p)
        (λ j → αᴰ≡βᴰ j _ (Pᴰ .F-hom f p))
        (λ j → Qᴰ .F-hom ((Idᴰ /Fⱽ α≡β j) .F-hom f) (αᴰ≡βᴰ j c' p))
        i

  module _
    {α : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {αᴰ βᴰ : PshHomᴰ α Pᴰ Qᴰ}
    where
    private
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
      module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ

    makePshHomᴰPath : (αᴰ .N-ob ≡ βᴰ .N-ob) → αᴰ ≡ βᴰ
    makePshHomᴰPath = makePshHomᴰPathP αᴰ βᴰ (λ i → α)
