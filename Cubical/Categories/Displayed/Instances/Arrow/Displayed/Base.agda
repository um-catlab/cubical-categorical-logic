{-
  Displayed Arrow and Iso categories displayed over ordinary Arrow and Iso categories.

  Universal property: a section of the Arrowᴰ bundle is a displayed natural
  transformation between functors, section of the Isoᴰ bundle is a
  displayed natural isomorphism

-}
module Cubical.Categories.Displayed.Instances.Arrow.Displayed.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Morphism

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More as BPᴰ
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Section.More
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Instances.Graph
open import Cubical.Categories.Displayed.Instances.PropertyOver
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
open import Cubical.Categories.Instances.TotalCategory as ∫C
open import Cubical.Categories.Bifunctor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor
open Categoryᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  open StructureOver
  ArrowᴰBase : Category (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ArrowᴰBase = ∫C {C = C ×C C} (Arrow C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))

  -- Manual definition for the time being rather than some kind of Graphᴰ
  ArrowᴰStr : StructureOver (∫C {C = C ×C C} (Arrow C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))) ℓCᴰ' ℓCᴰ'
  ArrowᴰStr .ob[_] ((x , y) , f , xᴰ , yᴰ) = Cᴰ [ f ][ xᴰ , yᴰ ]
  ArrowᴰStr .Hom[_][_,_] {x = ((x , y) , f , xᴰ , yᴰ)} {y = ((x' , y') , f' , xᴰ' , yᴰ')}
    ((g , h) , sq , gᴰ , hᴰ)
    fᴰ fᴰ'
    = (gᴰ Cᴰ.⋆ᴰ fᴰ') Cᴰ.≡[ sq ] (fᴰ Cᴰ.⋆ᴰ hᴰ)
  ArrowᴰStr .idᴰ = Cᴰ.rectifyOut (Cᴰ.⋆IdL _ ∙ sym (Cᴰ.⋆IdR _))
  ArrowᴰStr ._⋆ᴰ_ sq sq' = Cᴰ.rectifyOut
    (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.≡in sq' ⟩
    ∙ sym (Cᴰ.⋆Assoc _ _ _)
    ∙ Cᴰ.⟨ Cᴰ.≡in sq ⟩⋆⟨⟩
    ∙ Cᴰ.⋆Assoc _ _ _)
  ArrowᴰStr .isPropHomᴰ = λ pf1 pf2 →
    isOfHLevel→isOfHLevelDep 2 {B = Cᴰ.Hom[_][ _ , _ ]}(λ f → Cᴰ.isSetHomᴰ) _ _ pf1 pf2 _

  Arrowᴰ : Categoryᴰ (∫C {C = C ×C C} (Arrow C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))) ℓCᴰ' ℓCᴰ'
  Arrowᴰ = StructureOver→Catᴰ ArrowᴰStr

  IsoᴰBase : Category _ _
  IsoᴰBase = ∫C {C = C ×C C} (Iso C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))

  -- TODO: fix type signature
  IsoᴰBaseHom≡ : ∀ {x y} → {f g : IsoᴰBase [ x , y ]}
    → (Σ[ v ∈ fst f ≡ fst g ] PathP (λ i → (Cᴰ ×Cᴰ Cᴰ) [ v i ][ x .snd .snd , y .snd .snd ]) (snd (snd f)) (snd (snd g)))
    → f ≡ g
  IsoᴰBaseHom≡ {f = f} pf = ΣPathP (pf .fst , ΣPathP ((isProp→PathP (λ _ → isProp× (C.isSetHom _ _) isPropUnit) _ _) , pf .snd))

  IsoᴰStr : StructureOver (∫C {C = C ×C C} (Iso C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))) ℓCᴰ' ℓCᴰ'
  IsoᴰStr .ob[_] ((x , y) , f , xᴰ , yᴰ) = CatIsoᴰ Cᴰ f xᴰ yᴰ
  IsoᴰStr .Hom[_][_,_] {x = ((x , y) , f , xᴰ , yᴰ)} {y = ((x' , y') , f' , xᴰ' , yᴰ')}
    ((g , h) , sq , gᴰ , hᴰ)
    fᴰ fᴰ'
    = (gᴰ Cᴰ.⋆ᴰ fᴰ' .fst) Cᴰ.≡[ sq .fst ] fᴰ .fst Cᴰ.⋆ᴰ hᴰ
  IsoᴰStr .idᴰ = Cᴰ.rectifyOut (Cᴰ.⋆IdL _ ∙ sym (Cᴰ.⋆IdR _))
  IsoᴰStr ._⋆ᴰ_ sq sq' = Cᴰ.rectifyOut
    (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.≡in sq' ⟩
    ∙ sym (Cᴰ.⋆Assoc _ _ _)
    ∙ Cᴰ.⟨ Cᴰ.≡in sq ⟩⋆⟨⟩
    ∙ Cᴰ.⋆Assoc _ _ _)
  IsoᴰStr .isPropHomᴰ = λ pf1 pf2 →
    isOfHLevel→isOfHLevelDep 2 {B = Cᴰ.Hom[_][ _ , _ ]}(λ f → Cᴰ.isSetHomᴰ) _ _ pf1 pf2 _

  Isoᴰ : Categoryᴰ (∫C {C = C ×C C} (Iso C ×ᴰ (Cᴰ ×Cᴰ Cᴰ))) ℓCᴰ' ℓCᴰ'
  Isoᴰ = StructureOver→Catᴰ IsoᴰStr

  hasPropHomsIsoᴰ : hasPropHoms Isoᴰ
  hasPropHomsIsoᴰ = hasPropHomsStructureOver IsoᴰStr

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F G : Functor C D}{α : F ⇒ G}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  where
  ArrowᴰReflection :
    Section {D = ∫C Cᴰ} (∫F (BPᴰ.introF (F ,F G) (wkSection Cᴰ (arrIntroS α)) (Fᴰ ,Fᴰ Gᴰ))) (Arrowᴰ Dᴰ) → NatTransᴰ α Fᴰ Gᴰ
  ArrowᴰReflection Fᴰ .NatTransᴰ.N-obᴰ xᴰ = Fᴰ .F-obᴰ _
  ArrowᴰReflection Fᴰ .NatTransᴰ.N-homᴰ fᴰ = Fᴰ .F-homᴰ _

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F G : Functor C D}{α : F ≅ᶜ G}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  where
  IsoᴰReflection :
    Section {D = ∫C Cᴰ} (∫F (BPᴰ.introF (F ,F G) (wkSection Cᴰ (isoIntroS α)) (Fᴰ ,Fᴰ Gᴰ))) (Isoᴰ Dᴰ)
    → NatIsoᴰ α Fᴰ Gᴰ
  IsoᴰReflection Fᴰ .NatIsoᴰ.transᴰ .NatTransᴰ.N-obᴰ _ = Fᴰ .F-obᴰ _ .fst
  IsoᴰReflection Fᴰ .NatIsoᴰ.transᴰ .NatTransᴰ.N-homᴰ _ = Fᴰ .F-homᴰ _
  IsoᴰReflection Fᴰ .NatIsoᴰ.nIsoᴰ _ = Fᴰ .F-obᴰ _ .snd
