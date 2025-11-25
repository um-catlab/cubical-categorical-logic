{-
   Local and Global Sections of a displayed category.

   A local section of a displayed category Cᴰ over a functor F : D → C
   is visualized as follows:

          Cᴰ
        ↗ |
       /  |
    s /   |
     /    |
    /     ↓
   D ---→ C
       F

   We call this a *global* section if F is the identity functor.

   Every Section can be implemented as a Functorᴰ out of Unitᴰ (see
   Displayed.Instances.Terminal):

       Fᴰ
   D ----→ Cᴰ
   ∥       |
   ∥       |
   ∥       |
   ∥       |
   ∥       ↓
   D ----→ C
       F

   And vice-versa any Functorᴰ

       Fᴰ
   Dᴰ ----→ Cᴰ
   |        |
   |        |
   |        |
   |        |
   ↓        ↓
   D -----→ C
       F

   Can be implemented as a Section (see
   Displayed.Constructions.TotalCategory)

            Cᴰ
          ↗ |
         /  |
      s /   |
       /    |
      /     ↓
   ∫Dᴰ ---→ C
        F

   Both options are sometimes more ergonomic. One of the main
   cosmetic differences is

   1. When defining a Functorᴰ, the object of the base category is
      implicit
   2. When defining a Section, the object of the base category is
      explicit

   Definitionally, there is basically no difference as these are
   definitional isomorphisms.

   Elimination rules are naturally stated in terms of local sections
   (and often global sections, see below). Intro rules can be
   formulated as either constructing a Section or a Functorᴰ. Good
   style is to offer both introS for Section and introF for Functorᴰ.

-}
module Cubical.Categories.LocallySmall.Displayed.Section.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ
open Functor

module _ {C : Category Cob CHom-ℓ}
         {D : Category Dob DHom-ℓ}
         (F : Functor D C)
         (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
         where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module Cᴰ = Categoryᴰ Cᴰ
    module F = FunctorNotation F

  -- Section without a qualifier means *local* section.
  record Section : Typeω
    where
    field
      F-obᴰ  : ∀ d → Cobᴰ (F.F-ob d)
      F-homᴰ : ∀ {d d'} (f : D.Hom[ d , d' ])
        → Cᴰ.Hom[ F.F-hom f ][ F-obᴰ d , F-obᴰ d' ]
      F-idᴰ : ∀ {d} → F-homᴰ (D.id {d}) Cᴰ.∫≡ Cᴰ.idᴰ
      F-seqᴰ : ∀ {d d' d''}
            → (f : D.Hom[ d , d' ])(g : D.Hom[ d' , d'' ])
            → F-homᴰ (f D.⋆ g) Cᴰ.∫≡ F-homᴰ f Cᴰ.⋆ᴰ F-homᴰ g
    F-homᴰ⟨_⟩ : ∀ {x y}{f g : D.Hom[ x , y ]}
        (f≡g : f ≡ g) →
        F-homᴰ f Cᴰ.∫≡ F-homᴰ g
    F-homᴰ⟨ f≡g ⟩ i = (F.F-hom (f≡g i)) , (F-homᴰ (f≡g i))

    intro : Functor D Cᴰ.∫C
    intro .F-ob d = F.F-ob d , F-obᴰ d
    intro .F-hom f = F.F-hom f , F-homᴰ f
    intro .F-id = F-idᴰ
    intro .F-seq f g = F-seqᴰ f g

{-
   A Global Section is a local section over the identity functor.

          Cᴰ
        ↗ |
       /  |
    s /   |
     /    |
    /     ↓
   C ==== C


   So global sections are by definition local sections

   All local sections can be implemented as global sections into the
   reindexed displayed category. See Reindex.agda for details.

   But this isomorphism is not definitional (i.e. the equations are
   not provable by refl). Constructing a local section is preferable
   as they are more flexible, but often elimination principles are
   naturally proven first about global sections and then generalized
   to local sections using reindexing.

   It is good style is to offer both: elimLocal to construct a local
   section and elimGlobal to construct a global section.
-}


module _ {C : Category Cob CHom-ℓ}
         (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
         where
  GlobalSection : Typeω
  GlobalSection = Section idF Cᴰ

{-

   Composition of a Section and a Functor

                 Cᴰ
               ↗ |
              /  |
           s /   |
            /    |
           /     ↓
   E ---→ D ---→ C
              F

-}

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  {F : Functor D E}
  {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  (Fᴰ : Section F Eᴰ)
  (G : Functor C D)
  where
  open Section
  private
    module Eᴰ = Categoryᴰ Eᴰ
    module Fᴰ = Section Fᴰ
    module G = FunctorNotation G

  compSectionFunctor : Section (F ∘F G) Eᴰ
  compSectionFunctor .F-obᴰ d = Fᴰ.F-obᴰ (G.F-ob d)
  compSectionFunctor .F-homᴰ f = Fᴰ.F-homᴰ (G.F-hom f)
  compSectionFunctor .F-idᴰ = Fᴰ.F-homᴰ⟨ G.F-id ⟩ ∙ Fᴰ.F-idᴰ
  compSectionFunctor .F-seqᴰ f g =
    Fᴰ.F-homᴰ⟨ G.F-seq f g ⟩ ∙ Fᴰ.F-seqᴰ (G.F-hom f) (G.F-hom g)

{-

  Composition of a Section and a Functorᴰ

              Fᴰ'
          Cᴰ ---→ Cᴰ'
        ↗ |       |
       /  |       |
    s /   |       |
     /    |       |
    /     ↓       ↓
   D ---→ C ----→ C'
       F     F'

-}
module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  {F : Functor D E}
  {G : Functor C D}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  (Fᴰ : Functorᴰ F Dᴰ Eᴰ)
  (Gᴰ : Section G Dᴰ)
  where
  open Section
  private
    module Eᴰ = Categoryᴰ Eᴰ
    module Fᴰ = Functorᴰ Fᴰ
    module Gᴰ = Section Gᴰ

  compFunctorᴰSection : Section (F ∘F G) Eᴰ
  compFunctorᴰSection .F-obᴰ = λ d → Fᴰ.F-obᴰ (Gᴰ.F-obᴰ d)
  compFunctorᴰSection .F-homᴰ = λ f → Fᴰ.F-homᴰ (Gᴰ.F-homᴰ f)
  compFunctorᴰSection .F-idᴰ =
    Fᴰ.F-homᴰ⟨ Gᴰ.F-idᴰ ⟩ ∙ Fᴰ.F-idᴰ
  compFunctorᴰSection .F-seqᴰ f g =
    Fᴰ.F-homᴰ⟨ Gᴰ.F-seqᴰ f g ⟩ ∙ Fᴰ.F-seqᴰ (Gᴰ.F-homᴰ f) (Gᴰ.F-homᴰ g)
