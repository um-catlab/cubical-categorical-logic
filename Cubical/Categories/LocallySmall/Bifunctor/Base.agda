module Cubical.Categories.LocallySmall.Bifunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Functor.Base


open CatIso

record Bifunctor (C : Category Cob CHom-ℓ)
                 (D : Category Dob DHom-ℓ)
                 (E : Category Eob EHom-ℓ)
       : Typeω where
  no-eta-equality
  constructor bifunctor
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module E = CategoryNotation E

  field
    Bif-ob : Cob → Dob → Eob
    Bif-hom× : ∀ {c c' d d'} (f : C.Hom[ c , c' ])(g : D.Hom[ d , d' ])
      → E.Hom[ Bif-ob c d , Bif-ob c' d' ]
    Bif-homL : ∀ {c c'} (f : C.Hom[ c , c' ]) d
      → E.Hom[ Bif-ob c d , Bif-ob c' d ]
    Bif-homR : ∀ {d d'} c (g : D.Hom[ d , d' ])
      → E.Hom[ Bif-ob c d , Bif-ob c d' ]
    Bif-×-id : ∀ {c d} → Bif-hom× (C.id {c}) (D.id {d}) ≡ E.id
    Bif-×-seq : ∀ {c c' c'' d d' d''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
      → Bif-hom× (f C.⋆ f') (g D.⋆ g')
        ≡ Bif-hom× f g E.⋆ Bif-hom× f' g'
    Bif-L×-agree : ∀ {c c'} (f : C.Hom[ c , c' ]) d
      → Bif-homL f d ≡ Bif-hom× f D.id
    Bif-R×-agree : ∀ {d d'} c (g : D.Hom[ d , d' ])
      → Bif-homR c g ≡ Bif-hom× C.id g
  Bif-hom×⟨_⟩⟨_⟩ : ∀ {c c' d d'}{f f' g g'}
    (f≡f' : Path C.Hom[ c , c' ] f f')
    (g≡g' : Path D.Hom[ d , d' ] g g')
    → Path E.Hom[ Bif-ob c d , Bif-ob c' d' ] (Bif-hom× f g) (Bif-hom× f' g')
  Bif-hom×⟨ f≡f' ⟩⟨ g≡g' ⟩ = cong₂ Bif-hom× f≡f' g≡g'

  Bif-iso× : ∀ {c c' d d'} (f : C.ISOC.Hom[ c , c' ])(g : D.ISOC.Hom[ d , d' ])
      → E.ISOC.Hom[ Bif-ob c d , Bif-ob c' d' ]
  Bif-iso× f g .fun = Bif-hom× (f .fun) (g .fun)
  Bif-iso× f g .inv = Bif-hom× (f .inv) (g .inv)
  Bif-iso× f g .sec = sym Bif-×-seq ∙ Bif-hom×⟨ f .sec ⟩⟨ g .sec ⟩ ∙ Bif-×-id
  Bif-iso× f g .ret = sym Bif-×-seq ∙ Bif-hom×⟨ f .ret ⟩⟨ g .ret ⟩ ∙ Bif-×-id

open Bifunctor
open Functor

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  where
  BifunctorToParFunctor : Bifunctor C D E → Functor (C ×C D) E
  BifunctorToParFunctor F .F-ob = λ z → F .Bif-ob (z .Σω.fst) (z .Σω.snd)
  BifunctorToParFunctor F .F-hom = λ z → F .Bif-hom× (z .fst) (z .snd)
  BifunctorToParFunctor F .F-id = F .Bif-×-id
  BifunctorToParFunctor F .F-seq = λ f g → F .Bif-×-seq

  ParFunctorToBifunctor : Functor (C ×C D) E → Bifunctor C D E
  ParFunctorToBifunctor F .Bif-ob = λ z z₁ → F-ob F (z , z₁)
  ParFunctorToBifunctor F .Bif-hom× = λ f g → F-hom F (f , g)
  ParFunctorToBifunctor F .Bif-homL = λ f d → F-hom F (f , Category.id D)
  ParFunctorToBifunctor F .Bif-homR = λ c g → F-hom F (Category.id C , g)
  ParFunctorToBifunctor F .Bif-×-id = F-id F
  ParFunctorToBifunctor F .Bif-×-seq = F-seq F (_ , _) (_ , _)
  ParFunctorToBifunctor F .Bif-L×-agree f d = refl
  ParFunctorToBifunctor F .Bif-R×-agree g c = refl

  module _ {Cob' CHom-ℓ'}
    {C' : Category Cob' CHom-ℓ'}
    (F : Bifunctor C' D E)
    (G : Functor C C')
    where
    compL : Bifunctor C D E
    compL .Bif-ob = λ z → F .Bif-ob (F-ob G z)
    compL .Bif-hom× = λ f → F .Bif-hom× (F-hom G f)
    compL .Bif-homL = λ f → F .Bif-homL (F-hom G f)
    compL .Bif-homR = λ c → F .Bif-homR (F-ob G c)
    compL .Bif-×-id = cong₂ (F .Bif-hom×) (F-id G) refl ∙ F .Bif-×-id
    compL .Bif-×-seq =
      cong₂ (F .Bif-hom×) (F-seq G _ _) refl
      ∙ F .Bif-×-seq
    compL .Bif-L×-agree = λ f → F .Bif-L×-agree (F-hom G f)
    compL .Bif-R×-agree c g =
      F .Bif-R×-agree (F-ob G c) g
      ∙ cong₂ (F .Bif-hom×) (sym $ F-id G) refl
    infixl 30 compL
    syntax compL F G = F ∘Fl G

  module _ {Dob' DHom-ℓ'}
    {D' : Category Dob' DHom-ℓ'}
    (F : Bifunctor C D' E)
    (G : Functor D D')
    where
    compR : Bifunctor C D E
    compR .Bif-ob = λ z z₁ → F .Bif-ob z (F-ob G z₁)
    compR .Bif-hom× = λ f g → F .Bif-hom× f (F-hom G g)
    compR .Bif-homL = λ f d → F .Bif-homL f (F-ob G d)
    compR .Bif-homR = λ c g → F .Bif-homR c (F-hom G g)
    compR .Bif-×-id = cong₂ (F .Bif-hom×) refl (G .F-id) ∙ F .Bif-×-id
    compR .Bif-×-seq =
      cong₂ (F .Bif-hom×) refl (F-seq G _ _)
      ∙ F .Bif-×-seq
    compR .Bif-L×-agree f d =
      F .Bif-L×-agree f (F-ob G d)
      ∙ cong₂ (F .Bif-hom×) refl (sym $ F-id G)
    compR .Bif-R×-agree = λ c g → F .Bif-R×-agree c (F-hom G g)

    infixl 30 compR
    syntax compR F G = F ∘Fr G

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  {Cob' CHom-ℓ'}
  {Dob' DHom-ℓ'}
  {C' : Category Cob' CHom-ℓ'}
  {D' : Category Dob' DHom-ℓ'}
  (F : Bifunctor C' D' E)
  where
  module _ (G : Functor C C') (H : Functor D D') where
    compLR : Bifunctor C D E
    compLR = F ∘Fl G ∘Fr H

  module _ (GH : Σω (Functor C C') λ _ → Functor D D') where
    compLR' : Bifunctor C D E
    compLR' = compLR (GH .Σω.fst) (GH .Σω.snd)

    infixl 30 compLR'
    syntax compLR' F GH = F ∘Flr GH
