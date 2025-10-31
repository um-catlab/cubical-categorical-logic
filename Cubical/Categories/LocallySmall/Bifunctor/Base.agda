module Cubical.Categories.LocallySmall.Bifunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Functor.Base as LocallySmall

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open CatIso
open CatIsoᴰ

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

record Bifunctorᴰ
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  (F : Bifunctor C D E)
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ)
  : Typeω where
  no-eta-equality
  constructor bifunctorᴰ
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module E = CategoryNotation E
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module F = Bifunctor F

  field
    Bif-obᴰ : ∀ {c d} → (cᴰ : Cobᴰ c) (dᴰ : Dobᴰ d) → Eobᴰ (F.Bif-ob c d)
    Bif-hom×ᴰ : ∀ {c c' d d'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.Hom[ c , c' ]}{g : D.Hom[ d , d' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.Bif-hom× f g ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
    Bif-homLᴰ : ∀ {c c' d}{cᴰ cᴰ' }
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      dᴰ
      → Eᴰ.Hom[ F.Bif-homL f d ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ ]
    Bif-homRᴰ : ∀ {c d d'}{dᴰ dᴰ'}
      {g : D.Hom[ d , d' ]}
      cᴰ
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.Bif-homR c g ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ dᴰ' ]
    Bif-×-idᴰ : ∀ {c d}{cᴰ : Cobᴰ c}{dᴰ : Dobᴰ d}
      → Bif-hom×ᴰ (Cᴰ.idᴰ {xᴰ = cᴰ}) (Dᴰ.idᴰ {xᴰ = dᴰ}) Eᴰ.∫≡ Eᴰ.idᴰ
    Bif-×-seqᴰ : ∀ {c c' c'' d d' d''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
      {fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]}
      {fᴰ' : Cᴰ.Hom[ f' ][ cᴰ' , cᴰ'' ]}
      {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]}
      {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ' , dᴰ'' ]}
      → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
        Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
    Bif-L×-agreeᴰ : ∀ {c c' d}{cᴰ cᴰ' }
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (dᴰ : Dobᴰ d)
      → Bif-homLᴰ fᴰ dᴰ Eᴰ.∫≡ Bif-hom×ᴰ fᴰ Dᴰ.idᴰ
    Bif-R×-agreeᴰ : ∀ {c d d'}{dᴰ dᴰ'}
      {g : D.Hom[ d , d' ]}
      (cᴰ : Cobᴰ c)
      (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
      → Bif-homRᴰ cᴰ gᴰ Eᴰ.∫≡ Bif-hom×ᴰ Cᴰ.idᴰ gᴰ

  Bif-hom×ᴰ⟨_⟩⟨_⟩ : ∀ {c c' d d'}{f f' g g'}{cᴰ cᴰ' dᴰ dᴰ'}{fᴰ fᴰ' gᴰ gᴰ'}
    (fᴰ≡fᴰ' : Path Cᴰ.Hom[ (c , cᴰ) , (c' , cᴰ') ] (f , fᴰ) (f' , fᴰ'))
    (gᴰ≡gᴰ' : Path Dᴰ.Hom[ (d , dᴰ) , (d' , dᴰ') ] (g , gᴰ) (g' , gᴰ'))
    → (Bif-hom×ᴰ fᴰ gᴰ) Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ' gᴰ')
  Bif-hom×ᴰ⟨ fᴰ≡fᴰ' ⟩⟨ gᴰ≡gᴰ' ⟩ i =
    (F.Bif-hom× (fᴰ≡fᴰ' i .fst) (gᴰ≡gᴰ' i .fst))
    , (Bif-hom×ᴰ (fᴰ≡fᴰ' i .snd) (gᴰ≡gᴰ' i .snd))

  ∫F : Bifunctor Cᴰ.∫C Dᴰ.∫C Eᴰ.∫C
  ∫F .Bif-ob (c , cᴰ) (d , dᴰ) = _ , Bif-obᴰ cᴰ dᴰ
  ∫F .Bif-hom× (f , fᴰ) (g , gᴰ) = _ , Bif-hom×ᴰ fᴰ gᴰ
  ∫F .Bif-homL (f , fᴰ) (d , dᴰ) = _ , Bif-homLᴰ fᴰ dᴰ
  ∫F .Bif-homR (c , cᴰ) (g , gᴰ) = _ , Bif-homRᴰ cᴰ gᴰ
  ∫F .Bif-×-id = Bif-×-idᴰ
  ∫F .Bif-×-seq = Bif-×-seqᴰ
  ∫F .Bif-L×-agree (_ , fᴰ) (_ , dᴰ) = Bif-L×-agreeᴰ fᴰ dᴰ
  ∫F .Bif-R×-agree (_ , cᴰ) (_ , gᴰ) = Bif-R×-agreeᴰ cᴰ gᴰ

module _
  {C : Category Cob CHom-ℓ} {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ} {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ} {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  where

  open Bifunctorᴰ
  open Functorᴰ

  BifunctorᴰToParFunctorᴰ :
    {F : Bifunctor C D E} → Bifunctorᴰ F Cᴰ Dᴰ Eᴰ →
    Functorᴰ (BifunctorToParFunctor F) (Cᴰ ×Cᴰ Dᴰ) Eᴰ
  BifunctorᴰToParFunctorᴰ Fᴰ .F-obᴰ = λ z → Fᴰ .Bif-obᴰ (z .Σω.fst) (z .Σω.snd)
  BifunctorᴰToParFunctorᴰ Fᴰ .F-homᴰ = λ fᴰ → Fᴰ .Bif-hom×ᴰ (fᴰ .fst) (fᴰ .snd)
  BifunctorᴰToParFunctorᴰ Fᴰ .F-idᴰ = Fᴰ .Bif-×-idᴰ
  BifunctorᴰToParFunctorᴰ Fᴰ .F-seqᴰ = λ fᴰ gᴰ → Fᴰ .Bif-×-seqᴰ

  ParFunctorᴰToBifunctorᴰ :
    {F : Functor (C ×C D) E} →
    Functorᴰ F (Cᴰ ×Cᴰ Dᴰ) Eᴰ →
    Bifunctorᴰ (ParFunctorToBifunctor F) Cᴰ Dᴰ Eᴰ
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-obᴰ = λ cᴰ dᴰ → F-obᴰ Fᴰ (cᴰ , dᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-hom×ᴰ = λ fᴰ gᴰ → F-homᴰ Fᴰ (fᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-homLᴰ = λ fᴰ dᴰ → F-homᴰ Fᴰ (fᴰ , Categoryᴰ.idᴰ Dᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-homRᴰ = λ cᴰ gᴰ → F-homᴰ Fᴰ (Categoryᴰ.idᴰ Cᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-×-idᴰ = F-idᴰ Fᴰ
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-×-seqᴰ = F-seqᴰ Fᴰ (_ , _) (_ , _)
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-L×-agreeᴰ _ _ = refl
  ParFunctorᴰToBifunctorᴰ Fᴰ .Bif-R×-agreeᴰ _ _ = refl

module _
  {C : Category Cob CHom-ℓ}
  {Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  {Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ} {Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  where

  open Bifunctorᴰ
  open Functorᴰ

  BifunctorᴰToParFunctorᴰSF :
    {F : Bifunctor C D E} → Bifunctorᴰ F Cᴰ Dᴰ Eᴰ →
    Functorᴰ (BifunctorToParFunctor F) (Cᴰ ×CᴰSF Dᴰ) Eᴰ
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-obᴰ =
    λ z → Fᴰ .Bif-obᴰ (liftω (z .Liftω.lowerω .fst))
                      (liftω (z .Liftω.lowerω .snd))
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-homᴰ =
    λ fᴰ → Fᴰ .Bif-hom×ᴰ (fᴰ .fst) (fᴰ .snd)
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-idᴰ = Fᴰ .Bif-×-idᴰ
  BifunctorᴰToParFunctorᴰSF Fᴰ .F-seqᴰ = λ fᴰ gᴰ → Fᴰ .Bif-×-seqᴰ

  ParFunctorᴰToBifunctorᴰSF :
    {F : Functor (C ×C D) E} →
    Functorᴰ F (Cᴰ ×CᴰSF Dᴰ) Eᴰ →
    Bifunctorᴰ (ParFunctorToBifunctor F) Cᴰ Dᴰ Eᴰ
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-obᴰ =
    λ cᴰ dᴰ → F-obᴰ Fᴰ (liftω (cᴰ .Liftω.lowerω , dᴰ .Liftω.lowerω))
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-hom×ᴰ = λ fᴰ gᴰ → F-homᴰ Fᴰ (fᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-homLᴰ = λ fᴰ dᴰ → F-homᴰ Fᴰ (fᴰ , Categoryᴰ.idᴰ Dᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-homRᴰ = λ cᴰ gᴰ → F-homᴰ Fᴰ (Categoryᴰ.idᴰ Cᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-×-idᴰ = F-idᴰ Fᴰ
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-×-seqᴰ = F-seqᴰ Fᴰ (_ , _) (_ , _)
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-L×-agreeᴰ _ _ = refl
  ParFunctorᴰToBifunctorᴰSF Fᴰ .Bif-R×-agreeᴰ _ _ = refl

-- Cᴰ ⇒ⱽ Dᴰ
-- an object over x is a functor F : Cᴰ.v[ x ] → Dᴰ.v[ x ]
-- a morphism from F_x : Cᴰ⇒Dᴰ[ x ] to G_y : Cᴰ⇒Dᴰ[ y ]
--
-- over f : C [ x , y ] is?
-- well it could be a profunctor homomorphism Cᴰ[ f ][ xᴰ , yᴰ ] → Cᴰ [ f ][ F xᴰ , G yᴰ ]
-- if Cᴰ, Dᴰ are fibrations this could be a nat trans F ∘ f* ⇒ f* ∘ G : Cᴰ.v[ y ] → Dᴰ.v[ x ]
--   i.e., for every yᴰ a morphism Dᴰ.v[ x ][ F (f* yᴰ) , f* (G yᴰ) ],
--   i.e., Dᴰ [ f ][ F (f* yᴰ) , yᴰ ]
record Bifunctorⱽ {C : Category Cob CHom-ℓ}{E : Category Eob EHom-ℓ}
  (F : Functor C E)
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ)
  (Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ)
  : Typeω where
  no-eta-equality
  constructor bifunctorⱽ
  private
    module C = CategoryNotation C
    module E = CategoryNotation E
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module F = FunctorNotation F

  field
    Bif-obᴰ : ∀ {c} → (cᴰ : Cobᴰ c) (dᴰ : Dobᴰ c) → Eobᴰ (F.F-ob c)
    Bif-hom×ᴰ : ∀ {c c'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.Hom[ c , c' ]}
      (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.Hom[ f ][ dᴰ , dᴰ' ])
      → Eᴰ.Hom[ F.F-hom f ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
    -- -- homL doesn't make sense unless Dᴰ is an (op)fibration
    -- -- does it make sense if Dᴰ is Conduché?
    -- Bif-homLᴰ : ∀ {c c'}{cᴰ cᴰ' }
    --   {f : C.Hom[ c , c' ]}
    --   (fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ])
    --   (dᴰ : Dobᴰ c')
    --   → Eᴰ.Hom[ f ][ Bif-obᴰ cᴰ (f Dᴰ.^* dᴰ) , Bif-obᴰ cᴰ' dᴰ ]
    -- -- vice-versa homR makes sense only if Cᴰ is an (op)fibration

    -- Hm...
    Bif-×-idᴰ : ∀ {c}{cᴰ : Cobᴰ c}{dᴰ : Dobᴰ c}
      → Bif-hom×ᴰ (Cᴰ.idᴰ {xᴰ = cᴰ}) (Dᴰ.idᴰ {xᴰ = dᴰ}) Eᴰ.∫≡ Eᴰ.idᴰ
    Bif-×-seqᴰ : ∀ {c c' c''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
      {f : C.Hom[ c , c' ]}{f' : C.Hom[ c' , c'' ]}
      {fᴰ : Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]}
      {fᴰ' : Cᴰ.Hom[ f' ][ cᴰ' , cᴰ'' ]}
      {gᴰ : Dᴰ.Hom[ f ][ dᴰ , dᴰ' ]}
      {gᴰ' : Dᴰ.Hom[ f' ][ dᴰ' , dᴰ'' ]}
      → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
        Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
  opaque
    Bif-hom×ᴰ⟨_⟩⟨_⟩ : ∀ {c c'}{f f'}{cᴰ cᴰ' dᴰ dᴰ'}{fᴰ fᴰ' gᴰ gᴰ'}
      (fᴰ≡fᴰ' : Path Cᴰ.Hom[ (c , cᴰ) , (c' , cᴰ') ] (f , fᴰ) (f' , fᴰ'))
      (gᴰ≡gᴰ' : Path Dᴰ.Hom[ (c , dᴰ) , (c' , dᴰ') ] (f , gᴰ) (f' , gᴰ'))
      → (Bif-hom×ᴰ fᴰ gᴰ) Eᴰ.∫≡ (Bif-hom×ᴰ fᴰ' gᴰ')
    Bif-hom×ᴰ⟨_⟩⟨_⟩ {gᴰ = gᴰ} {gᴰ'} fᴰ≡fᴰ' gᴰ≡gᴰ' =
      ΣPathP (F.F-hom⟨ PathPΣ fᴰ≡fᴰ' .fst ⟩
      , (λ i → Bif-hom×ᴰ (fᴰ≡fᴰ' i .snd) (rectified-gᴰ≡gᴰ' i)))
      where
      rectified-gᴰ≡gᴰ' : gᴰ Dᴰ.≡[ PathPΣ fᴰ≡fᴰ' .fst ] gᴰ'
      rectified-gᴰ≡gᴰ' = Dᴰ.rectify $ Dᴰ.≡out $ gᴰ≡gᴰ'

  Bif-iso×ᴰ : ∀ {c c'}{cᴰ cᴰ' dᴰ dᴰ'}
      {f : C.ISOC.Hom[ c , c' ]}
      (fᴰ : Cᴰ.ISOCᴰ.Hom[ f ][ cᴰ , cᴰ' ])
      (gᴰ : Dᴰ.ISOCᴰ.Hom[ f ][ dᴰ , dᴰ' ])
      → Eᴰ.ISOCᴰ.Hom[ F.F-iso f ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
  Bif-iso×ᴰ fᴰ gᴰ .funᴰ = Bif-hom×ᴰ (fᴰ .funᴰ) (gᴰ .funᴰ)
  Bif-iso×ᴰ fᴰ gᴰ .invᴰ = Bif-hom×ᴰ (fᴰ .invᴰ) (gᴰ .invᴰ)
  Bif-iso×ᴰ fᴰ gᴰ .secᴰ = sym Bif-×-seqᴰ ∙ Bif-hom×ᴰ⟨ fᴰ .secᴰ ⟩⟨ gᴰ .secᴰ ⟩
    ∙ Bif-×-idᴰ
  Bif-iso×ᴰ fᴰ gᴰ .retᴰ = sym Bif-×-seqᴰ ∙ Bif-hom×ᴰ⟨ fᴰ .retᴰ ⟩⟨ gᴰ .retᴰ ⟩
    ∙ Bif-×-idᴰ
