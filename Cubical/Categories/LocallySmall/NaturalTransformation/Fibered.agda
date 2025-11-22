module Cubical.Categories.LocallySmall.NaturalTransformation.Fibered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallFunctor
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties

open Category
open Categoryᴰ
open SmallCategory

module FiberedFunctorDefs
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ

  FiberedFunctor : (d : Dob) → Typeω
  FiberedFunctor d = Functor C.cat Dᴰ.v[ d ]

  module _ (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x}) (d : Dob) where
    FiberedFunctorEq : Typeω
    FiberedFunctorEq = Functor C.cat (fibEq Dᴰ D-⋆ d)

    FiberedFunctor→FiberedFunctorEq :
      FiberedFunctor d → FiberedFunctorEq
    FiberedFunctor→FiberedFunctorEq = fib→fibEq Dᴰ D-⋆ d ∘F_

    FiberedFunctorEq→FiberedFunctor :
      FiberedFunctorEq → FiberedFunctor d
    FiberedFunctorEq→FiberedFunctor = fibEq→fib Dᴰ D-⋆ d ∘F_

  module FiberedFunctorNotation {d : Dob} (F : FiberedFunctor d)
    where

    open FunctorNotation F public

module FibNatTransDefs
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  open FiberedFunctorDefs C Dᴰ public
  module _
    {d d' : Dob} (g : D.Hom[ d , d' ])
    (F : FiberedFunctor d)
    (G : FiberedFunctor d')
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G

    N-homTy :
      (N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])
      → ∀ {x y} → (f  : C.Hom[ liftω x , liftω y ]) → Type _
    N-homTy N-ob {x} {y} f =
      (F.F-hom f Dᴰ.⋆ⱽᴰ N-ob y) ≡
      (N-ob x Dᴰ.⋆ᴰⱽ G.F-hom f)

    record FibNatTrans : Type (ℓ-max (DHom-ℓᴰ d d') $ ℓ-max ℓC' ℓC)
      where
      no-eta-equality
      constructor natTrans
      field
        N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ]
        N-hom : ∀ {x y} (f : C.Hom[ liftω x , liftω y ]) → N-homTy N-ob f

      N-hom' : ∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ G.F-hom f)
      N-hom' f =
        Dᴰ.reind-filler _ _
        ∙ Dᴰ.≡in (N-hom f)
        ∙ (sym $ Dᴰ.reind-filler _ _)

  module _
    {d d' : Dob} {g : D.Hom[ d , d' ]}
    (F : FiberedFunctor d)
    (G : FiberedFunctor d')
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G
    module _
      (N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])
      where
      N-hom'→N-hom : ∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ G.F-hom f)
          → N-homTy g F G N-ob f
      N-hom'→N-hom f p =
        Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ p
          ∙ Dᴰ.reind-filler _ _

  open FibNatTrans

  idFibTrans : ∀ {d}(F : FiberedFunctor d)
    → FibNatTrans D.id F F
  idFibTrans F .N-ob _ = Dᴰ.idᴰ
  idFibTrans F .N-hom f =
    N-hom'→N-hom F F (λ _ → Dᴰ.idᴰ) f
      (Dᴰ.⋆IdRᴰ _ ∙ (sym $ Dᴰ.⋆IdLᴰ _))

  seqFibTrans : ∀ {d d' d''}
    {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
    {F G H}
    (α : FibNatTrans g F G)
    (β : FibNatTrans g' G H)
    → FibNatTrans (g D.⋆ g') F H

  seqFibTrans α β .N-ob x = α .N-ob x Dᴰ.⋆ᴰ β .N-ob x
  seqFibTrans {F = F} {H = H} α β .N-hom f =
    N-hom'→N-hom F H _ f
      ((sym $ Dᴰ.⋆Assocᴰ _ _ _)
      ∙ Dᴰ.⟨ N-hom' α f ⟩⋆⟨⟩
      ∙ Dᴰ.⋆Assoc _ _ _
      ∙ Dᴰ.⟨⟩⋆⟨ N-hom' β f ⟩
      ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _))

  module _
    {d d'}
    (g : D.Hom[ d , d' ])
    (F : FiberedFunctor d)
    (G : FiberedFunctor d')
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G
    FibNatTransIsoΣ :
      Iso (FibNatTrans g F G)
        (Σ[ N-ob ∈ (∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])]
        (∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → N-homTy g F G N-ob f))
    unquoteDef FibNatTransIsoΣ = defineRecordIsoΣ FibNatTransIsoΣ (quote (FibNatTrans))

    isSetFibNatTrans : isSet (FibNatTrans g F G)
    isSetFibNatTrans =
      isSetRetract (Iso.fun FibNatTransIsoΣ ) (Iso.inv FibNatTransIsoΣ)
        (Iso.leftInv FibNatTransIsoΣ)
        (isSetΣSndProp
          (isSetΠ (λ _ → Dᴰ.isSetHomᴰ))
          (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → Dᴰ.isSetHomᴰ _ _))))

  module _
    {d d'}
    {g g' : D.Hom[ d , d' ]}
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G

    makeFibNatTransPathP :
      {α : FibNatTrans g F G}
      {β : FibNatTrans g' F G}
      → (g≡g' : g ≡ g')
      → PathP
          (λ i → ∀ x →
            Dᴰ.Hom[ g≡g' i ][ F.F-ob (liftω x) ,
                              G.F-ob (liftω x) ])
          (α .N-ob)
          (β .N-ob)
      → PathP (λ i → FibNatTrans (g≡g' i) F G) α β
    makeFibNatTransPathP g≡g' p i .N-ob x = p i x
    makeFibNatTransPathP {α = α} {β = β} g≡g' p i .N-hom {x = x} {y = y} f =
      isSet→SquareP (λ i j → Dᴰ.isSetHomᴰ)
        (α .N-hom f)
        (β .N-hom f)
        (λ j → F.F-hom f Dᴰ.⋆ⱽᴰ p j y)
        (λ j → p j x Dᴰ.⋆ᴰⱽ G.F-hom f)
        i

  module _
    {d d'} {g g' : D.Hom[ d , d' ]}
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    {α : FibNatTrans g F G}
    {β : FibNatTrans g' F G}
    (g≡g' : g ≡ g')
    (p : ∀ x → α .N-ob x Dᴰ.∫≡ β .N-ob x)
    where

    makeFibNatTransPath :
      Path (Σ[ h ∈ (D.Hom[ d , d' ]) ] FibNatTrans h F G) ((_ , α)) ((_ , β))
    makeFibNatTransPath =
      ΣPathP
        (g≡g' ,
        makeFibNatTransPathP g≡g' (funExt λ x → Dᴰ.rectify (Dᴰ.≡out (p x))))
