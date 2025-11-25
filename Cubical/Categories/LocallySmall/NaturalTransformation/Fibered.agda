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
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
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

module FunctorDefs
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ

  Functor : (d : Dob) → Typeω
  Functor d = LocallySmallF.Functor C.cat Dᴰ.v[ d ]

  module _ (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x}) (d : Dob) where
    FunctorEq : Typeω
    FunctorEq = LocallySmallF.Functor C.cat (fibEq Dᴰ D-⋆ d)

    Functor→FunctorEq :
      Functor d → FunctorEq
    Functor→FunctorEq = fib→fibEq Dᴰ D-⋆ d LocallySmallF.∘F_

    FunctorEq→Functor :
      FunctorEq → Functor d
    FunctorEq→Functor = fibEq→fib Dᴰ D-⋆ d LocallySmallF.∘F_

  module FunctorNotation {d : Dob} (F : Functor d)
    where

    open LocallySmallF.FunctorNotation F public

module NatTransDefs
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  open FunctorDefs C Dᴰ public
  module _
    {d d' : Dob} (g : D.Hom[ d , d' ])
    (F : Functor d)
    (G : Functor d')
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G

    N-homTy :
      (N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])
      → ∀ {x y} → (f  : C.Hom[ liftω x , liftω y ]) → Type _
    N-homTy N-ob {x} {y} f =
      (F.F-hom f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ G.F-hom f)

    record NatTrans : Type (ℓ-max (DHom-ℓ d d') (ℓ-max (DHom-ℓᴰ d d') $ ℓ-max ℓC' ℓC))
      where
      no-eta-equality
      constructor natTrans
      field
        N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ]
        N-hom : ∀ {x y} (f : C.Hom[ liftω x , liftω y ]) → N-homTy N-ob f

  open NatTrans

  idFibTrans : ∀ {d}(F : Functor d)
    → NatTrans D.id F F
  idFibTrans F .N-ob _ = Dᴰ.idᴰ
  idFibTrans F .N-hom f =
    Dᴰ.⋆IdRᴰ _
    ∙ (sym $ Dᴰ.⋆IdLᴰ _)

  seqFibTrans : ∀ {d d' d''}
    {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
    {F G H}
    (α : NatTrans g F G)
    (β : NatTrans g' G H)
    → NatTrans (g D.⋆ g') F H
  seqFibTrans α β .N-ob x = α .N-ob x Dᴰ.⋆ᴰ β .N-ob x
  seqFibTrans {F = F} {H = H} α β .N-hom f =
      (sym $ Dᴰ.⋆Assocᴰ _ _ _)
      ∙ Dᴰ.⟨ N-hom α f ⟩⋆⟨⟩
      ∙ Dᴰ.⋆Assoc _ _ _
      ∙ Dᴰ.⟨⟩⋆⟨ N-hom β f ⟩
      ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)

  module _
    {d d'}
    (g : D.Hom[ d , d' ])
    (F : Functor d)
    (G : Functor d')
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
    NatTransIsoΣ :
      Iso (NatTrans g F G)
        (Σ[ N-ob ∈ (∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])]
        (∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → N-homTy g F G N-ob f))
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote (NatTrans))

    isSetNatTrans : isSet (NatTrans g F G)
    isSetNatTrans = isSetIso NatTransIsoΣ
      (isSetΣSndProp (isSetΠ (λ _ → Dᴰ.isSetHomᴰ))
        (λ _ → isPropImplicitΠ2 λ _ _ → isPropΠ λ _ →
          isSetΣ D.isSetHom (λ _ → Dᴰ.isSetHomᴰ) _ _))

  module _
    {d d'}
    {g g' : D.Hom[ d , d' ]}
    {F : Functor d}
    {G : Functor d'}
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G

    makeNatTransPathP :
      {α : NatTrans g F G}
      {β : NatTrans g' F G}
      → (g≡g' : g ≡ g')
      → PathP
          (λ i → ∀ x →
            Dᴰ.Hom[ g≡g' i ][ F.F-ob (liftω x) ,
                              G.F-ob (liftω x) ])
          (α .N-ob)
          (β .N-ob)
      → PathP (λ i → NatTrans (g≡g' i) F G) α β
    makeNatTransPathP g≡g' p i .N-ob x = p i x
    makeNatTransPathP {α = α} {β = β} g≡g' p i .N-hom {x = x} {y = y} f =
      isSet→SquareP (λ _ _ → isSetΣ D.isSetHom (λ _ → Dᴰ.isSetHomᴰ))
        (α .N-hom f) (β .N-hom f)
        (λ j → _ , (F.F-hom f Dᴰ.⋆ᴰ p j y))
        (λ j → _ , (p j x Dᴰ.⋆ᴰ G.F-hom f))
        i

  module _
    {d d'} {g g' : D.Hom[ d , d' ]}
    {F : Functor d}
    {G : Functor d'}
    {α : NatTrans g F G}
    {β : NatTrans g' F G}
    (g≡g' : g ≡ g')
    (p : ∀ x → α .N-ob x Dᴰ.∫≡ β .N-ob x)
    where

    makeNatTransPath :
      Path (Σ[ h ∈ (D.Hom[ d , d' ]) ] NatTrans h F G) ((_ , α)) ((_ , β))
    makeNatTransPath =
      ΣPathP
        (g≡g' ,
        makeNatTransPathP g≡g' (funExt λ x → Dᴰ.rectify (Dᴰ.≡out (p x))))
