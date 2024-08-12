---
title: finite products are a conservative extension over the free category, via gluing of displayed categories
abstract: >
    To demonstate some facilities of this library,
    we use a logical relations construction to show that the inclusion functor from the free category over a quiver Q,
    to the free category with finite products over Q, is fully faithful.
    Viewing free categories as proof-relevant syntactic theories of type inhabitation, this states that
    the addition of finite product types is a conservative extension of the product-less Q-theory.
    We normalize (potentially) product-ful Q-terms by lifting them into a normal-forms category displayed over the product-ful Q-theory,
    where the normal-forms category is a gluing of the syntax with displayed presheaves.
---

---

a.

We start by importing everything we need from
[the upstream cubical agda standard library](https://github.com/agda/cubical) and
[this library](https://github.com/maxsnew/cubical-categorical-logic).

(`--lossy-unification` just keeps the type checking time sufficiently interactive.)
```agda
{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Conservativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Constructions.Free.Category.Quiver as FC
  hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base as FCC
  hiding (rec)
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct
```
We open some frequently used namespaces for convenience.
```agda
open Category
open Functor
open NatTrans
open Cubical.Categories.Constructions.Elements.Contravariant
open Categoryᴰ
open Section
open CartesianOver
```
A free category with finite products TODO
```agda
Quiver→×Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → ×Quiver ℓ ℓ'
Quiver→×Quiver Q .fst = Q .fst
Quiver→×Quiver Q .snd .ProductQuiver.mor = Q .snd .QuiverOver.mor
Quiver→×Quiver Q .snd .ProductQuiver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→×Quiver Q .snd .ProductQuiver.cod = ↑_ ∘S Q .snd .QuiverOver.cod
```
Everything is relative to a Quiver/Signature TODO
```agda
module _ {ℓQ ℓQ'} (Q : Quiver ℓQ ℓQ') where
  private module Q = QuiverOver (Q .snd)

```
Q-Category
```agda
  FREE : Category _ _
  FREE = FreeCat Q

```
Q-(Category with finite products)
```agda
  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory (Quiver→×Quiver Q)

  ı : Interp Q (FREE-1,× .fst)
  ı ._$g_ = ↑_
  ı ._<$g>_ = ↑ₑ_
```
the "main culprit"
```agda
  ⊆ : Functor FREE (FREE-1,× .fst)
  ⊆ = FC.rec Q ı

```
the use of rec to define the functor is just to save work, since no specific
behavior on non-atoms is required

contrast this with `nerve` later
```agda
  extension : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  extension = FCC.rec (Quiver→×Quiver Q)
    (PresheafCategory FREE _ , ⊤𝓟 _ _ , ×𝓟 _ _)
    (YO ⟅_⟆)
    λ f → YO ⟪ ↑ f ⟫

  commutes : YO ≡ extension ∘F ⊆
  commutes = FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

  comp-Faithful : isFaithful (extension ∘F ⊆)
  comp-Faithful = subst isFaithful commutes isFaithfulYO

  -- TODO: move this general fact about isFaithful if it isn't already in stdlib
  module _ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
    {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
    (F : Functor A B)(G : Functor B C) where
    isFaithful-GF→isFaithful-F : isFaithful (G ∘F F) → isFaithful F
    isFaithful-GF→isFaithful-F faith x y f g p =
      faith x y f g (congS (λ Ff → G ⟪ Ff ⟫) p)

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-GF→isFaithful-F ⊆ extension comp-Faithful

```
same type as `extension` but very different usage, and now we *do* care about
the definitional behavior on non-atoms (ie F-hom), or else we get stuck in
⊆-Full
```agda
  nerve : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  nerve .F-ob Γ .F-ob A =
    (FREE-1,× .fst) [ ⊆ ⟅ A ⟆ , Γ ] , FREE-1,× .fst .isSetHom
  nerve .F-ob Γ .F-hom t = λ δ → ⊆ ⟪ t ⟫ ⋆⟨ FREE-1,× .fst ⟩ δ
  nerve .F-ob Γ .F-id = funExt (FREE-1,× .fst .⋆IdL)
  nerve .F-ob Γ .F-seq _ _ = funExt (λ _ → FREE-1,× .fst .⋆Assoc _ _ _)
  nerve .F-hom δ = natTrans (λ _ → λ δ' → δ' ⋆⟨ FREE-1,× .fst ⟩ δ)
    (λ _ → funExt (λ _ → FREE-1,× .fst .⋆Assoc _ _ _))
  nerve .F-id = makeNatTransPath (funExt (λ _ → funExt (FREE-1,× .fst .⋆IdR)))
  nerve .F-seq _ _ = makeNatTransPath
    (funExt (λ _ → funExt (λ _ → sym (FREE-1,× .fst .⋆Assoc _ _ _))))

  private
    𝓟ᴰFREE = PRESHEAFᴰ FREE (ℓ-max ℓQ ℓQ') (ℓ-max ℓQ ℓQ')
    module 𝓟ᴰFREE = Categoryᴰ 𝓟ᴰFREE

  S : Section nerve 𝓟ᴰFREE
  S = elimLocal' (Quiver→×Quiver Q)
    (LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals FREE _ _ _))
    (LiftedBinProductsReindex'
      (BinProductsToBinProducts' _ (FREE-1,× .snd .snd))
      (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _))
    OB
    HOM
    where
    OB : (o : FREE .ob) → Presheafᴰ _ _ _ (nerve ⟅ ⊆ ⟅ o ⟆ ⟆)
    OB o .F-ob (o' , o'→×o) = (Σ[ f ∈ FREE [ o' , o ] ] ⊆ ⟪ f ⟫ ≡ o'→×o) ,
      isSetΣ (FREE .isSetHom)
      (λ _ → isSet→isGroupoid (FREE-1,× .fst .isSetHom) _ _)
    OB o .F-hom {x = o',o'→×o} {y = o'',o''→×o} (o''→o' , p) =
      λ (witness-o'→o , q) → witness-o'→o ∘⟨ FREE ⟩ o''→o' ,
      ⊆ .F-seq _ _ ∙ congS (λ x → ⊆ ⟪ o''→o' ⟫ ⋆⟨ FREE-1,× .fst ⟩ x) q ∙ p
    OB o .F-id = funExt (λ _ → ΣPathP (FREE .⋆IdL _ ,
      isSet→SquareP (λ _ _ → FREE-1,× .fst .isSetHom) _ _ _ _))
    OB o .F-seq _ _ = funExt (λ _ → ΣPathP (FREE .⋆Assoc _ _ _ ,
      isSet→SquareP (λ _ _ → FREE-1,× .fst .isSetHom) _ _ _ _))
    HOM : (e : Q.mor) →
      𝓟ᴰFREE.Hom[ nerve ⟪ ⊆ ⟪ ↑ e ⟫ ⟫ ][ OB (Q.dom e) , OB (Q.cod e) ]
    HOM e = natTrans
      (λ (o , o→×∙e) (witness-o→∙e , p) →
        ↑ e ∘⟨ FREE ⟩ witness-o→∙e , ⊆ .F-seq _ _ ∙
        congS (λ x → ⊆ ⟪ ↑ e ⟫ ∘⟨ FREE-1,× .fst ⟩ x) p)
      λ f → funExt (λ _ → ΣPathP (FREE .⋆Assoc _ _ _ ,
        isSet→SquareP (λ _ _ → FREE-1,× .fst .isSetHom) _ _ _ _))

```
instantiate gluing argument
```agda
  ⊆-Full : isFull ⊆
  ⊆-Full o o' F[f] = ∣ f , p ∙ FREE-1,× .fst .⋆IdL _ ∣₁
    where
    ⊆[→o'] : 𝓟ᴰFREE.ob[ nerve ⟅ ⊆ ⟅ o' ⟆ ⟆ ]
    ⊆[→o'] = S .F-obᴰ (⊆ ⟅ o' ⟆)
    ⊆[→o']* : 𝓟ᴰFREE.ob[ nerve ⟅ ⊆ ⟅ o ⟆ ⟆ ]
    ⊆[→o']* = PRESHEAFᴰ-AllCartesianOvers _ _ _ ⊆[→o'] (nerve ⟪ F[f] ⟫) .f*cᴰ'
    f,p : ⟨ ⊆[→o']* ⟅ o , FREE-1,× .fst .id ⟆ ⟩
    f,p = (S .F-homᴰ F[f] ⟦ o , FREE-1,× .fst .id ⟧) (FREE .id , refl)
    f : FREE [ o , o' ]
    f = f,p .fst
    p : ⊆ ⟪ f ⟫ ≡ FREE-1,× .fst .id ⋆⟨ FREE-1,× .fst ⟩ F[f]
    p = f,p .snd

```
And finally,
```agda
  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
```
