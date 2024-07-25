{-# OPTIONS --lossy-unification #-}
module Gluing.Conservativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Constructions.Free.Category.Quiver as FC
  hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base as FCC
  hiding (rec)
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct

private
  variable ℓQ ℓQ' ℓC ℓC' : Level

open Category
open Functor
open Categoryᴰ
open Section
open NatTrans

Quiver→×Quiver : ∀{ℓ ℓ' : Level} → Quiver ℓ ℓ' → ×Quiver ℓ ℓ'
Quiver→×Quiver Q .fst = Q .fst
Quiver→×Quiver Q .snd .ProductQuiver.mor = Q .snd .QuiverOver.mor
Quiver→×Quiver Q .snd .ProductQuiver.dom = ↑_ ∘S Q .snd .QuiverOver.dom
Quiver→×Quiver Q .snd .ProductQuiver.cod = ↑_ ∘S Q .snd .QuiverOver.cod

module _ (Q : Quiver ℓQ ℓQ') where
  FREE : Category _ _
  FREE = FreeCat Q

  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory (Quiver→×Quiver Q)

  ı : Interp Q (FREE-1,× .fst)
  ı ._$g_ = ↑_
  ı ._<$g>_ = ↑ₑ_

  ⊆ : Functor FREE (FREE-1,× .fst)
  ⊆ = FC.rec Q ı

  -- TODO: wts ⊆* is fully faithful

  -- the use of rec to define the functor is just to save work
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

  -- inductive normal forms, later
  --NormalForm : (A : FREE-1,× .fst .ob) → (B : FREE-1,× .fst .ob) → Type {!!}
  --NormalForm (↑ x) B = {!!}
  --NormalForm (x × y) B = {!!}
  --NormalForm ⊤ B = {!!}

  ---- NOTE: WRONG
  ---- this has the same data as extension, but the usage is completely different
  ---- and we actually need this definition on products and terminal
  --nerve : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  --nerve = extension

  YOish : (o : Q .fst) → Presheaf FREE _
  YOish o .F-ob ι = FREE-1,× .fst [ ⊆ ⟅ ι ⟆ , ⊆ ⟅ o ⟆ ] , FREE-1,× .fst .isSetHom
  YOish o .F-hom t = λ f → ⊆ ⟪ t ⟫ ⋆⟨ FREE-1,× .fst ⟩ f
  YOish o .F-id = funExt (FREE-1,× .fst .⋆IdL)
  YOish o .F-seq _ _ = funExt (λ _ → FREE-1,× .fst .⋆Assoc _ _ _)

  YOish' : (e : Q .snd .QuiverOver.mor) → PresheafCategory FREE _ [ YOish (Q .snd .QuiverOver.dom e) , YOish (Q .snd .QuiverOver.cod e) ]
  YOish' e = natTrans (λ o g → g ⋆⟨ FREE-1,× .fst ⟩ ⊆ ⟪ ↑ e ⟫) (λ _ → funExt (λ _ → FREE-1,× .fst .⋆Assoc _ _ _))

  YOish'' : Functor (FREE-1,× .fst) (PresheafCategory FREE _)
  YOish'' = FCC.rec (Quiver→×Quiver Q)
    (PresheafCategory FREE _ , ⊤𝓟 _ _ , ×𝓟 _ _)
    YOish
    YOish'

  -- TODO: this elim stuff doesn't quite have the right "nice" interface
  -- Reindex/Properties needs fixing
  -- Also the names don't always match
  foo : Section YOish'' (PRESHEAFᴰ FREE _ _)
  foo = elimLocal' (Quiver→×Quiver Q)
    (LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals FREE _ _ _))
    (LiftedBinProdsReindex' (BinProductsToBinProducts' _ (FREE-1,× .snd .snd)) (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _))
    OB
    HOM
    where
    --module Q = ×QuiverNotation (Quiver→×Quiver Q)
    OB : (o : FREE .ob) → Presheafᴰ FREE _ _ (YOish'' ⟅ ⊆ ⟅ o ⟆ ⟆)
    OB o .F-ob (o' , f) = FREE [ o' , o ] , FREE .isSetHom
    OB o .F-hom {x = o',o'→o} {y = o'',o''→o} (f , p) g = f ⋆⟨ FREE ⟩ g -- TODO: var names
    OB o .F-id = funExt (FREE .⋆IdL)
    OB o .F-seq _ _ = funExt (FREE .⋆Assoc _ _)
    module 𝓟FREEᴰ = Categoryᴰ (PRESHEAFᴰ FREE _ _)
    HOM : (e : Q .snd .QuiverOver.mor) → 𝓟FREEᴰ.Hom[ YOish'' ⟪ ↑ₑ e ⟫ ][ OB (Q .snd .QuiverOver.dom e) , OB (Q .snd .QuiverOver.cod e) ]
    HOM e = natTrans (λ  _ x → x ⋆⟨ FREE ⟩ ↑ e) λ f → funExt (λ x₁ → FREE .⋆Assoc _ _ _)

  ⊆-Full : isFull ⊆
  ⊆-Full o o' F[f] = ∣ foo .F-homᴰ F[f] .N-ob (o , FREE-1,× .fst .id) (FREE .id) , {!refl!} ∣₁

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
