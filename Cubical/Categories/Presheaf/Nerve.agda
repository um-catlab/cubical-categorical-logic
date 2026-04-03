{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Nerve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory as ∫
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open PshHomStrict
open Section
open PshHom

-- The nerve functor along F : Functor C D
-- Maps d ∈ D to the presheaf c ↦ D [ F c , d ]
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
  Nerve : Functor D (PRESHEAF C ℓD')
  Nerve = reindPshFStrict F ∘F YOStrict

  -- The nerve functor always preserves binary products because
  -- presheaf limits are computed pointwise:
  -- D [ F c , A × B ] ≅ D [ F c , A ] × D [ F c , B ]
  module _ (bps : BinProducts D) where
    Nerve-pres-bp : preservesProvidedBinProducts Nerve bps
    Nerve-pres-bp A B Γ = isoToIsEquiv the-iso
      where
      open Iso
      module bp = BinProductNotation (bps (A , B))

      pairHom : PshHomStrict Γ (Nerve ⟅ A ⟆) → PshHomStrict Γ (Nerve ⟅ B ⟆)
              → PshHomStrict Γ (Nerve ⟅ bp.vert ⟆)
      pairHom α β .N-ob c x = α .N-ob c x bp.,p β .N-ob c x
      pairHom α β .N-hom c c' f x' x eq =
        sym (bp.,p≡
          (sym (α .N-hom c c' f x' x eq)
           ∙ cong (λ g → F ⟪ f ⟫ ⋆⟨ D ⟩ g) (sym bp.×β₁)
           ∙ sym (D .⋆Assoc _ _ _))
          (sym (β .N-hom c c' f x' x eq)
           ∙ cong (λ g → F ⟪ f ⟫ ⋆⟨ D ⟩ g) (sym bp.×β₂)
           ∙ sym (D .⋆Assoc _ _ _)))

      the-iso : Iso (PshHomStrict Γ (Nerve ⟅ bp.vert ⟆))
                    (PshHomStrict Γ (Nerve ⟅ A ⟆) × PshHomStrict Γ (Nerve ⟅ B ⟆))
      the-iso .fun f = f ⋆PshHomStrict Nerve ⟪ bp.π₁ ⟫ , f ⋆PshHomStrict Nerve ⟪ bp.π₂ ⟫
      the-iso .inv (α , β) = pairHom α β
      the-iso .sec (α , β) = ΣPathP
        ( makePshHomStrictPath (funExt₂ λ c x → bp.×β₁)
        , makePshHomStrictPath (funExt₂ λ c x → bp.×β₂))
      the-iso .ret f = makePshHomStrictPath (funExt₂ λ c x →
        bp.,p-extensionality bp.×β₁ bp.×β₂)

  -- How to think of a displayed presheaf?
  -- It's a proof-relevant version of a pre-composition-closed subset.

  -- In this case, we are defining an invariant on morphisms
  -- of the form D [ F- , F c ]
  --
  -- The property is that they are in the image of F ⟪_⟫

  -- This is (obviously) closed under precomposition with morphisms F
  -- ⟪ f ⟫ by functoriality
  NerveᴰOb : ∀ c → Presheafᴰ ((Nerve ∘F F) ⟅ c ⟆) (Unitᴰ C) ((ℓ-max ℓC' ℓD'))
  NerveᴰOb c .F-ob (c' , _ , f) .fst = fiber (F .F-hom) f
  NerveᴰOb c .F-ob (c' , _ , f) .snd = isSetΣ (isSetHom C) (λ f → isProp→isSet (isSetHom D _ _))
  -- f : C [ c , c' ]
  -- g : D [ F ⟅ c' ⟆ , F ⟅ c '' ⟆ ]
  -- F ⟪ F⁻g ⟫ = g
  ---------------------
  -- we can construct F⁻(F ⟪ f ⟫ ⋆ g) as f ⋆ F⁻g
  NerveᴰOb c .F-hom {y = (_ , _ , g)} (f , _ , p) F⁻g =
    f C.⋆ F⁻g .fst , F .F-seq _ _ ∙ D.⟨ refl ⟩⋆⟨ F⁻g .snd ⟩ ∙ Eq.eqToPath p
  NerveᴰOb c .F-id = funExt (λ F⁻g →
    ΣPathPProp (λ a → D.isSetHom _ _) (C.⋆IdL (F⁻g .fst)))
  NerveᴰOb c .F-seq f g = funExt λ F⁻h →
    ΣPathPProp (λ a → D.isSetHom _ _) (C.⋆Assoc (g .fst) (f .fst) (F⁻h .fst))

  -- The functoriality of this section says that the action
  -- post-composition with a morphism F ⟪ f ⟫ preserves the property of
  -- being in the image of F ⟪_⟫ (also by functoriality of F).
  Nerveᴰ : Section (Nerve ∘F F) (PRESHEAFᴰ (Unitᴰ C) ℓD' (ℓ-max ℓC' ℓD'))
  Nerveᴰ .F-obᴰ = NerveᴰOb
  Nerveᴰ .F-homᴰ f .N-ob (c , _ , g) F⁻g .fst = F⁻g .fst C.⋆ f
  Nerveᴰ .F-homᴰ f .N-ob (c , _ , g) F⁻g .snd =
    F .F-seq _ _ ∙ D.⟨ F⁻g .snd ⟩⋆⟨ refl ⟩
  Nerveᴰ .F-homᴰ f .N-hom _ _ (g , _) (h , _) = ΣPathPProp (λ a → D.isSetHom _ _)
    (C.⋆Assoc g h f)
  Nerveᴰ .F-idᴰ = makePshHomᴰPathP _ _ _ (funExt (λ (c , _ , g) → funExt (λ F⁻g →
    ΣPathPProp (λ a → D.isSetHom (F .F-hom a) g) (C.⋆IdR (F⁻g .fst)))))
  Nerveᴰ .F-seqᴰ f g = makePshHomᴰPathP _ _ _ (funExt λ _ → funExt λ _ →
    ΣPathPProp (λ _ → D.isSetHom _ _) (sym (C.⋆Assoc _ _ _)))

  -- The Nerveᴰ is faithful basically by a Yoneda argument and the
  -- fact that D.id {F ⟅ c ⟆} is in the image of F ⟪_⟫
  Nerveᴰ-faithful : isFaithful (intro (Nerve ∘F F) Nerveᴰ)
  Nerveᴰ-faithful x y f g Nf≡Ng =
    f
      ≡⟨ (sym $ C.⋆IdL _) ⟩
    Nerveᴰ .F-homᴰ f .N-ob (x , tt , D.id) (C.id , F .F-id) .fst
      ≡[ i ]⟨ Nf≡Ng i .snd .N-ob (x , tt , D.id) (C.id , F .F-id) .fst ⟩
    Nerveᴰ .F-homᴰ g .N-ob (x , tt , D.id) (C.id , F .F-id) .fst
      ≡⟨ C.⋆IdL _ ⟩
    g ∎

  -- The following looks like it's provable because it looks
  -- Yoneda-ish but it's not, it's nerveish.
  
  -- α is a PshHom (D [ F⟅-⟆ , x ]) (D [ F⟅-⟆ , y ])
  -- αᴰ is a PshHomᴰ α (Nerveᴰ x) (Nerveᴰ y)
  -- Nerveᴰ-full : isFull (intro (Nerve ∘F F) Nerveᴰ)
  -- Nerveᴰ-full x y (α , αᴰ) =
  --   ∣ (αᴰ .N-ob (x , tt , D.id) (C.id , F .F-id) .fst)
  --   , ΣPathP ((makePshHomStrictPath (funExt (λ Γ → funExt (λ f →
  --     D.⟨ refl ⟩⋆⟨ αᴰ .N-ob (x , tt , D.id) (C.id , F .F-id) .snd ⟩
  --     ∙ {!α .N-hom!})))) -- stuck here because you don't know f is in the image of F⟪_⟫
  --   , {!!}) ∣₁

  -- The interesting thing is that we can use Nerveᴰ to prove that F
  -- is fully faithful.
  --
  -- What we need is a section of the Nerve functor that
  -- when composed with F is equivalent to Nerveᴰ.
  --
  -- The idea is that a section of the nerve functor is *some*
  -- invariant of morphisms in D that is preserved by pre-composition
  -- with morphism F ⟪ f ⟫ and post-composition with arbitrary
  -- morphisms of D.
  --
  -- If this restricts on F to something equivalent to Nerveᴰ then
  -- that means that it is full and faithful because 1. Nerveᴰ is
  -- faithful and 2. it establishes that all morphisms of D (of
  -- appropriate type) preserve the invariant of being in the image of
  -- F and so they are in the image of F themselves because id is and
  -- g = id ⋆ g.
  module _
    -- technically the universe levels don't have to line up this
    -- closely but at least in the conservativity proofs they do so
    -- w/e
    (S : Section Nerve (PRESHEAFᴰ (Unitᴰ C) ℓD' (ℓ-max ℓC' ℓD')))
    -- we should weaken this to a natiso
    (SF≡Nerveᴰ : compSectionFunctor S F ≡ Nerveᴰ)
    where
    -- Firstly, this implies that F is faithful because S ∘ F is faithful
    SF-faithful : isFaithful (intro (Nerve ∘F F) (compSectionFunctor S F))
    SF-faithful = subst (λ SF → isFaithful (intro (Nerve ∘F F) SF)) (sym SF≡Nerveᴰ)
      Nerveᴰ-faithful

    F-faithful : isFaithful F
    F-faithful x y f g Ff≡Fg = SF-faithful x y f g λ i →
      Nerve ⟪ Ff≡Fg i ⟫ , S .F-homᴰ (Ff≡Fg i)

    -- next this says that any g : D [ F ⟅ c ⟆ , F ⟅ c' ⟆ ] preserves
    -- the invariant of being in the image of F, which implies that F
    -- is full as well.
    module _ {c c'} (g : D [ F ⟅ c ⟆ , F ⟅ c' ⟆ ]) where
      Ng :
        ⟨ Nerveᴰ .F-obᴰ c .F-ob (c , tt , D.id) ⟩
        → ⟨ Nerveᴰ .F-obᴰ c' .F-ob (c , tt , D.id D.⋆ g) ⟩
      Ng = subst {A = Section (Nerve ∘F F) ((PRESHEAFᴰ (Unitᴰ C) ℓD' (ℓ-max ℓC' ℓD')))}
        {x = compSectionFunctor S F}
        {y = Nerveᴰ}
        (λ SF → ⟨ SF .F-obᴰ c .F-ob (c , tt , D.id) ⟩ → ⟨ SF .F-obᴰ c' .F-ob (c , tt , D.id D.⋆ g) ⟩)
        SF≡Nerveᴰ
        (S .F-homᴰ g .N-ob (c , tt , D.id))

    isFullF : isFull F
    isFullF x y F[f] = ∣ F⁻[f]' .fst , F⁻[f]' .snd ∙ D.⋆IdL F[f] ∣₁ where
      F⁻[f]' = Ng F[f] (C.id , F .F-id)

    isFullyFaithfulF : isFullyFaithful F
    isFullyFaithfulF = isFull+Faithful→isFullyFaithful {F = F} isFullF F-faithful

-- YOStrict preserves binary products (special case of Nerve-pres-bp
-- with the identity functor, since Nerve Id ≡ YOStrict by computation)
module _ {C : Category ℓC ℓC'} (bps : BinProducts C) where
  YOStrict-pres-bp : preservesProvidedBinProducts (YOStrict {C = C}) bps
  YOStrict-pres-bp A B Γ = isoToIsEquiv the-iso
    where
    open Iso
    module bp = BinProductNotation (bps (A , B))

    pairHom : PshHomStrict Γ (YOStrict ⟅ A ⟆) → PshHomStrict Γ (YOStrict ⟅ B ⟆)
            → PshHomStrict Γ (YOStrict ⟅ bp.vert ⟆)
    pairHom α β .N-ob c x = α .N-ob c x bp.,p β .N-ob c x
    pairHom α β .N-hom c c' f x' x eq =
      sym (bp.,p≡
        (sym (α .N-hom c c' f x' x eq)
         ∙ cong (λ g → f ⋆⟨ C ⟩ g) (sym bp.×β₁)
         ∙ sym (C .⋆Assoc _ _ _))
        (sym (β .N-hom c c' f x' x eq)
         ∙ cong (λ g → f ⋆⟨ C ⟩ g) (sym bp.×β₂)
         ∙ sym (C .⋆Assoc _ _ _)))

    the-iso : Iso (PshHomStrict Γ (YOStrict ⟅ bp.vert ⟆))
                  (PshHomStrict Γ (YOStrict ⟅ A ⟆) × PshHomStrict Γ (YOStrict ⟅ B ⟆))
    the-iso .fun f = f ⋆PshHomStrict YOStrict ⟪ bp.π₁ ⟫ , f ⋆PshHomStrict YOStrict ⟪ bp.π₂ ⟫
    the-iso .inv (α , β) = pairHom α β
    the-iso .sec (α , β) = ΣPathP
      ( makePshHomStrictPath (funExt₂ λ c x → bp.×β₁)
      , makePshHomStrictPath (funExt₂ λ c x → bp.×β₂))
    the-iso .ret f = makePshHomStrictPath (funExt₂ λ c x →
      bp.,p-extensionality bp.×β₁ bp.×β₂)

-- When D is a cartesian category, the nerve is a cartesian functor
module _ {C : Category ℓC ℓC'} {D : CartesianCategory ℓD ℓD'} (F : Functor C (D .CartesianCategory.C)) where
  private
    module D = CartesianCategory D

  CartesianNerve : CartesianFunctor D (PRESHEAF C ℓD')
  CartesianNerve = Nerve F , Nerve-pres-bp F D.bp
