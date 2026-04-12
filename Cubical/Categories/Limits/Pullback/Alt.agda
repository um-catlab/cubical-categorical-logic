{-# OPTIONS --lossy-unification #-}
-- A definition of pullbacks bootstapped using
-- products in a slice category
--
-- A pullback of f : l → m and g : r → m is usually presented
-- as the universal object pb making the following diagram commute
--
--             pbπ₂
--        pb --------> r
--        |_|          |
--   pbπ₁ |            |g
--        |            |
--        v            v
--        l  --------> m
--              f
--
-- This universal property can be stated directly,
-- as in Cubical.Categories.Limits.Pullback where a pullback is
-- described with a record spelling out each part of the above
-- diagram
-- record Pullback (cspn : Cospan) : Type (ℓ-max ℓ ℓ') where
--   field
--     pbOb  : ob
--     pbPr₁ : C [ pbOb , cspn .l ]
--     pbPr₂ : C [ pbOb , cspn .r ]
--     pbCommutes : pbPr₁ ⋆ cspn .s₁ ≡ pbPr₂ ⋆ cspn .s₂
--     univProp : isPullback cspn pbPr₁ pbPr₂ pbCommutes
--
-- Likewise, the definition of the slice category found in
-- Cubical.Categories.Instances.Slice defines manual record types
-- to describe the objects and morphisms in the slice category
--
-- Although it is straightforward to define these data, it is
-- verbose and overly concrete. Instead, we can provide a
-- characterization of the slice category C / c as the total category
-- of the category of elements for C [-, c ]
-- C / c := ∫C (Element (C [-, c ])
--
-- With this definition of C / c, we may then give a description of
-- pullbacks as a derived notion. That is, pullbacks in C between
-- f : l → m and g : r → m correspond precisely to binary products in C / m
--
-- Because this description reuses existing definitons, there is really
-- no new work necessary for decsribing pullbacks. Instead, the PullbackNotation
-- module on C is really only re-exporting the interface of the BinProductNotation
-- module on C / c .
--
--
-- Given a morphism f : y → x, we may readily define a post-composition
-- functor PostComposeWithF : (C / y) → (C / x). The existence of pullbacks
-- further lets us describe a pointwise right adjoint to PostComposeWithF,
-- which can then be completed to a functor (C / x) → (C / x) via
-- functor comprehension, which we call ChangeBase
--
-- PostComposeWithF ⊣ ChangeBase
--
-- Lastly, we construct natural transformations that characterize
-- functoriality for ChangeBase
-- - Id ⇒ ChangeBase id
-- - ChangeBase f ∘F ChangeBase g ⇒ ChangeBase (f ⋆ g)
module Cubical.Categories.Limits.Pullback.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf
open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓ ℓ' : Level

open Functor
open Iso
open PshHom
open PshIso
open NatTrans

module _ (C : Category ℓ ℓ') where
  private
    module C = Category C

  module _ (m : C.ob) where
    Sliceᴰ : Categoryᴰ C _ _
    Sliceᴰ = Element (C [-, m ])

    Slice : Category _ _
    Slice = ∫C Sliceᴰ

    _/_ : Category _ _
    _/_ = Slice

  module _ {m : C.ob} where
    module _ {l r} (f : C [ l , m ]) (g : C [ r , m ]) where
      Pullback : Type _
      Pullback = BinProduct (Slice m) ((l , f) , (r , g))

  Pullbacks : Type _
  Pullbacks = ∀ {l m r} (f : C [ l , m ]) (g : C [ r , m ]) → Pullback f g

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C

  module PullbackNotation {l m r : C.ob} {f : C [ l , m ]} {g : C [ r , m ]}
     (pb : Pullback C f g) where
     private
       module bp = BinProductNotation pb

     vert = bp.vert .fst

     pbπ : C [ vert , m ]
     pbπ = bp.vert .snd

     pbπ₁ : C [ vert , l ]
     pbπ₁ = bp.π₁ .fst

     pbπ₂ : C [ vert , r ]
     pbπ₂ = bp.π₂ .fst

     opaque
       pbCommutes : pbπ₁ C.⋆ f ≡ pbπ₂ C.⋆ g
       pbCommutes = bp.π₁ .snd ∙ sym (bp.π₂ .snd)

     opaque
       pbIntro : ∀ {Γ} →
         (f' : C [ Γ , l ]) → (g' : C [ Γ , r ]) →
         f' C.⋆ f ≡ g' C.⋆ g → C [ Γ , vert ]
       pbIntro f' g' e = ((f' , e) bp.,p (g' , refl)) .fst

     opaque
       unfolding pbIntro
       pbβ₁ : ∀ {Γ} {f' : C [ Γ , l ]} {g' : C [ Γ , r ]} {e : f' C.⋆ f ≡ g' C.⋆ g}
         → pbIntro f' g' e C.⋆ pbπ₁ ≡ f'
       pbβ₁ = cong fst bp.×β₁

       pbβ₂ : ∀ {Γ} {f' : C [ Γ , l ]} {g' : C [ Γ , r ]} {e : f' C.⋆ f ≡ g' C.⋆ g}
         → pbIntro f' g' e C.⋆ pbπ₂ ≡ g'
       pbβ₂ = cong fst bp.×β₂

       pbIntro≡ : ∀ {Γ} {f' : C [ Γ , l ]} {g' : C [ Γ , r ]}
         {e : f' C.⋆ f ≡ g' C.⋆ g} {h : C [ Γ , vert ]}
         → f' ≡ h C.⋆ pbπ₁
         → g' ≡ h C.⋆ pbπ₂
         → pbIntro f' g' e ≡ h
       pbIntro≡ {e = e} {h = h} p q =
         cong fst (bp.,p≡ {g = h ,
           C.⟨ refl ⟩⋆⟨ sym $ bp.π₁ .snd ⟩
           ∙ sym (C.⋆Assoc _ _ _)
           ∙ C.⟨ sym p ⟩⋆⟨ refl ⟩
           ∙ e}
           (ΣPathP (p , toPathP (C.isSetHom _ _ _ _)))
           (ΣPathP (q , toPathP (C.isSetHom _ _ _ _))))

       pbExtensionality : ∀ {Γ} {h k : C [ Γ , vert ]}
         → h C.⋆ pbπ₁ ≡ k C.⋆ pbπ₁
         → h C.⋆ pbπ₂ ≡ k C.⋆ pbπ₂
         → h ≡ k
       pbExtensionality {h = h} {k = k} p q =
         cong fst (bp.,p-extensionality {_} {h , refl}
           {k , C.⟨ refl ⟩⋆⟨ sym (bp.π₁ .snd) ⟩
              ∙ sym (C.⋆Assoc _ _ _)
              ∙ C.⟨ sym p ⟩⋆⟨ refl ⟩
              ∙ C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ bp.π₁ .snd ⟩}
           (ΣPathP (p , toPathP (C.isSetHom _ _ _ _)))
           (ΣPathP (q , toPathP (C.isSetHom _ _ _ _))))

  module PullbacksNotation (pbs : Pullbacks C) where
    module pb {l m r} {f : C [ l , m ]} {g : C [ r , m ]} =
      PullbackNotation (pbs f g)
    open pb public

module _ {ℓC ℓC'} (C : Category ℓC ℓC') (pb : Pullbacks C) {x y} (f : C [ y , x ]) where
  private
    module C = Category C
    module pb {z} {g} = PullbackNotation {r = z} {f = f} {g = g} (pb f g)
  PostComposeWithF : Functor (C / y) (C / x)
  PostComposeWithF .F-ob g = _ , (g .snd C.⋆ f)
  PostComposeWithF .F-hom (h , h≡) = h , (sym (C.⋆Assoc _ _ _) ∙ cong (C._⋆ f) h≡)
  PostComposeWithF .F-id = Σ≡Prop (λ _ → C.isSetHom _ _) refl
  PostComposeWithF .F-seq u v = Σ≡Prop (λ _ → C.isSetHom _ _) refl

  ChangeBase : Functor (C / x) (C / y)
  ChangeBase = FunctorComprehension (RightAdjointProf PostComposeWithF) ues
    where
    open UniversalElement
    open PullbacksNotation pb
    ues : UniversalElements (RightAdjointProf PostComposeWithF)
    ues (z , g) .vertex = vert {f = f} {g = g} , pbπ₁
    ues (z , g) .element = pbπ₂ , (sym $ pbCommutes {f = f} {g = g})
    ues (z , g) .universal (w , h) = isIsoToIsEquiv (
      (λ (ϕ , ϕ≡) → pbIntro h ϕ (sym ϕ≡) , pbβ₁) ,
      (λ (ϕ , ϕ≡) → Σ≡Prop (λ _ → C.isSetHom _ _) pbβ₂) ,
      (λ (ϕ , ϕ≡) → Σ≡Prop (λ _ → C.isSetHom _ _) (pbIntro≡ (sym ϕ≡) refl)))

module _ {ℓC ℓC'} (C : Category ℓC ℓC') (pb : Pullbacks C)  where
  private
    module C = Category C
  module _ {x : C.ob} where
    private
      module pbId {r : C.ob} {g : C [ r , x ]} =
        PullbackNotation {r = r} {f = C.id {x}} {g = g} (pb (C.id {x}) g)

    ChangeBaseId : NatTrans (Id {C = C / x}) (ChangeBase C pb (C.id {x}))
    ChangeBaseId .N-ob (a , α) =
      pbId.pbIntro α C.id (C.⋆IdR α ∙ sym (C.⋆IdL α)) , pbId.pbβ₁
    ChangeBaseId .N-hom {x = a , α} {y = b , β} (h , h≡) = ΣPathP
      ( pbId.pbExtensionality
          ( C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ pbId.pbβ₁ ⟩
          ∙ h≡
          ∙ sym pbId.pbβ₁
          ∙ C.⟨ refl ⟩⋆⟨ sym pbId.pbβ₁ ⟩
          ∙ sym (C.⋆Assoc _ _ _))
          ( C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ pbId.pbβ₂ ⟩
          ∙ C.⋆IdR _
          ∙ sym (C.⋆IdL _)
          ∙ C.⟨ sym pbId.pbβ₂ ⟩⋆⟨ refl ⟩
          ∙ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ sym pbId.pbβ₂ ⟩
          ∙ sym (C.⋆Assoc _ _ _))
      , isProp→PathP (λ _ → C.isSetHom _ _) _ _)

  module _ {x y z : C.ob} (f : C [ y , x ]) (g : C [ z , y ]) where
    private
      module pbf {r : C.ob} {α : C [ r , x ]} =
        PullbackNotation {r = r} {f = f} {g = α} (pb f α)
      module pbg {r : C.ob} {α : C [ r , y ]} =
        PullbackNotation {r = r} {f = g} {g = α} (pb g α)
      module pbgf {r : C.ob} {α : C [ r , x ]} =
        PullbackNotation {r = r} {f = g C.⋆ f} {g = α} (pb (g C.⋆ f) α)

    ChangeBaseComp :
      NatTrans (ChangeBase C pb g ∘F ChangeBase C pb f)
               (ChangeBase C pb (g C.⋆ f))
    ChangeBaseComp .N-ob (a , α) =
      pbgf.pbIntro pbg.pbπ₁ (pbg.pbπ₂ C.⋆ pbf.pbπ₂)
        ( sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ pbg.pbCommutes ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbf.pbCommutes ⟩
        ∙ sym (C.⋆Assoc _ _ _))
      , pbgf.pbβ₁
    ChangeBaseComp .N-hom {x = a , α} {y = b , β} (h , h≡) = ΣPathP
      ( pbgf.pbExtensionality
          ( C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ pbgf.pbβ₁ ⟩
          ∙ pbg.pbβ₁
          ∙ sym pbgf.pbβ₁
          ∙ C.⟨ refl ⟩⋆⟨ sym pbgf.pbβ₁ ⟩
          ∙ sym (C.⋆Assoc _ _ _))
          ( C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ pbgf.pbβ₂ ⟩
          ∙ sym (C.⋆Assoc _ _ _)
          ∙ C.⟨ pbg.pbβ₂ ⟩⋆⟨ refl ⟩
          ∙ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ pbf.pbβ₂ ⟩
          ∙ sym (C.⋆Assoc _ _ _)
          ∙ C.⟨ sym pbgf.pbβ₂ ⟩⋆⟨ refl ⟩
          ∙ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ sym pbgf.pbβ₂ ⟩
          ∙ sym (C.⋆Assoc _ _ _))
      , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
