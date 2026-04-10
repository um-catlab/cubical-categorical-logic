{-# OPTIONS --lossy-unification #-}
-- A definition of pullbacks bootstapped using
-- products in the total category of slices
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
open import Cubical.Categories.Limits.BinProduct.More

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
    Slice : Categoryᴰ C _ _
    Slice = Element (C [-, m ])

  module _ {m : C.ob} where
    module _ {l r} (f : C [ l , m ]) (g : C [ r , m ]) where
      Pullback : Type _
      Pullback = BinProduct (∫C (Slice m)) ((l , f) , (r , g))

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
  ChangeBase : Functor (∫C (Slice C x)) (∫C (Slice C y))
  ChangeBase .Functor.F-ob (z , g) = _ , pb.pbπ₁ {g = g}
  ChangeBase .Functor.F-hom {x = a , α} {y = b , β} (h , h≡) =
    (pb.pbIntro pb.pbπ₁ (pb.pbπ₂ C.⋆ h)
      ((pb.pbCommutes ∙ C.⟨ refl ⟩⋆⟨ sym h≡ ⟩) ∙ sym (C.⋆Assoc _ _ _))) ,
    pb.pbβ₁
  ChangeBase .Functor.F-id =
    ΣPathP ((pb.pbIntro≡ (sym $ C.⋆IdL _) (C.⋆IdR _ ∙ (sym $ C.⋆IdL _))) ,
            (isProp→PathP (λ _ → C.isSetHom _ _) _ _))
  ChangeBase .Functor.F-seq _ _ =
    ΣPathP (pb.pbIntro≡
             (sym pb.pbβ₁ ∙ C.⟨ refl ⟩⋆⟨ sym pb.pbβ₁ ⟩ ∙ sym (C.⋆Assoc _ _ _))
             ((sym $ C.⋆Assoc _ _ _) ∙ C.⟨ sym pb.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
             ∙ C.⟨ refl ⟩⋆⟨ sym pb.pbβ₂ ⟩ ∙ sym (C.⋆Assoc _ _ _))
             ,
            (isProp→PathP (λ _ → C.isSetHom _ _) _ _))

module _ {ℓC ℓC'} (C : Category ℓC ℓC') (pb : Pullbacks C)  where
  private
    module C = Category C
  module _ {x : C.ob} where
    private
      module pbId {r : C.ob} {g : C [ r , x ]} =
        PullbackNotation {r = r} {f = C.id {x}} {g = g} (pb (C.id {x}) g)

    ChangeBaseId : NatTrans (Id {C = ∫C (Slice C x)}) (ChangeBase C pb (C.id {x}))
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
