{-
   A variant of reindexing using J to avoid transport clutter.
-}
module Cubical.Categories.Displayed.Instances.Reindex.Eq.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.Conversion as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.TotalCategory
  hiding (introF; introS)
open import Cubical.Categories.Instances.TotalCategory as TotalCat
  hiding (intro)
import Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Magmoid

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

module _
  {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where

  private
    module C = Category C
    module R = HomᴰReasoning Cᴰ

    -- todo: generalize upstream somewhere to Data.Equality?
    isPropEqHom : ∀ {a b : C.ob} {f g : C [ a , b ]}
                → isProp (f Eq.≡ g)
    isPropEqHom {f = f}{g} =
      subst isProp (Eq.PathPathEq {x = f}{y = g}) (C.isSetHom f g)

  open Categoryᴰ Cᴰ

  reind' : {a b : C.ob} {f g : C [ a , b ]} (p : f Eq.≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → Hom[ f ][ aᴰ , bᴰ ] → Hom[ g ][ aᴰ , bᴰ ]
  reind' p = Eq.transport Hom[_][ _ , _ ] p

  reind≡reind' : ∀ {a b : C.ob} {f g : C [ a , b ]}
    {p : f ≡ g} {e : f Eq.≡ g}
    {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    → R.reind p fᴰ ≡ reind' e fᴰ
  reind≡reind' {p = p}{e} fᴰ =
    subst {x = Eq.pathToEq p}
      (λ e → R.reind p fᴰ ≡ reind' e fᴰ)
      (isPropEqHom _ _)
      lem
    where
    lem : R.reind p fᴰ ≡ reind' (Eq.pathToEq p) fᴰ
    lem = sym (Eq.eqToPath
      ((Eq.transportPathToEq→transportPath Hom[_][ _ , _ ]) p fᴰ))

module EqReindex
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (F : Functor C D)
  (F-id'  : {x : C .ob} → D .id {x = F .F-ob x} Eq.≡ F .F-hom (C .id))
  (F-seq' : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → (F .F-hom f) ⋆⟨ D ⟩ (F .F-hom g) Eq.≡ F .F-hom (f ⋆⟨ C ⟩ g))
  where

  private
    module R = HomᴰReasoning Dᴰ
    module C = Category C
    module D = Category D
    module Dᴰ = Categoryᴰ Dᴰ
    F*Dᴰ = Reindex.reindex Dᴰ F

    singId : singl {A = {x : C .ob} {p : Dᴰ .Categoryᴰ.ob[_] (F .F-ob x)} →
       Dᴰ .Categoryᴰ.Hom[_][_,_] {F .F-ob x} {F .F-ob x}
       (F .F-hom {x} {x} (C .id {x})) p p}
       (R.reind (λ i → F .F-id (~ i)) (Dᴰ.idᴰ))
    singId = (reind' Dᴰ F-id' Dᴰ.idᴰ ,
      implicitFunExt (λ {x} → implicitFunExt (λ {xᴰ} →
      reind≡reind' Dᴰ Dᴰ.idᴰ)))

    singSeq : singl
      {A = ∀ {x y z} {f : C .Hom[_,_] x y} {g : C .Hom[_,_] y z}{xᴰ}{yᴰ}{zᴰ}
       → Dᴰ.Hom[ F .F-hom f ][ xᴰ , yᴰ ]
       → Dᴰ.Hom[ F .F-hom g ][ yᴰ , zᴰ ]
       → Dᴰ.Hom[ F .F-hom (f C.⋆ g)][ xᴰ , zᴰ ]}
      (λ {x}{y}{z}{f}{g} fᴰ gᴰ → R.reind (sym (F .F-seq f g)) (fᴰ Dᴰ.⋆ᴰ gᴰ))
    singSeq = (λ fᴰ gᴰ → reind' Dᴰ (F-seq' _ _) (Dᴰ._⋆ᴰ_ fᴰ gᴰ)) ,
      implicitFunExt (λ {x} → implicitFunExt (λ {y} → implicitFunExt (λ {z} →
      implicitFunExt (λ {f} → implicitFunExt (λ {g} → implicitFunExt (λ {xᴰ} →
      implicitFunExt (λ {yᴰ} → implicitFunExt (λ {zᴰ} →
      funExt (λ fᴰ → funExt λ gᴰ → reind≡reind' Dᴰ (fᴰ Dᴰ.⋆ᴰ gᴰ))))))))))

  -- This definition is preferable to reindex when F-id' and F-seq'
  -- are given by Eq.refl.
  reindex : Categoryᴰ C ℓDᴰ ℓDᴰ'
  reindex = redefine-id⋆ F*Dᴰ singId singSeq

  hasPropHomsReindex : hasPropHoms Dᴰ → hasPropHoms reindex
  hasPropHomsReindex = λ z {c} {c'} f → z (F-hom F f)

  open Functorᴰ
  -- There's probably an easier way to do this using sing'
  forgetReindex : Functorᴰ F reindex Dᴰ
  forgetReindex .F-obᴰ = λ z → z
  forgetReindex .F-homᴰ = λ z → z
  forgetReindex .F-idᴰ {x}{xᴰ} =
    subst (λ F-id' → PathP (λ i → Dᴰ.Hom[ F .F-id i ][ xᴰ , xᴰ ])
      F-id'
      Dᴰ.idᴰ)
      (λ i → singId .snd i)
      (symP (R.≡out (R.reind-filler (sym (F .F-id)) _)))
  forgetReindex .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ =
    subst
      {A = ∀ {x y z} {f : C .Hom[_,_] x y} {g : C .Hom[_,_] y z}{xᴰ}{yᴰ}{zᴰ}
       → Dᴰ.Hom[ F .F-hom f ][ xᴰ , yᴰ ]
       → Dᴰ.Hom[ F .F-hom g ][ yᴰ , zᴰ ]
       → Dᴰ.Hom[ F .F-hom (f C.⋆ g)][ xᴰ , zᴰ ]}
      (λ F-seq' →  PathP (λ i → Dᴰ.Hom[ F .F-seq f g i ][ xᴰ , zᴰ ])
       (F-seq' fᴰ gᴰ) (fᴰ Dᴰ.⋆ᴰ gᴰ))
      (λ i → singSeq .snd i)
      (symP (R.≡out (R.reind-filler (sym (F .F-seq f g)) _)))

   -- TODO: it would be really nice to have a macro reindexRefl! that
   -- worked like the following: See
   -- Cubical.Categories.Instances.Quotient.More for an example
   -- reindexRefl! Cᴰ F = reindex' Cᴰ F Eq.refl (λ _ _ → Eq.refl)

  module _ {B : Category ℓB ℓB'}
           (G : Functor B C)
           (FGᴰ : Section (F ∘F G) Dᴰ)
           where
    introS : Section G reindex
    introS = redefine-id⋆S F*Dᴰ singId singSeq (Reindex.introS _ FGᴰ)

  open Functorᴰ

  module _ {B : Category ℓB ℓB'}{Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
           (G : Functor B C)
           (FGᴰ : Functorᴰ (F ∘F G) Bᴰ Dᴰ)
           where
    introF : Functorᴰ G Bᴰ reindex
    introF = TotalCat.recᴰ _ _ (introS _
      (reindS' (Eq.refl , Eq.refl) (TotalCat.elim FGᴰ)))
