{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
import Cubical.Categories.Displayed.Fibration.Base as Fibration

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  record CartesianLift {x : C .ob} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) : Type
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    field
      p*Pᴰ : Cᴰ.ob[ x ]
      π : Pᴰ.p[ p ][ p*Pᴰ ]
      isCartesian : ∀ {z zᴰ}{g : C [ z , x ]} →
        isIso (λ (gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]) → gᴰ Pᴰ.⋆ᴰ π)

    opaque
      intro :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → Pᴰ.p[ g P.⋆ p ][ zᴰ ]
        → Cᴰ [ g ][ zᴰ , p*Pᴰ ]
      intro = isCartesian .fst
    opaque
      unfolding intro
      private
        intro⟨_⟩ :
          ∀ {z zᴰ}{g g' : C [ z , x ]}
          → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
          → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
          → (g , gpᴰ) ≡ (g' , gpᴰ')
          → (g , intro gpᴰ) ≡ (g' , intro gpᴰ')
        intro⟨ gp≡gp' ⟩ i .fst = gp≡gp' i .fst
        intro⟨ gp≡gp' ⟩ i .snd = intro $ gp≡gp' i .snd

      intro⟨_⟩⟨_⟩ :
        ∀ {z zᴰ}{g g' : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
        → g ≡ g'
        → Path Pᴰ.p[ _ ] (_ , gpᴰ) (_ , gpᴰ')
        → Path Cᴰ.Hom[ _ , _ ] (_ , intro gpᴰ) (_ , intro gpᴰ')
      intro⟨ g≡g' ⟩⟨ gpᴰ≡gpᴰ' ⟩ =
        intro⟨ ΣPathP (g≡g' , (Pᴰ.rectify $ Pᴰ.≡out $ gpᴰ≡gpᴰ')) ⟩

      β :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , (intro gpᴰ Pᴰ.⋆ᴰ π))
            (_ , gpᴰ)
      β = Pᴰ.≡in $ isCartesian .snd .fst _

      intro≡ :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , gpᴰ)
            (_ , (gᴰ Pᴰ.⋆ᴰ π))
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , intro gpᴰ)
            (_ , gᴰ)
      intro≡ gp≡gπ =
        intro⟨ refl ⟩⟨ gp≡gπ ⟩
        ∙ (Cᴰ.≡in (isCartesian .snd .snd _))

  -- Hypothesis:
  -- - By Yoneda, an element p : P.p[ x ] is equivalent to a α : PshHom (C [-, x ]) P
  -- - CartesianLift is a vertical universal element over reind α Pᴰ
  CartesianLift' : ∀ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  CartesianLift' p Pᴰ = UniversalElementⱽ Cᴰ _ (reindYo p Pᴰ)

  module _ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (cL : CartesianLift p Pᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module cL = CartesianLift cL
      module p*Pᴰ = PresheafⱽNotation (reindYo p Pᴰ)
    open UniversalElementⱽ
    CartesianLift→CartesianLift' : CartesianLift' p Pᴰ
    CartesianLift→CartesianLift' .vertexⱽ = cL.p*Pᴰ
    CartesianLift→CartesianLift' .elementⱽ = Cᴰ.idᴰ Pᴰ.⋆ᴰ cL.π
    CartesianLift→CartesianLift' .universalⱽ .fst = cL.isCartesian .fst
    CartesianLift→CartesianLift' .universalⱽ {y} {yᴰ} {f} .snd =
      subst
        motive
        (funExt (λ fᴰ → Pᴰ.rectify $ Pᴰ.≡out $
          Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.⋆IdL _ ⟩ ∙ Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _))
        (cL.isCartesian .snd)
      where
        motive : (Cᴰ [ f ][ yᴰ , cL.p*Pᴰ ] → Pᴰ.p[ f P.⋆ p ][ yᴰ ]) → Type _
        motive introⱽ = section introⱽ (cL.isCartesian .fst) × retract introⱽ (cL.isCartesian .fst)

  -- TODO: make this functorial
  -- i.e. an input displayed category over C whose objects are Σ[ c ] P.p[ c ] × Pᴰ

open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
         where
  private
    module P = PresheafNotation P
  isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ
  isFibration' = ∀ {x} (p : P.p[ x ]) → CartesianLift' p Pᴰ

  module isFibrationNotation (isFibPᴰ : isFibration) where
    module _ {x} (p : P.p[ x ]) where
      open CartesianLift (isFibPᴰ p) using (p*Pᴰ) public
    module _ {x} {p : P.p[ x ]} where
      open CartesianLift (isFibPᴰ p) hiding (p*Pᴰ) public

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  -- TODO: This definitional isomorphism seems to justify defining
  -- Fibration.CartesianLift as YoLift
  CatLift→YoLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → Fibration.CartesianLift Cᴰ yᴰ f
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
  CatLift→YoLift = λ z →
                        record
                        { p*Pᴰ = z .Fibration.CartesianLift.f*yᴰ
                        ; π = z .Fibration.CartesianLift.π
                        ; isCartesian = z .Fibration.CartesianLift.isCartesian
                        }

  YoLift→CatLift : ∀ {x y yᴰ}{f : C [ x , y ]}
    → CartesianLift f (Cᴰ [-][-, yᴰ ])
    → Fibration.CartesianLift Cᴰ yᴰ f
  YoLift→CatLift = λ z →
                        record
                        { f*yᴰ = z .CartesianLift.p*Pᴰ
                        ; π = z .CartesianLift.π
                        ; isCartesian = z .CartesianLift.isCartesian
                        }

  YoLift'→CatLift' : ∀ {x y yᴰ}{f : C [ x , y ]}
    → CartesianLift' f (Cᴰ [-][-, yᴰ ])
    → Fibration.CartesianLift' Cᴰ yᴰ f
  YoLift'→CatLift' = λ x → record
    { vertexⱽ = x .UniversalElementⱽ.vertexⱽ
    ; elementⱽ = x .UniversalElementⱽ.elementⱽ
    ; universalⱽ = x .UniversalElementⱽ.universalⱽ
    }

  YoFibrations : Type _
  YoFibrations = ∀ {y} (yᴰ : Cᴰ.ob[ y ]) → isFibration (Cᴰ [-][-, yᴰ ])

  isCatFibration→YoFibrations : Fibration.isFibration Cᴰ → YoFibrations
  isCatFibration→YoFibrations isFib yᴰ p = CatLift→YoLift $ isFib yᴰ p

  YoFibrations→isCatFibration : YoFibrations → Fibration.isFibration Cᴰ
  YoFibrations→isCatFibration YoLifts cᴰ' f = YoLift→CatLift $ YoLifts cᴰ' f

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  isCatFibration' : Type _
  isCatFibration' = ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isFibration' (Cᴰ [-][-, xᴰ ])

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration Qᴰ)
         where
  private
    module Cᴰ = Fibers Cᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module isFibQᴰ = isFibrationNotation Qᴰ isFibQᴰ
  isFibrationReind : isFibration (reind {P = P} α Qᴰ)
  isFibrationReind p .p*Pᴰ = isFibQᴰ.p*Pᴰ (α .fst _ p)
  isFibrationReind p .π = isFibQᴰ.π
  isFibrationReind p .isCartesian .fst qᴰ =
    isFibQᴰ.intro $ Qᴰ.reind (α .snd _ _ _ p) qᴰ
  isFibrationReind p .isCartesian .snd .fst qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      sym (Qᴰ.reind-filler _ _)
      ∙ isFibQᴰ.β
      ∙ (sym $ Qᴰ.reind-filler _ _)
  isFibrationReind p .isCartesian .snd .snd gᴰ =
    Cᴰ.rectify $ Cᴰ.≡out $ isFibQᴰ.intro≡ $ sym $
      Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  module _ {P : Presheaf D ℓP} (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ) (isFibPᴰ : isFibration Pᴰ) where
    isFibrationReindFunc
      : isFibration (reindFunc F Pᴰ)
    isFibrationReindFunc p .p*Pᴰ = p*Pᴰ (isFibPᴰ p)
    isFibrationReindFunc p .π = π (isFibPᴰ p)
    isFibrationReindFunc p .isCartesian = isCartesian (isFibPᴰ p)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q){Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  (isFibQᴰ : isFibration Qᴰ)
  where
  isFibrationReindHet : isFibration (reindHet α Qᴰ)
  isFibrationReindHet = isFibrationReind _ α (isFibrationReindFunc F Qᴰ isFibQᴰ)

-- If we use CartesianLift' and we don't worry about definitional
-- behavior being too nice, this can become very simple and conceptual

-- For example, in the following, we want to show that
-- isFib Qᴰ ⇒ isFib (reind α Qᴰ)
--
-- isFib Qᴰ means all reindYo q Qᴰ are representable.
-- isFib (reind α Qᴰ) means that all reindYo p (reind α Qᴰ).
-- but reindYo p (reind α Qᴰ) ≡ reindYo (α p) Qᴰ.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration' Qᴰ)
         where
  isFibration'Reind : isFibration' (reind {P = P} α Qᴰ)
  isFibration'Reind p = isFibQᴰ (α .fst _ p) ◁PshIsoⱽ invPshIsoⱽ (reindYo-seqIsoⱽ α Qᴰ p)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  -- This gives us a very interesting alternate proof of isFibrationReindex
  module _ (isFibDᴰ : Fibration.isFibration Dᴰ) where
    open Fibration.CartesianLift
    private
      module Dᴰ = Categoryᴰ Dᴰ

    isCatFibrationReindex : Fibration.isFibration (Reindex.reindex Dᴰ F)
    isCatFibrationReindex = YoFibrations→isCatFibration yF where
      module _  where
      yF' : ∀ {y} (yᴰ : Dᴰ.ob[ F ⟅ y ⟆ ])
        → isFibration (reindHet (Functor→PshHet F y) (Dᴰ [-][-, yᴰ ]))
      yF' yᴰ = isFibrationReindHet _ (isCatFibration→YoFibrations isFibDᴰ _)
      yF : YoFibrations
      yF yᴰ p .p*Pᴰ = yF' yᴰ p .p*Pᴰ
      yF yᴰ p .π = yF' yᴰ p .π
      yF yᴰ p .isCartesian = yF' yᴰ p .isCartesian

  isCatFibration'Reindex
    : isCatFibration' Dᴰ
    → isCatFibration' (Reindex.reindex Dᴰ F)
  isCatFibration'Reindex isFib xᴰ f =
    reindUEⱽ (isFib xᴰ (F ⟪ f ⟫)) ◁PshIsoⱽ
      (invPshIsoⱽ reindYoReindFunc
      ⋆PshIsoⱽ reindPshIsoⱽ reindⱽFuncRepr)

-- Reindexing a projectionlike endofunctor gives a displayed endofunctor
-- when cartesian lifts along the projection exists
-- TODO : Find the most general version of this
module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (F : Functor C C)
  (πF : NatTrans F Id)
  where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _
    (πF* : {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
      CartesianLift' (πF ⟦ Γ ⟧) (Cᴰ [-][-, Γᴰ ]))
    where

    open UniversalElementⱽ

    introπF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ Δᴰ , vertexᴰ (πF* Γᴰ) ]
    introπF* {Γᴰ = Γᴰ} γᴰ = introᴰ (πF* Γᴰ) γᴰ

    introπF*⟨_⟩⟨_⟩ :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ Δᴰ' : Cᴰ.ob[ Δ ]}{γ γ' : C [ Δ , F ⟅ Γ ⟆ ]} →
        {Δᴰ≡Δᴰ' : Δᴰ ≡ Δᴰ'} →
        (γ≡γ' : γ ≡ γ') →
        {γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ]} →
        {γᴰ' : Cᴰ [ γ' C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ' , Γᴰ ]} →
        γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ≡Δᴰ' i , Γᴰ ]) ] γᴰ' →
        introπF* γᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ≡Δᴰ' i , vertexⱽ (πF* Γᴰ) ]) ] introπF* γᴰ'
    introπF*⟨ γ≡γ' ⟩⟨ γᴰ≡γᴰ' ⟩ i = introπF* (γᴰ≡γᴰ' i)

    π-πF* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ [ πF ⟦ Γ ⟧ ][ vertexⱽ (πF* Γᴰ) , Γᴰ ]
    π-πF* Γᴰ = Cᴰ.reind (C.⋆IdL _) $ πF* Γᴰ .elementⱽ

    β-πF* :
      ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
        {Δ} {Δᴰ : Cᴰ.ob[ Δ ]}{γ : C [ Δ , F ⟅ Γ ⟆ ]}
      → (γᴰ : Cᴰ [ γ C.⋆ πF ⟦ Γ ⟧ ][ Δᴰ , Γᴰ ])
      → introπF* γᴰ Cᴰ.⋆ᴰ π-πF* Γᴰ ≡ γᴰ
    β-πF* {Γᴰ = Γᴰ} γᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.reind-filler _ _
        ∙ Cᴰ.≡in (βⱽ (πF* Γᴰ) {pᴰ = γᴰ})

    open NatTrans

    weakenπFᴰ : Functorᴰ F Cᴰ Cᴰ
    weakenπFᴰ .F-obᴰ Γᴰ = πF* Γᴰ .vertexⱽ
    weakenπFᴰ .F-homᴰ {f = γ} {xᴰ = Γᴰ} {yᴰ = Δᴰ} γᴰ =
      introπF* (Cᴰ.reind (sym $ πF .N-hom γ) $ (π-πF* Γᴰ Cᴰ.⋆ᴰ γᴰ))
    weakenπFᴰ .F-idᴰ {xᴰ = Γᴰ} =
        introπF*⟨ F .F-id  ⟩⟨
          Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⋆IdR _
            ∙ (sym $ Cᴰ.reind-filler _ _)
        ⟩
          ▷ (sym $ weak-ηⱽ (πF* Γᴰ))
    weakenπFᴰ .F-seqᴰ γᴰ δᴰ =
      introπF*⟨ F .F-seq _ _ ⟩⟨
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
               ∙ Cᴰ.reind-filler _ _
               ∙ (Cᴰ.≡in $ sym $ β-πF* (Cᴰ.reind (sym $ πF .N-hom _) (π-πF* _ Cᴰ.⋆ᴰ γᴰ)))
               ⟩⋆⟨ refl ⟩
          ∙ (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (πF* _))
