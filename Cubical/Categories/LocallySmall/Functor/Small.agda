module Cubical.Categories.LocallySmall.Functor.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallF

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Unit as Unit
open import Cubical.Categories.LocallySmall.Instances.Weaken

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base


open Category
open Categoryᴰ
open SmallCategory
open Iso

-- This looks like a mix of a functor and a displayed functor, because...it is!
--
-- 1. This is equivalent to a functor from C to the fiber category Dᴰ.v[ d ], but without any reind
-- 2. This is equivalent to a functorᴰ from wk C to Dᴰ over Unit.rec d, but as a small type
record Functor
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  (d : Dob)
  : Type  (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (DHom-ℓᴰ d d) (Dobᴰ-ℓ d)))
  where
  no-eta-equality
  constructor functor
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ

  field
    F-ob : C.ob → Dobᴰ d
    F-hom : ∀ {x y} (f : C.Hom[ (liftω x) , (liftω y) ])
      → Dᴰ.Cⱽ.Hom[ liftω (F-ob x)  , liftω (F-ob y) ]
    F-id : ∀ {x} → F-hom C.id ≡ Dᴰ.idᴰ {xᴰ = liftω (F-ob x)}
    F-seq : ∀ {x y z} (f : C.Hom[ liftω x , liftω y ])(g : C.Hom[ liftω y , liftω z ])
      → F-hom (f C.⋆ g) Dᴰ.≡[ sym $ D.⋆IdL _ ] (F-hom f Dᴰ.⋆ᴰ F-hom g)

  -- A Functor is the exact data of a displayed functor over a constant functor
  -- d : 1 → D, except that it is a small type.
  asFunctorᴰ : Functorᴰ (Unit.rec d) (weaken C.cat) Dᴰ
  asFunctorᴰ = functorᴰ (mapω F-ob) F-hom (Dᴰ.≡in F-id) λ fᴰ gᴰ → Dᴰ.≡in (F-seq fᴰ gᴰ)


module _
  {C : SmallCategory ℓC ℓC'}
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  where
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ
  module _ {d d'} (f : D.Hom[ d , d' ]) (F : Functor C Dᴰ d) (F' : Functor C Dᴰ d') where
    private
      module F = Functor F
      module F' = Functor F'

    record NatTrans : Type (ℓ-max (ℓ-max ℓC ℓC') (DHom-ℓᴰ d d')) where
      no-eta-equality
      constructor natTrans
      field
        N-ob  : ∀ c → Dᴰ.Hom[ f ][ liftω (F.F-ob c) , liftω (F'.F-ob c) ]
        N-hom : ∀ {c c'} (g : C.Hom[ liftω c , liftω c' ])
          → (F.F-hom g Dᴰ.⋆ᴰ N-ob c')
              Dᴰ.≡[ D.⋆IdL f ∙ (sym $ D.⋆IdR f) ]
            (N-ob c Dᴰ.⋆ᴰ F'.F-hom g)
      ∫N-hom : ∀ {c c'} (g : C.Hom[ liftω c , liftω c' ])
          → (F.F-hom g Dᴰ.⋆ᴰ N-ob c') Dᴰ.∫≡ (N-ob c Dᴰ.⋆ᴰ F'.F-hom g)
      ∫N-hom g = Dᴰ.≡in $ N-hom g

    
    N-obTy : Type _
    N-obTy = ∀ c → Dᴰ.Hom[ f ][ liftω (F.F-ob c) , liftω (F'.F-ob c) ]

    isSetN-obTy : isSet (N-obTy)
    isSetN-obTy = isSetΠ (λ _ → Dᴰ.isSetHomᴰ)

    N-homTy : ∀ (N-ob : N-obTy) → Type _
    N-homTy N-ob = ∀ {c c'} (g : C.Hom[ liftω c , liftω c' ]) →
      (F.F-hom g Dᴰ.⋆ᴰ N-ob c')
        Dᴰ.≡[ D.⋆IdL f ∙ (sym $ D.⋆IdR f) ]
      (N-ob c Dᴰ.⋆ᴰ F'.F-hom g)

    isPropN-homTy : ∀ N-ob → isProp (N-homTy N-ob)
    isPropN-homTy N-ob = isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ _ _ → isSet→SquareP (λ _ _ → Dᴰ.isSetHomᴰ) _ _ _ _

    NatTransΣ = (Σ N-obTy N-homTy)

    NatTransIsoΣ : Iso NatTrans (Σ N-obTy N-homTy)
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote NatTrans)

    isSetNatTrans : isSet NatTrans
    isSetNatTrans = isSetIso NatTransIsoΣ
      (isSetΣSndProp isSetN-obTy isPropN-homTy)

  open NatTrans
  idTrans : ∀ {d} (F : Functor C Dᴰ d) → NatTrans D.id F F
  idTrans F = natTrans
    (λ c → Dᴰ.idᴰ)
    (λ g → Dᴰ.rectify-out $ Dᴰ.⋆IdR _ ∙ (sym $ Dᴰ.⋆IdL _))

  seqTrans : ∀ {d d' d''}{f : D.Hom[ d , d' ]}{g : D.Hom[ d' , d'' ]}
    {F : Functor C Dᴰ d}{G : Functor C Dᴰ d'}{H : Functor C Dᴰ d''}
    (α : NatTrans f F G)
    (β : NatTrans g G H)
    → NatTrans (f D.⋆ g) F H
  seqTrans {d} {d'} {d''} {f} {g} {F} {G} {H} α β = natTrans
    (λ c → α .N-ob c Dᴰ.⋆ᴰ β .N-ob c)
    λ h → Dᴰ.rectify-out $
      sym (Dᴰ.⋆Assoc _ _ _)
      ∙ Dᴰ.⟨ ∫N-hom α h ⟩⋆⟨⟩
      ∙ Dᴰ.⋆Assoc _ _ _
      ∙ Dᴰ.⟨⟩⋆⟨ ∫N-hom β h ⟩
      ∙ sym (Dᴰ.⋆Assoc _ _ _)

  -- TODO: private?
  opaque
    makeNatTransΣPathP : ∀ {d d'}{f f' : D.Hom[ d , d' ]}
      {F : Functor C Dᴰ d}{G : Functor C Dᴰ d'}
      (f≡f' : f ≡ f')
      (α : NatTransΣ f F G)
      (α' : NatTransΣ f' F G)
      → (∀ c → α .fst c Dᴰ.≡[ f≡f' ] α' .fst c)
      → PathP (λ i → NatTransΣ (f≡f' i) F G) α α'
    makeNatTransΣPathP {F = F}{G} f≡f' α α' α≡α' = ΣPathP ((funExt α≡α') ,
      isProp→PathP (λ i → isPropN-homTy (f≡f' i) F G (funExt α≡α' i)) (α .snd) (α' .snd))

    makeNatTransPathP : ∀ {d d'}{f f' : D.Hom[ d , d' ]}
      {F : Functor C Dᴰ d}{G : Functor C Dᴰ d'}
      (f≡f' : f ≡ f')
      (α : NatTrans f F G)
      (α' : NatTrans f' F G)
      → (∀ c → α .N-ob c Dᴰ.≡[ f≡f' ] α' .N-ob c)
      → PathP (λ i → NatTrans (f≡f' i) F G) α α'
    makeNatTransPathP {d} {d'} {f} {f'} {F} {G} f≡f' α α' α≡α' =
      -- works for any retract
      (sym $ NatTransIsoΣ f F G .leftInv α )
      ◁ congDep {b₁ = NatTransIsoΣ f F G .fun α} {b₂ = NatTransIsoΣ f' F G .fun α'}
        (λ f → NatTransIsoΣ f F G .inv) f≡f' (makeNatTransΣPathP {F = F}{G = G}
          f≡f'
          (NatTransIsoΣ f F G .fun α)
          (NatTransIsoΣ f' F G .fun α')
          α≡α')
      ▷ NatTransIsoΣ f' F G .leftInv α'

module _
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = Category D
    module Dᴰ = CategoryᴰNotation Dᴰ

  open Categoryᴰ
  FUNCTOR : SmallFibersCategoryᴰ D _ (Functor C Dᴰ) _
  FUNCTOR .Hom[_][_,_] f (liftω F) (liftω F') = NatTrans f F F'
  FUNCTOR .idᴰ = idTrans _
  FUNCTOR ._⋆ᴰ_ = seqTrans
  FUNCTOR .⋆IdLᴰ fᴰ = ΣPathP ((D.⋆IdL _) , (makeNatTransPathP _ _ _ λ c → Dᴰ.rectify-out $ Dᴰ.⋆IdL _))
  FUNCTOR .⋆IdRᴰ fᴰ = ΣPathP ((D.⋆IdR _) , (makeNatTransPathP _ _ _ λ c → Dᴰ.rectify-out $ Dᴰ.⋆IdR _))
  FUNCTOR .⋆Assocᴰ fᴰ gᴰ hᴰ = ΣPathP ((D.⋆Assoc _ _ _) , (makeNatTransPathP _ _ _ λ c → Dᴰ.rectify-out $ Dᴰ.⋆Assoc _ _ _))
  FUNCTOR .isSetHomᴰ = isSetNatTrans _ _ _

module _
  (B : SmallCategory ℓB ℓB')
  (C : SmallCategory ℓC ℓC')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  BIFUNCTOR : SmallFibersCategoryᴰ D _ (Functor B (FUNCTOR C Dᴰ)) _
  BIFUNCTOR = FUNCTOR B (FUNCTOR C Dᴰ)
