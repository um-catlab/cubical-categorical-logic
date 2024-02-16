{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Terminal

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  open Category
  weaken : Categoryᴰ C ℓD ℓD'
  weaken .ob[_] x = D .ob
  weaken .Hom[_][_,_] f d d' = D [ d , d' ]
  weaken .idᴰ = D .id
  weaken ._⋆ᴰ_ = D ._⋆_
  weaken .⋆IdLᴰ = D .⋆IdL
  weaken .⋆IdRᴰ = D .⋆IdR
  weaken .⋆Assocᴰ = D .⋆Assoc
  weaken .isSetHomᴰ = D .isSetHom

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ

  Fst : Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

  -- Snd : Functorᴰ Fst {!weaken!} {!!}
  -- Snd = {!!}

  module _ {D : Category ℓD ℓD'}
           (F : Functor D C)
           (Fᴰ : Functorᴰ F (Unitᴰ D) Cᴰ)
           where
    mk∫Functor : Functor D (∫C Cᴰ)
    mk∫Functor .F-ob d = F ⟅ d ⟆ , Fᴰ .F-obᴰ _
    mk∫Functor .F-hom f = (F ⟪ f ⟫) , (Fᴰ .F-homᴰ _)
    mk∫Functor .F-id = ΣPathP (F .F-id , Fᴰ .F-idᴰ)
    mk∫Functor .F-seq f g = ΣPathP (F .F-seq f g , Fᴰ .F-seqᴰ _ _)

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where

  open Functorᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  Fstᴰ : Functorᴰ Id (∫Cᴰ Cᴰ Dᴰ) Cᴰ
  Fstᴰ .F-obᴰ = fst
  Fstᴰ .F-homᴰ = fst
  Fstᴰ .F-idᴰ = refl
  Fstᴰ .F-seqᴰ _ _ = refl

  module _ {E : Category ℓE ℓE'} (F : Functor E C)
           {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
           (Fᴰ : Functorᴰ F Eᴰ Cᴰ)
           (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Dᴰ)
           where

    mk∫ᴰFunctorᴰ : Functorᴰ F Eᴰ (∫Cᴰ Cᴰ Dᴰ)
    mk∫ᴰFunctorᴰ .F-obᴰ xᴰ = Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ _
    mk∫ᴰFunctorᴰ .F-homᴰ fᴰ = (Fᴰ .F-homᴰ fᴰ) , (Gᴰ .F-homᴰ _)
    mk∫ᴰFunctorᴰ .F-idᴰ = ΣPathP (Fᴰ .F-idᴰ , Gᴰ .F-idᴰ)
    mk∫ᴰFunctorᴰ .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ .F-seqᴰ fᴰ gᴰ , Gᴰ .F-seqᴰ _ _)

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
  where
  open Category

  private
    module Cᴰ = Categoryᴰ Cᴰ

  -- s for "simple" because D is not dependent on C
  ∫Cᴰsr : Categoryᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫Cᴰsr .ob[_] c = Σ[ d ∈ D .ob ] Cᴰ.ob[ c , d ]
  ∫Cᴰsr .Hom[_][_,_] f (d , cᴰ) (d' , cᴰ') =
    Σ[ g ∈ D [ d , d' ] ] Cᴰ.Hom[ f , g ][ cᴰ , cᴰ' ]
  ∫Cᴰsr .idᴰ = (D .id) , Cᴰ.idᴰ
  ∫Cᴰsr ._⋆ᴰ_ (f , fᴰ) (g , gᴰ) = (f ⋆⟨ D ⟩ g) , (fᴰ Cᴰ.⋆ᴰ gᴰ)
  ∫Cᴰsr .⋆IdLᴰ (f , fᴰ) = ΣPathP (_ , Cᴰ.⋆IdLᴰ _)
  ∫Cᴰsr .⋆IdRᴰ _ = ΣPathP (_ , Cᴰ.⋆IdRᴰ _)
  ∫Cᴰsr .⋆Assocᴰ _ _ _ = ΣPathP (_ , Cᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰsr .isSetHomᴰ = isSetΣ (D .isSetHom) (λ _ → Cᴰ .isSetHomᴰ)

  Fstᴰsr : Functorᴰ Id ∫Cᴰsr (weaken C D)
  Fstᴰsr .Functorᴰ.F-obᴰ = fst
  Fstᴰsr .Functorᴰ.F-homᴰ = fst
  Fstᴰsr .Functorᴰ.F-idᴰ = refl
  Fstᴰsr .Functorᴰ.F-seqᴰ = λ fᴰ gᴰ → refl

  ∫Cᴰsl : Categoryᴰ D (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫Cᴰsl .ob[_] d = Σ[ c ∈ C .ob ] Cᴰ.ob[ c , d ]
  ∫Cᴰsl .Hom[_][_,_] g (c , cᴰ) (c' , cᴰ') =
    Σ[ f ∈ C [ c , c' ] ] Cᴰ.Hom[ f , g ][ cᴰ , cᴰ' ]
  ∫Cᴰsl .idᴰ = (C .id) , Cᴰ.idᴰ
  ∫Cᴰsl ._⋆ᴰ_ (f , fᴰ) (g , gᴰ) = (f ⋆⟨ C ⟩ g) , (fᴰ Cᴰ.⋆ᴰ gᴰ)
  ∫Cᴰsl .⋆IdLᴰ (f , fᴰ) = ΣPathP (_ , Cᴰ.⋆IdLᴰ _)
  ∫Cᴰsl .⋆IdRᴰ _ = ΣPathP (_ , Cᴰ.⋆IdRᴰ _)
  ∫Cᴰsl .⋆Assocᴰ _ _ _ = ΣPathP (_ , Cᴰ.⋆Assocᴰ _ _ _)
  ∫Cᴰsl .isSetHomᴰ = isSetΣ (C .isSetHom) (λ _ → Cᴰ .isSetHomᴰ)

  Fstᴰsl : Functorᴰ Id ∫Cᴰsl (weaken D C)
  Fstᴰsl .Functorᴰ.F-obᴰ = fst
  Fstᴰsl .Functorᴰ.F-homᴰ = fst
  Fstᴰsl .Functorᴰ.F-idᴰ = refl
  Fstᴰsl .Functorᴰ.F-seqᴰ = λ _ _ → refl

  -- TODO: mk∫ᴰsFunctor
  --
  module _
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
    (Fᴰ : Functorᴰ F Eᴰ (weaken C D))
    (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ)
    where

    open Functorᴰ

    mk∫ᴰsrFunctorᴰ : Functorᴰ F Eᴰ ∫Cᴰsr
    mk∫ᴰsrFunctorᴰ .F-obᴰ xᴰ = (Fᴰ .F-obᴰ xᴰ) , (Gᴰ .F-obᴰ _ )
    mk∫ᴰsrFunctorᴰ .F-homᴰ fᴰ = Fᴰ .F-homᴰ fᴰ , Gᴰ .F-homᴰ _
    mk∫ᴰsrFunctorᴰ .F-idᴰ = ΣPathP ((Fᴰ .F-idᴰ) , (Gᴰ .F-idᴰ))
    mk∫ᴰsrFunctorᴰ .F-seqᴰ fᴰ gᴰ =
      ΣPathP ((Fᴰ .F-seqᴰ fᴰ gᴰ) , (Gᴰ .F-seqᴰ _ _))

  Assocᴰsr : Functorᴰ (FstBP C D) Cᴰ ∫Cᴰsr
  Assocᴰsr = mk∫ᴰsrFunctorᴰ _ Π2 Π3 where
    open Functorᴰ
    Π2 : Functorᴰ (FstBP C D) Cᴰ (weaken C D)
    Π2 .F-obᴰ {x}        _ = x .snd
    Π2 .F-homᴰ {_}{_}{f} _ = f .snd
    Π2 .F-idᴰ       = refl
    Π2 .F-seqᴰ _ _  = refl

    Π3 : Functorᴰ (∫F Π2) (Unitᴰ (∫C Cᴰ)) Cᴰ
    Π3 .F-obᴰ {x}        _ = x .snd
    Π3 .F-homᴰ {_}{_}{f} _ = f .snd
    Π3 .F-idᴰ      = refl
    Π3 .F-seqᴰ _ _ = refl

  Assoc-sr⁻ : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)
  Assoc-sr⁻ = mk∫Functor Assc Assc' where
    open Functor
    open Functorᴰ
    -- Might want this at the top level
    Assc : Functor (∫C ∫Cᴰsr) (C ×C D)
    Assc .F-ob (c , (d , _)) = c , d
    Assc .F-hom (f , (g , _)) = f , g
    Assc .F-id = refl
    Assc .F-seq _ _ = refl

    Assc' : Functorᴰ Assc _ Cᴰ
    Assc' .F-obᴰ {x}        _ = x .snd .snd
    Assc' .F-homᴰ {_}{_}{f} _ = f .snd .snd
    Assc' .F-idᴰ = refl
    Assc' .F-seqᴰ _ _ = refl

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  open Categoryᴰ
  _^opᴰ : Categoryᴰ (C ^op) ℓCᴰ ℓCᴰ'
  _^opᴰ .ob[_] x = Cᴰ.ob[ x ]
  _^opᴰ .Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ yᴰ , xᴰ ]
  _^opᴰ .idᴰ = Cᴰ.idᴰ
  _^opᴰ ._⋆ᴰ_ fᴰ gᴰ = gᴰ Cᴰ.⋆ᴰ fᴰ
  _^opᴰ .⋆IdLᴰ = Cᴰ .⋆IdRᴰ
  _^opᴰ .⋆IdRᴰ = Cᴰ .⋆IdLᴰ
  _^opᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = symP (Cᴰ.⋆Assocᴰ _ _ _)
  _^opᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFᴰ : Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFᴰ .F-obᴰ = Fᴰ .F-obᴰ
  _^opFᴰ .F-homᴰ = Fᴰ .F-homᴰ
  _^opFᴰ .F-idᴰ = Fᴰ .F-idᴰ
  _^opFᴰ .F-seqᴰ fᴰ gᴰ = Fᴰ .F-seqᴰ gᴰ fᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D

  open Categoryᴰ Dᴰ
  open Functor F
  open Functorᴰ

  forgetReindex : Functorᴰ F (reindex Dᴰ F) Dᴰ
  forgetReindex .F-obᴰ = λ z → z
  forgetReindex .F-homᴰ = λ z → z
  forgetReindex .F-idᴰ = symP (transport-filler _ _)
  forgetReindex .F-seqᴰ fᴰ gᴰ = symP (transport-filler _ _)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ

  hasContrHoms : Type _
  hasContrHoms = ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
    → isContr Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasPropHoms : Type _
  hasPropHoms = ∀ {c c' : C .ob}(f : C [ c , c' ])(cᴰ : Cᴰ.ob[ c ])(cᴰ' : Cᴰ.ob[ c' ])
    → isProp Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasContrHoms→hasPropHoms : hasContrHoms → hasPropHoms
  hasContrHoms→hasPropHoms contrHoms = λ f cᴰ cᴰ' → isContr→isProp (contrHoms f cᴰ cᴰ')

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  mkFunctorᴰPropHoms : (propHoms : hasPropHoms Dᴰ)
                      → (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
                      → (F-homᴰ : {x y : C .ob} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
                        → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
                      → Functorᴰ F Cᴰ Dᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ = F-homᴰ
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ = isProp→PathP (λ i → propHoms _ _ _) _ _
  mkFunctorᴰPropHoms propHoms F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ _ _ = isProp→PathP (λ i → propHoms _ _ _) _ _

  mkFunctorᴰContrHoms : (contrHoms : hasContrHoms Dᴰ)
                      → (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
                      → Functorᴰ F Cᴰ Dᴰ
  mkFunctorᴰContrHoms contrHoms F-obᴰ =
    mkFunctorᴰPropHoms (hasContrHoms→hasPropHoms Dᴰ contrHoms) F-obᴰ
    λ _ → contrHoms _ _ _ .fst
