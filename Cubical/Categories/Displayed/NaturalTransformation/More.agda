module Cubical.Categories.Displayed.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Functorᴰ
open NatTrans
open NatIso
open NatTransᴰ
open isIso
open isIsoᴰ



module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  record NatIsoᴰ {F : Functor C D}{G : Functor C D}
    (α : NatIso F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
    : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' ℓDᴰ')))) where
    private
      module Cᴰ = Fibers Cᴰ
      module Dᴰ = Fibers Dᴰ
    field
      transᴰ : NatTransᴰ (α .trans) Fᴰ Gᴰ
      nIsoᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isIsoᴰ Dᴰ (α .nIso x) (transᴰ .N-obᴰ xᴰ)

    sqRLᴰ :
      ∀ {x}{y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}{f}
      {fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]} →
      PathP
        (λ i →
          Dᴰ.Hom[ sqRL α {f = f} i ][
            Fᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ yᴰ ])
        (Fᴰ .F-homᴰ fᴰ)
        ((transᴰ .N-obᴰ xᴰ
        Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ)
        Dᴰ.⋆ᴰ nIsoᴰ yᴰ .isIsoᴰ.invᴰ)
    sqRLᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        (sym $ Dᴰ.⋆IdR _)
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.≡in (symP (nIsoᴰ _ .isIsoᴰ.retᴰ)) ⟩
        ∙ (sym $ Dᴰ.⋆Assoc _ _ _)
        ∙ Dᴰ.⟨ Dᴰ.≡in (transᴰ .N-homᴰ _) ⟩⋆⟨ refl ⟩

    sqLLᴰ :
      ∀ {x}{y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}{f}
      {fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]} →
      PathP
        (λ i →
          Dᴰ.Hom[ sqLL α {f = f} i ][ _ , _ ])
        (Gᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ nIsoᴰ yᴰ .isIsoᴰ.invᴰ)
        (nIsoᴰ xᴰ .isIsoᴰ.invᴰ Dᴰ.⋆ᴰ Fᴰ .F-homᴰ fᴰ)
    sqLLᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        (sym $ Dᴰ.⋆IdL _)
        ∙ Dᴰ.⟨ sym $ Dᴰ.≡in $ nIsoᴰ _ .isIsoᴰ.secᴰ ⟩⋆⟨ refl ⟩
        ∙ Dᴰ.⋆Assoc _ _ _
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym (Dᴰ.≡in sqRLᴰ ∙ Dᴰ.⋆Assoc _ _ _) ⟩

    sqLRᴰ :
      ∀ {x}{y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}{f}
      {fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]} →
      PathP
        (λ i →
          Dᴰ.Hom[ sqLR α {f = f} i ][ _ , _ ])
        (Gᴰ .F-homᴰ fᴰ)
        ((nIsoᴰ xᴰ .isIsoᴰ.invᴰ
        Dᴰ.⋆ᴰ Fᴰ .F-homᴰ fᴰ)
        Dᴰ.⋆ᴰ transᴰ .N-obᴰ yᴰ)
    sqLRᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        (sym $ Dᴰ.⋆IdR _)
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.≡in (symP (nIsoᴰ _ .isIsoᴰ.secᴰ)) ⟩
        ∙ (sym $ Dᴰ.⋆Assoc _ _ _)
        ∙ Dᴰ.⟨ Dᴰ.≡in sqLLᴰ ⟩⋆⟨ refl ⟩

  module _ {F : Functor C D}{G : Functor C D}
    (α : NatIso F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ) where
    open NatTrans
    open NatIsoᴰ
    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Fibers Dᴰ
    isosToNatIsoᴰ :
      (isoᴰs : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → CatIsoᴰ Dᴰ (NatIsoAt α x) (Fᴰ .F-obᴰ xᴰ) (Gᴰ .F-obᴰ xᴰ))
      → (∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}{f : C [ x , y ]}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])
          → (Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ isoᴰs yᴰ .fst) Dᴰ.∫≡ (isoᴰs xᴰ .fst Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ))
      → NatIsoᴰ α Fᴰ Gᴰ
    isosToNatIsoᴰ isoᴰs homᴰ .transᴰ .N-obᴰ = λ xᴰ → isoᴰs xᴰ .fst
    isosToNatIsoᴰ isoᴰs homᴰ .transᴰ .N-homᴰ fᴰ = Dᴰ.rectify $ Dᴰ.≡out $ homᴰ fᴰ
    isosToNatIsoᴰ isoᴰs homᴰ .nIsoᴰ xᴰ .invᴰ = isoᴰs xᴰ .snd .invᴰ
    isosToNatIsoᴰ isoᴰs homᴰ .nIsoᴰ xᴰ .secᴰ = isoᴰs xᴰ .snd .secᴰ
    isosToNatIsoᴰ isoᴰs homᴰ .nIsoᴰ xᴰ .retᴰ = isoᴰs xᴰ .snd .retᴰ

    mkNatIsoPropHom : hasPropHoms Dᴰ
      → (∀ {x} xᴰ → Dᴰ.Hom[ α .trans ⟦ x ⟧ ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ])
      → (∀ {x} xᴰ → Dᴰ.Hom[ α .nIso x .inv ][ Gᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ xᴰ ])
      → NatIsoᴰ α Fᴰ Gᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .transᴰ .N-obᴰ = αᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .transᴰ .N-homᴰ {f = f} fᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.invᴰ = α⁻ᴰ xᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.secᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.retᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _

open NatIsoᴰ
module _
  {B : Category ℓB ℓB'}
  {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  {G H : Functor B C}
  {Gᴰ : Functorᴰ G Bᴰ Cᴰ}
  {Hᴰ : Functorᴰ H Bᴰ Cᴰ}
  where
  private
    module Bᴰ = Fibers Bᴰ
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    module D = Category D

  module _
    {α : NatTrans G H}
    (αᴰ : NatTransᴰ α Gᴰ Hᴰ) where
    _∘ʳᴰ_ : NatTransᴰ (F ∘ʳ α) (Fᴰ ∘Fᴰ Gᴰ) (Fᴰ ∘Fᴰ Hᴰ)
    _∘ʳᴰ_ .N-obᴰ bᴰ = Fᴰ .F-homᴰ (αᴰ .N-obᴰ bᴰ)
    _∘ʳᴰ_ .N-homᴰ {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP (Fᴰ .F-seqᴰ _ _))
        ∙ Dᴰ.≡in (congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .N-homᴰ fᴰ))
        ∙ Dᴰ.≡in (Fᴰ .F-seqᴰ _ _)

  module _
    {α : NatIso G H}
    (αᴰ : NatIsoᴰ α Gᴰ Hᴰ) where
    -- TODO there is already a nondispalyed ∘ʳⁱ in the library
    -- under ∘ʳi
    _∘ʳᴰⁱ_ : NatIsoᴰ (F ∘ʳⁱ α) (Fᴰ ∘Fᴰ Gᴰ) (Fᴰ ∘Fᴰ Hᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.transᴰ = _∘ʳᴰ_ (αᴰ .NatIsoᴰ.transᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.invᴰ =
      F-homᴰ Fᴰ (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.invᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.secᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP $ Fᴰ .F-seqᴰ _ _)
        ∙ (Dᴰ.≡in $ congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.secᴰ))
        ∙ (Dᴰ.≡in $ Fᴰ .F-idᴰ)
    _∘ʳᴰⁱ_ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.retᴰ =
      Dᴰ.rectify $ Dᴰ.≡out $
        Dᴰ.≡in (symP $ Fᴰ .F-seqᴰ _ _)
        ∙ (Dᴰ.≡in $ congP (λ _ → Fᴰ .F-homᴰ) (αᴰ .NatIsoᴰ.nIsoᴰ bᴰ .isIsoᴰ.retᴰ))
        ∙ (Dᴰ.≡in $ Fᴰ .F-idᴰ)

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  private
    module Dᴰ = Fibers Dᴰ

  idTransᴰ : NatTransᴰ (idTrans F) Fᴰ Fᴰ
  idTransᴰ .N-obᴰ _ =  Dᴰ.idᴰ
  idTransᴰ .N-homᴰ fᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $
      Dᴰ.⋆IdR _
      ∙ (sym $ Dᴰ.⋆IdL _)

  idNatIsoᴰ : NatIsoᴰ (idNatIso F) Fᴰ Fᴰ
  idNatIsoᴰ .NatIsoᴰ.transᴰ = idTransᴰ
  idNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ = Dᴰ.idᴰ
  idNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ =
    Dᴰ.⋆IdLᴰ (idNatIsoᴰ .NatIsoᴰ.transᴰ .N-obᴰ xᴰ)
  idNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ =
    Dᴰ.⋆IdLᴰ (idNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ)

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F G : Functor C D}
  {α : NatTrans F G}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  (αᴰ : NatTransᴰ α Fᴰ Gᴰ)
  where
  opNatTransᴰ : NatTransᴰ (opNatTrans α) (Gᴰ ^opFᴰ) (Fᴰ ^opFᴰ)
  opNatTransᴰ .N-obᴰ = αᴰ .N-obᴰ
  opNatTransᴰ .N-homᴰ fᴰ = symP (αᴰ .N-homᴰ fᴰ)

  ∫NT : NatTrans (∫F Fᴰ) (∫F Gᴰ)
  ∫NT .N-ob x = N-ob α (x .fst) , αᴰ .N-obᴰ (x .snd)
  ∫NT .N-hom (f , fᴰ) = ΣPathP ((N-hom α f) , (αᴰ .N-homᴰ fᴰ))

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F G : Functor C D}
  {α : NatIso F G}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
  (αᴰ : NatIsoᴰ α Fᴰ Gᴰ)
  where
  opNatIsoᴰ : NatIsoᴰ (opNatIso α) (Gᴰ ^opFᴰ) (Fᴰ ^opFᴰ)
  opNatIsoᴰ .NatIsoᴰ.transᴰ = opNatTransᴰ (αᴰ .NatIsoᴰ.transᴰ)
  opNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ =
    isisoᴰ (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ)
           (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ)
           (αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ)

  symNatIsoᴰ : NatIsoᴰ (symNatIso α) Gᴰ Fᴰ
  symNatIsoᴰ .NatIsoᴰ.transᴰ .N-obᴰ xᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ
  symNatIsoᴰ .NatIsoᴰ.transᴰ .N-homᴰ fᴰ = NatIsoᴰ.sqLLᴰ αᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.invᴰ =
    αᴰ .NatIsoᴰ.transᴰ .N-obᴰ xᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ
  symNatIsoᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.retᴰ =
    αᴰ .NatIsoᴰ.nIsoᴰ xᴰ .isIsoᴰ.secᴰ

module _
  {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {F : Functor B C} {G : Functor C D} {H : Functor D E}
  (Fᴰ : Functorᴰ F Bᴰ Cᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ) (Hᴰ : Functorᴰ H Dᴰ Eᴰ)
  where

  CATᴰ⋆Assoc :
    NatIsoᴰ
      (CAT⋆Assoc F G H)
      (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ))
      ((Hᴰ ∘Fᴰ Gᴰ) ∘Fᴰ Fᴰ)
  CATᴰ⋆Assoc .NatIsoᴰ.transᴰ .N-obᴰ = idTransᴰ ((Hᴰ ∘Fᴰ Gᴰ) ∘Fᴰ Fᴰ) .N-obᴰ
  CATᴰ⋆Assoc .NatIsoᴰ.transᴰ .N-homᴰ = idTransᴰ (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ)) .N-homᴰ
  CATᴰ⋆Assoc .NatIsoᴰ.nIsoᴰ = idNatIsoᴰ (Hᴰ ∘Fᴰ (Gᴰ ∘Fᴰ Fᴰ)) .NatIsoᴰ.nIsoᴰ

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  private
    module Dᴰ = Fibers Dᴰ

  _⋆NatTransᴰ_ : ∀ {F G H : Functor C D} →
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
    {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
    {Hᴰ : Functorᴰ H Cᴰ Dᴰ}
    {α : NatTrans F G}
    {β : NatTrans G H} →
    NatTransᴰ α Fᴰ Gᴰ → NatTransᴰ β Gᴰ Hᴰ → NatTransᴰ (α ⋆NatTrans β) Fᴰ Hᴰ
  _⋆NatTransᴰ_ = seqTransᴰ

  _⋆NatIsoᴰ_ : ∀ {F G H : Functor C D} →
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
    {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
    {Hᴰ : Functorᴰ H Cᴰ Dᴰ}
    {α : NatIso F G}
    {β : NatIso G H} →
    NatIsoᴰ α Fᴰ Gᴰ → NatIsoᴰ β Gᴰ Hᴰ → NatIsoᴰ (α ⋆NatIso β) Fᴰ Hᴰ
  (αᴰ ⋆NatIsoᴰ βᴰ) .transᴰ = αᴰ .transᴰ ⋆NatTransᴰ βᴰ .transᴰ
  (αᴰ ⋆NatIsoᴰ βᴰ) .nIsoᴰ xᴰ .invᴰ =
    (Dᴰ Categoryᴰ.⋆ᴰ βᴰ .nIsoᴰ xᴰ .invᴰ) (αᴰ .nIsoᴰ xᴰ .invᴰ)
  (αᴰ ⋆NatIsoᴰ βᴰ) .nIsoᴰ xᴰ .secᴰ =
   Dᴰ.rectify $ Dᴰ.≡out $
     Dᴰ.⋆Assoc _ _ _
     ∙ Dᴰ.⟨ refl ⟩⋆⟨ (sym $ Dᴰ.⋆Assoc _ _ _)
                      ∙ Dᴰ.⟨ Dᴰ.≡in $ αᴰ .nIsoᴰ xᴰ .secᴰ ⟩⋆⟨ refl ⟩
                      ∙ Dᴰ.⋆IdL _ ⟩
     ∙ (Dᴰ.≡in $ βᴰ .nIsoᴰ xᴰ .secᴰ)
  (αᴰ ⋆NatIsoᴰ βᴰ) .nIsoᴰ xᴰ .retᴰ =
   Dᴰ.rectify $ Dᴰ.≡out $
     (sym $ Dᴰ.⋆Assoc _ _ _)
     ∙ Dᴰ.⟨ Dᴰ.⋆Assoc _ _ _
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.≡in (βᴰ .nIsoᴰ xᴰ .retᴰ) ⟩
            ∙ Dᴰ.⋆IdR _ ⟩⋆⟨ refl ⟩
     ∙ (Dᴰ.≡in $ αᴰ .nIsoᴰ xᴰ .retᴰ)

  infixr 9 _⋆NatTransᴰ_
  infixr 9 _⋆NatIsoᴰ_

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {F : Functor C D}
  {G : Functor D E}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
  where

  private
    module Eᴰ = Fibers Eᴰ

  ∘Fᴰ-^opFᴰ-NatIsoᴰ :
    NatIsoᴰ (∘F-^opF-NatIso F G)
      ((Gᴰ ^opFᴰ) ∘Fᴰ (Fᴰ ^opFᴰ))
      ((Gᴰ ∘Fᴰ Fᴰ) ^opFᴰ)
  ∘Fᴰ-^opFᴰ-NatIsoᴰ .transᴰ .N-obᴰ xᴰ = Eᴰ.idᴰ
  ∘Fᴰ-^opFᴰ-NatIsoᴰ .transᴰ .N-homᴰ fᴰ =
    Eᴰ.rectify $ Eᴰ.≡out $
      Eᴰ.⋆IdL _ ∙ (sym $ Eᴰ.⋆IdR _)
  ∘Fᴰ-^opFᴰ-NatIsoᴰ .nIsoᴰ xᴰ .invᴰ = Eᴰ.idᴰ
  ∘Fᴰ-^opFᴰ-NatIsoᴰ .nIsoᴰ xᴰ .secᴰ = Eᴰ.⋆IdLᴰ (∘Fᴰ-^opFᴰ-NatIsoᴰ .nIsoᴰ xᴰ .invᴰ)
  ∘Fᴰ-^opFᴰ-NatIsoᴰ .nIsoᴰ xᴰ .retᴰ = Eᴰ.⋆IdLᴰ (∘Fᴰ-^opFᴰ-NatIsoᴰ .transᴰ .N-obᴰ xᴰ)
