{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.LocallySmall as LocallySmall
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ ℓRᴰ' : Level

open Bifunctorᴰ
open Functorᴰ

open isIsoOver

open PshHomᴰ
open PshHom
open PshIso

-- Product
module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  private
    module PshC = LocallySmallCategoryNotation (PRESHEAF C)
    module PshCᴰ = LocallySmallCategoryᴰNotation (PRESHEAFᴰ Cᴰ)
  module _ {P : Presheaf C ℓP}(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module P×ⱽQ = PresheafᴰNotation (Pᴰ ×ⱽPsh Qᴰ)
    ×ⱽ-Path :
      ∀ {x xᴰ}{p p' : P.p[ x ]}
        {pqᴰ : P×ⱽQ.p[ p ][ xᴰ ]}
        {pqᴰ' : P×ⱽQ.p[ p' ][ xᴰ ]}
      → Path Pᴰ.p[ _ ] (p , pqᴰ .fst) (p' , pqᴰ' .fst)
      → Path Qᴰ.p[ _ ] (p , pqᴰ .snd) (p' , pqᴰ' .snd)
      → Path P×ⱽQ.p[ _ ] (p , pqᴰ) (p' , pqᴰ')
    ×ⱽ-Path p≡p' q≡q' = ×≡Snd-hSet P.isSetPsh p≡p' q≡q'

  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    where
    ×ⱽ-π₁ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Pᴰ
    ×ⱽ-π₁ .N-obᴰ = fst
    ×ⱽ-π₁ .N-homᴰ = refl

    ×ⱽ-π₂ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Qᴰ
    ×ⱽ-π₂ .N-obᴰ = snd
    ×ⱽ-π₂ .N-homᴰ = refl
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
    where
    ×ⱽ-introᴰ : ∀ {α : PshHom P Q}
      → PshHomᴰ α Pᴰ Qᴰ
      → PshHomᴰ α Pᴰ Rᴰ
      → PshHomᴰ α Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introᴰ αᴰ βᴰ .N-obᴰ = λ z → αᴰ .N-obᴰ z , βᴰ .N-obᴰ z
    ×ⱽ-introᴰ αᴰ βᴰ .N-homᴰ = ×ⱽ-Path Qᴰ Rᴰ (αᴰ .N-homᴰ) (βᴰ .N-homᴰ)

    opaque
      ×ⱽ-β₁ : ∀ {α : PshHom P Q}
        → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
        → (βᴰ : PshHomᴰ α Pᴰ Rᴰ)
        → Path PshCᴰ.Hom[ _ , _ ] (_ , ×ⱽ-introᴰ αᴰ βᴰ ⋆PshHomᴰ ×ⱽ-π₁) (_ , αᴰ)
      ×ⱽ-β₁ αᴰ βᴰ = makePshHomᴰPath (PshC.⋆IdR _) (λ pᴰ → refl)

      ×ⱽ-β₂ : ∀ {α : PshHom P Q}
        → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
        → (βᴰ : PshHomᴰ α Pᴰ Rᴰ)
        → Path PshCᴰ.Hom[ _ , _ ] (_ , ×ⱽ-introᴰ αᴰ βᴰ ⋆PshHomᴰ ×ⱽ-π₂) (_ , βᴰ)
      ×ⱽ-β₂ αᴰ βᴰ = makePshHomᴰPath (PshC.⋆IdR _) (λ pᴰ → refl)

    ×ⱽPsh-UMP :
      IsoOver' {A = PshHom P Q}{B = PshHom P Q}
        -- TODO: abstract over this?
        (iso (λ α → α) (_⋆PshHom idPshHom) PshC.⋆IdR PshC.⋆IdR)
        (λ α → PshHomᴰ α Pᴰ Qᴰ × PshHomᴰ α Pᴰ Rᴰ)
        (λ α → PshHomᴰ α Pᴰ (Qᴰ ×ⱽPsh Rᴰ))
    ×ⱽPsh-UMP .IsoOver'.funᴰ α αᴰβᴰ = ×ⱽ-introᴰ (αᴰβᴰ .fst) (αᴰβᴰ .snd)
    ×ⱽPsh-UMP .IsoOver'.invᴰ α αᴰ = (αᴰ ⋆PshHomᴰ ×ⱽ-π₁) , (αᴰ ⋆PshHomᴰ ×ⱽ-π₂)
    ×ⱽPsh-UMP .IsoOver'.rightInvᴰ _ = makePshHomᴰPath (PshC.⋆IdR _) (λ pᴰ → refl)
    ×ⱽPsh-UMP .IsoOver'.leftInvᴰ _ = ×≡Snd-hSet (isSetPshHom P Q) (×ⱽ-β₁ _ _) (×ⱽ-β₂ _ _)

--   module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
--     where
--     ×ⱽ-introⱽ :
--       PshHomⱽ Pᴰ Qᴰ
--       → PshHomⱽ Pᴰ Rᴰ
--       → PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
--     ×ⱽ-introⱽ = ×ⱽ-introᴰ

--     ×ⱽPsh-UMPⱽ : Iso (PshHomⱽ Pᴰ Qᴰ × PshHomⱽ Pᴰ Rᴰ) (PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ))
--     ×ⱽPsh-UMPⱽ = ×ⱽPsh-UMPᴰ

  -- This is like PshProdⱽ .F-hom but for homomorphisms/isomorphisms
  -- between presheaves of different levels
  --
  -- TODO: get this by construction using LocallySmall stuff
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshHom P Q} where
      _×ⱽHom_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ α Pᴰ' Qᴰ')
        → PshHomᴰ (idPshHom {P = P} ⋆PshHom α) (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽHom βᴰ) = ×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomᴰ αᴰ) (×ⱽ-π₂ ⋆PshHomᴰ βᴰ)
    module _ {α α' : PshHom P Q} where
      opaque
        ⟨_⟩×ⱽHom⟨_⟩ : {αᴰ : PshHomᴰ α Pᴰ Qᴰ}{αᴰ' : PshHomᴰ α' Pᴰ Qᴰ}{βᴰ : PshHomᴰ α Pᴰ' Qᴰ'}{βᴰ' : PshHomᴰ α' Pᴰ' Qᴰ'}
          (αᴰ≡αᴰ' : Path PshCᴰ.Hom[ _ , _ ] (_ , αᴰ) (_ , αᴰ'))
          (βᴰ≡βᴰ' : Path PshCᴰ.Hom[ _ , _ ] (_ , βᴰ) (_ , βᴰ'))
          → Path PshCᴰ.Hom[ _ , _ ] (_ , αᴰ ×ⱽHom βᴰ) (_ , αᴰ' ×ⱽHom βᴰ')
        ⟨ αᴰ≡αᴰ' ⟩×ⱽHom⟨ βᴰ≡βᴰ' ⟩ = makePshHomᴰPath PshC.⟨⟩⋆⟨ cong fst αᴰ≡αᴰ' ⟩
          λ {p = p} pᴰ → ×≡Snd-hSet (Q .Functor.F-ob _ .snd)
            (λ i → (αᴰ≡αᴰ' i .fst .N-ob _ p) , αᴰ≡αᴰ' i .snd .N-obᴰ (pᴰ .fst))
            (λ i → (βᴰ≡βᴰ' i .fst .N-ob _ p) , βᴰ≡βᴰ' i .snd .N-obᴰ (pᴰ .snd))

  module _ {P : Presheaf C ℓP}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    where
    opaque
      ×ⱽHom-F-id : Path PshCᴰ.Hom[ _ , _ ]
        (_ , (PshCᴰ.idᴰ ×ⱽHom PshCᴰ.idᴰ))
        (_ , PshCᴰ.idᴰ {xᴰ = _ , liftω (Pᴰ ×ⱽPsh Pᴰ')})
      ×ⱽHom-F-id = IsoOver'.inv-inj ×ⱽPsh-UMP $ ×≡Snd-hSet (isSetPshHom _ _)
        (×ⱽ-β₁ (×ⱽ-π₁ ⋆PshHomᴰ PshCᴰ.idᴰ) (×ⱽ-π₂ ⋆PshHomᴰ PshCᴰ.idᴰ) ∙ PshCᴰ.⋆IdR _ ∙ sym (PshCᴰ.⋆IdL _))
        (×ⱽ-β₂ (×ⱽ-π₁ ⋆PshHomᴰ PshCᴰ.idᴰ) (×ⱽ-π₂ ⋆PshHomᴰ PshCᴰ.idᴰ) ∙ PshCᴰ.⋆IdR _ ∙ sym (PshCᴰ.⋆IdL _))

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
    {Rᴰ' : Presheafᴰ R Cᴰ ℓRᴰ'}
    where
      opaque
        ×ⱽHom-F-seq : ∀ {α β}
          ((αᴰ , αᴰ') : PshHomᴰ α Pᴰ Qᴰ × PshHomᴰ α Pᴰ' Qᴰ')
          ((βᴰ , βᴰ') : PshHomᴰ β Qᴰ Rᴰ × PshHomᴰ β Qᴰ' Rᴰ')
          → Path PshCᴰ.Hom[ _ , _ ]
              (_ , ((αᴰ PshCᴰ.⋆ᴰ βᴰ) ×ⱽHom (αᴰ' PshCᴰ.⋆ᴰ βᴰ')))
              (_ , ((αᴰ ×ⱽHom αᴰ') PshCᴰ.⋆ᴰ (βᴰ ×ⱽHom βᴰ')))
        ×ⱽHom-F-seq (αᴰ , αᴰ') (βᴰ , βᴰ') = IsoOver'.inv-inj ×ⱽPsh-UMP $
          ×≡Snd-hSet (isSetPshHom _ _)
            (×ⱽ-β₁ (×ⱽ-π₁ ⋆PshHomᴰ αᴰ PshCᴰ.⋆ᴰ βᴰ) (×ⱽ-π₂ ⋆PshHomᴰ αᴰ' PshCᴰ.⋆ᴰ βᴰ')
            ∙ sym (PshCᴰ.⋆Assoc _ _ _)
            ∙ PshCᴰ.⟨ sym $ ×ⱽ-β₁ _ _ ⟩⋆⟨⟩
            ∙ PshCᴰ.⋆Assoc _ _ _
            ∙ PshCᴰ.⟨⟩⋆⟨ sym $ ×ⱽ-β₁ _ _ ⟩
            ∙ sym (PshCᴰ.⋆Assoc ((idPshHom ⋆PshHom _) , (αᴰ ×ⱽHom αᴰ')) ((idPshHom ⋆PshHom _) , (βᴰ ×ⱽHom βᴰ')) (idPshHom , ×ⱽ-π₁)))
            ((×ⱽ-β₂ (×ⱽ-π₁ ⋆PshHomᴰ αᴰ PshCᴰ.⋆ᴰ βᴰ) (×ⱽ-π₂ ⋆PshHomᴰ αᴰ' PshCᴰ.⋆ᴰ βᴰ')
            ∙ sym (PshCᴰ.⋆Assoc _ _ _)
            ∙ PshCᴰ.⟨ sym $ ×ⱽ-β₂ _ _ ⟩⋆⟨⟩
            ∙ PshCᴰ.⋆Assoc _ _ _
            ∙ PshCᴰ.⟨⟩⋆⟨ sym $ ×ⱽ-β₂ _ _ ⟩
            ∙ sym (PshCᴰ.⋆Assoc ((idPshHom ⋆PshHom _) , (αᴰ ×ⱽHom αᴰ')) ((idPshHom ⋆PshHom _) , (βᴰ ×ⱽHom βᴰ')) (idPshHom , ×ⱽ-π₂))))
          -- (×ⱽ-β₁ (×ⱽ-π₁ ⋆PshHomᴰ αᴰ PshCᴰ.⋆ᴰ βᴰ) (×ⱽ-π₂ ⋆PshHomᴰ αᴰ' PshCᴰ.⋆ᴰ βᴰ')
          -- ∙ sym
          --   ((PshCᴰ.⋆Assoc (_ , αᴰ ×ⱽHom αᴰ') (_ , βᴰ ×ⱽHom βᴰ') (_ , ×ⱽ-π₁))
          --   ∙ ?))
          -- {!!}

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshCatIso P Q} where
      _×ⱽIso_ : (αᴰ : PshCatIsoᴰ α Pᴰ Qᴰ) (βᴰ : PshCatIsoᴰ α Pᴰ' Qᴰ')
        → PshCatIsoᴰ
            (PshC.subst-CatIso α (sym $ PshC.⋆IdL _) (sym $ PshC.⋆IdL _))
            (Pᴰ ×ⱽPsh Pᴰ')
            (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽIso βᴰ) .CatIsoᴰ.funᴰ = αᴰ .CatIsoᴰ.funᴰ ×ⱽHom βᴰ .CatIsoᴰ.funᴰ
      (αᴰ ×ⱽIso βᴰ) .CatIsoᴰ.invᴰ = αᴰ .CatIsoᴰ.invᴰ ×ⱽHom βᴰ .CatIsoᴰ.invᴰ
      (αᴰ ×ⱽIso βᴰ) .CatIsoᴰ.secᴰ =
        (_ , ((αᴰ .CatIsoᴰ.invᴰ ×ⱽHom βᴰ .CatIsoᴰ.invᴰ) PshCᴰ.⋆ᴰ (αᴰ .CatIsoᴰ.funᴰ ×ⱽHom βᴰ .CatIsoᴰ.funᴰ)))
          ≡⟨ sym (×ⱽHom-F-seq (αᴰ .CatIsoᴰ.invᴰ , βᴰ .CatIsoᴰ.invᴰ) (αᴰ .CatIsoᴰ.funᴰ , βᴰ .CatIsoᴰ.funᴰ)) ⟩
        (_ , ((αᴰ .CatIsoᴰ.invᴰ PshCᴰ.⋆ᴰ αᴰ .CatIsoᴰ.funᴰ) ×ⱽHom (βᴰ .CatIsoᴰ.invᴰ PshCᴰ.⋆ᴰ βᴰ .CatIsoᴰ.funᴰ)))
          ≡⟨ ⟨ αᴰ .CatIsoᴰ.secᴰ ⟩×ⱽHom⟨ βᴰ .CatIsoᴰ.secᴰ ⟩ ⟩
        (_ , (PshCᴰ.idᴰ ×ⱽHom PshCᴰ.idᴰ))
          ≡⟨ ×ⱽHom-F-id ⟩
        (_ , PshCᴰ.idᴰ) ∎
      (αᴰ ×ⱽIso βᴰ) .CatIsoᴰ.retᴰ =
        (_ , ((αᴰ .CatIsoᴰ.funᴰ ×ⱽHom βᴰ .CatIsoᴰ.funᴰ) PshCᴰ.⋆ᴰ (αᴰ .CatIsoᴰ.invᴰ ×ⱽHom βᴰ .CatIsoᴰ.invᴰ)))
          ≡⟨ sym (×ⱽHom-F-seq (αᴰ .CatIsoᴰ.funᴰ , βᴰ .CatIsoᴰ.funᴰ) (αᴰ .CatIsoᴰ.invᴰ , βᴰ .CatIsoᴰ.invᴰ)) ∙ ⟨ αᴰ .CatIsoᴰ.retᴰ ⟩×ⱽHom⟨ βᴰ .CatIsoᴰ.retᴰ ⟩ ∙ ×ⱽHom-F-id ⟩
        --   ≡⟨ sym (×ⱽHom-F-seq (αᴰ .CatIsoᴰ.funᴰ , βᴰ .CatIsoᴰ.funᴰ) (αᴰ .CatIsoᴰ.invᴰ , βᴰ .CatIsoᴰ.invᴰ)) ⟩
        -- (_ , ((αᴰ .CatIsoᴰ.funᴰ PshCᴰ.⋆ᴰ αᴰ .CatIsoᴰ.funᴰ) ×ⱽHom (βᴰ .CatIsoᴰ.invᴰ PshCᴰ.⋆ᴰ βᴰ .CatIsoᴰ.invᴰ)))
        --   ≡⟨ ⟨ αᴰ .CatIsoᴰ.retᴰ ⟩×ⱽHom⟨ βᴰ .CatIsoᴰ.retᴰ ⟩ ⟩
        -- (_ , (PshCᴰ.idᴰ ×ⱽHom PshCᴰ.idᴰ))
        --   ≡⟨ ×ⱽHom-F-id ⟩
        (_ , PshCᴰ.idᴰ) ∎

-- --   module _
-- --     {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
-- --     {P : Presheaf C ℓP}{R : Presheaf D ℓR}
-- --     {F : Functor D C}
-- --     {α : PshHet F R P}
-- --     {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Dᴰ ℓRᴰ}
-- --     (Fᴰ : Functorᴰ F Dᴰ Cᴰ)
-- --     where
-- --     ×ⱽ-introHet :
-- --       PshHetᴰ α Fᴰ Rᴰ Pᴰ
-- --       → PshHetᴰ α Fᴰ Rᴰ Qᴰ
-- --       → PshHetᴰ α Fᴰ Rᴰ (Pᴰ ×ⱽPsh Qᴰ)
-- --     ×ⱽ-introHet αᴰ βᴰ .N-obᴰ rᴰ = αᴰ .N-obᴰ rᴰ , βᴰ .N-obᴰ rᴰ
-- --     ×ⱽ-introHet αᴰ βᴰ .N-homᴰ = ΣPathP (αᴰ .N-homᴰ , βᴰ .N-homᴰ)

-- -- module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
-- --   {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
-- --   (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
-- --   where
-- --   private
-- --     module Pᴰ = PresheafᴰNotation Pᴰ
-- --     module Qᴰ = PresheafᴰNotation Qᴰ
-- --   PshProdⱽ≡ᴰ :
-- --     Pᴰ ×ᴰPsh Qᴰ ≡ reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ
-- --   PshProdⱽ≡ᴰ = Functorᴰ≡
-- --     (λ Aᴰ → funExt λ (p , q) → ΣPathPProp (λ _ → isPropIsSet) refl)
-- --     λ fᴰ → funExt λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP $
-- --       (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
-- --       , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _)

-- --   -- This one is only Eq.refl on objects, would need a corresponding eqToPshIsoⱽ' like reindF''
-- --   PshProdⱽ≅ᴰ :
-- --     PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
-- --   PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
-- --   PshProdⱽ≅ᴰ .fst .N-homᴰ =
-- --     ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
-- --            , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))
-- --   PshProdⱽ≅ᴰ .snd .inv _ x = x
-- --   PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
-- --   PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

-- -- module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
-- --   {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
-- --   {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
-- --   {α : PshHom P Q}
-- --   where
-- --   reind×ⱽIsoⱽ : PshIsoⱽ (reind α (Pᴰ ×ⱽPsh Qᴰ)) (reind α Pᴰ ×ⱽPsh reind α Qᴰ)
-- --   reind×ⱽIsoⱽ .fst = ×ⱽ-introⱽ (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₁)) (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₂))
-- --   reind×ⱽIsoⱽ .snd .inv p = invers .N-obᴰ
-- --     where
-- --       invers : PshHomⱽ (reind α Pᴰ ×ⱽPsh reind α Qᴰ) (reind α (Pᴰ ×ⱽPsh Qᴰ))
-- --       invers = reind-introⱽ (×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ reind-π) (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-π))
-- --   reind×ⱽIsoⱽ .snd .rightInv _ _ = refl
-- --   reind×ⱽIsoⱽ .snd .leftInv _ _ = refl

-- -- module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
-- --   {P : Presheaf D ℓP}
-- --   {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Dᴰ ℓQᴰ}
-- --   {F : Functor C D}
-- --   where
-- --   reindFunc×ⱽIsoⱽ' :
-- --     PshIsoᴰ (idPshIso {P = P} ∘ˡⁱ F ) (reindFunc F (Pᴰ ×ⱽPsh Qᴰ))
-- --               (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
-- --   reindFunc×ⱽIsoⱽ' .fst = ×ⱽ-introᴰ (×ⱽ-π₁ ∘ˡᴰ π Dᴰ F) (×ⱽ-π₂ ∘ˡᴰ π Dᴰ F)
-- --   reindFunc×ⱽIsoⱽ' .snd .inv p = invers .N-obᴰ
-- --     where
-- --       invers : PshHomⱽ (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ) (reindFunc F (Pᴰ ×ⱽPsh Qᴰ))
-- --       invers = ×ⱽ-introHet _ ×ⱽ-π₁ ×ⱽ-π₂
-- --   reindFunc×ⱽIsoⱽ' .snd .rightInv b q = refl
-- --   reindFunc×ⱽIsoⱽ' .snd .leftInv a p = refl

-- --   reindFunc×ⱽIsoⱽ :
-- --     PshIsoⱽ (reindFunc F (Pᴰ ×ⱽPsh Qᴰ))
-- --             (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
-- --   reindFunc×ⱽIsoⱽ .fst = PshHomEqPshHomᴰ (reindFunc×ⱽIsoⱽ' .fst) Eq.refl
-- --   reindFunc×ⱽIsoⱽ .snd = isisoover (λ a z → z) (λ _ _ → refl) λ _ _ → refl

-- -- module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
-- --   {x}
-- --   {F : Functor C D}
-- --   {Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ}{Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ}
-- --   where
-- --   reindⱽFunc×ⱽIsoⱽ :
-- --     PshIsoⱽ (reindⱽFunc F (Pᴰ ×ⱽPsh Qᴰ))
-- --             (reindⱽFunc F Pᴰ ×ⱽPsh reindⱽFunc F Qᴰ)
-- --   reindⱽFunc×ⱽIsoⱽ =
-- --     reindPshIsoⱽ {α = Functor→PshHet F x} reindFunc×ⱽIsoⱽ
-- --     ⋆PshIsoⱽ reind×ⱽIsoⱽ {Pᴰ = reindFunc F Pᴰ}{Qᴰ = reindFunc F Qᴰ}

-- -- open PshSection
-- -- open Section
-- -- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {F : GlobalSection Cᴰ} where
-- --   module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
-- --     (α : PshSection F Pᴰ)
-- --     (β : PshSection F Qᴰ)
-- --     where
-- --     ×ᴰ-introS : PshSection F (Pᴰ ×ᴰPsh Qᴰ)
-- --     ×ᴰ-introS .N-ob (p , q) = (α .N-ob p , β .N-ob q)
-- --     ×ᴰ-introS .N-hom _ _ = ΣPathP (α .N-hom _ _ , β .N-hom _ _)

-- --   module _
-- --     {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
-- --     ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
-- --     (α : PshSection F Pᴰ)
-- --     where
-- --     strictlyPreservesLocalRep : Type _
-- --     strictlyPreservesLocalRep = ∀ c
-- --       → strictlyPreservesUE F (×ᴰ-introS (Section→PshSection F c) α) (c ×P) (F .F-obᴰ c ×ᴰPᴰ)
