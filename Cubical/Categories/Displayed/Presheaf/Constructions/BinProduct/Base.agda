{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ :
    Functorᴰ PshProd' (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×Cᴰ PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                      (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ :
    Bifunctorᴰ PshProd (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ) (PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                       (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ

  _×ᴰPsh_ : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ)
            → Presheafᴰ (P ×Psh Q) Cᴰ _
  _×ᴰPsh_ = PshProdᴰ .Bif-obᴰ

  ∫×ᴰ≅× : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → {Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ}
        → PshIso (∫P (Pᴰ ×ᴰPsh Qᴰ)) (∫P Pᴰ ×Psh ∫P Qᴰ)
  ∫×ᴰ≅× .trans .N-ob _ ((p , q) , (pᴰ , qᴰ)) = (p , pᴰ) , (q , qᴰ)
  ∫×ᴰ≅× .trans .N-hom _ _ _ _ = refl
  ∫×ᴰ≅× .nIso _ .fst ((p , pᴰ) , (q , qᴰ)) = (p , q) , (pᴰ , qᴰ)
  ∫×ᴰ≅× .nIso _ .snd .fst _ = refl
  ∫×ᴰ≅× .nIso _ .snd .snd _ = refl

  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ :
    Functorⱽ (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ PRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  _×ⱽPsh_ : ∀ {P : Presheaf C ℓA}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓBᴰ)
            → Presheafᴰ P Cᴰ _
  Pᴰ ×ⱽPsh Qᴰ = PshProdⱽ .F-obᴰ (Pᴰ , Qᴰ)

  LocallyRepresentableᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Presheafᴰ P Cᴰ ℓPᴰ
    → Type _
  LocallyRepresentableᴰ (P , _×P) Pᴰ = ∀ {c} cᴰ → UniversalElementᴰ Cᴰ (c ×P) ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh Pᴰ)

  open UniversalElement
  ∫LocallyRepresentable :
    {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
    → ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
    → LocallyRepresentable (∫P Pᴰ)
  ∫LocallyRepresentable (Pᴰ , _×ᴰPᴰ) (Γ , Γᴰ) =
    UniversalElementᴰ.∫ue (Γᴰ ×ᴰPᴰ)
      ◁PshIso
      (∫×ᴰ≅× ⋆PshIso ×PshIso (TotalCatYoPshIso Cᴰ) idPshIso)

  LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    where module P = PresheafNotation P

  module LocallyRepresentableⱽNotation {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
    open UniversalElementⱽ

    ⌈_×ⱽ_*Pᴰ⌉ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
    ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ = vertexⱽ $ Γᴰ ×ⱽ p *Pᴰ

    introLR : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
      → Cᴰ [ γ ][ Δᴰ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    introLR {Γᴰ = Γᴰ}{p} γᴰ pᴰ = (introᴰ $ (Γᴰ ×ⱽ p *Pᴰ)) (γᴰ , pᴰ)

    introLR⟨_⟩⟨_⟩ : ∀
      {Γ}{Γᴰ}{p p' : P.p[ Γ ]}{p≡p'}
      {Δ}{Δᴰ Δᴰ'}{Δᴰ≡Δᴰ' : Δᴰ ≡ Δᴰ'}
      {γ γ' : C [ Δ , Γ ]}{γ≡γ'}
      {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ [ γ' ][ Δᴰ' , Γᴰ ]}
      {pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ]}
      {pᴰ' : Pᴰ.p[ γ' P.⋆ p' ][ Δᴰ' ]}
      → (γᴰ ≡[ cong₂ (Cᴰ [_][_, Γᴰ ]) γ≡γ' Δᴰ≡Δᴰ' ] γᴰ')
      → (pᴰ ≡[ cong₂ Pᴰ.p[_][_] P.⟨ γ≡γ' ⟩⋆⟨ p≡p' ⟩ Δᴰ≡Δᴰ' ] pᴰ')
      → introLR γᴰ pᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ≡Δᴰ' i , ⌈ Γᴰ ×ⱽ p≡p' i *Pᴰ⌉ ]) ] introLR γᴰ' pᴰ'
    introLR⟨ x ⟩⟨ x₁ ⟩ i = introLR (x i) (x₁ i)

    π₁LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ , Γᴰ ]
    π₁LR Γᴰ p = fst $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    π₂LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Pᴰ.p[ C.id P.⋆ p ][ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    π₂LR Γᴰ p = snd $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    opaque
      β₁LR : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
        {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → introLR γᴰ pᴰ Cᴰ.⋆ᴰⱽ π₁LR _ _ ≡ γᴰ
      β₁LR {_}{Γᴰ}{p} γᴰ pᴰ = Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ (Cᴰ.≡in $ λ i → βᴰ (Γᴰ ×ⱽ p *Pᴰ) {p = _ , γᴰ , pᴰ} i .snd .fst)

      β₂LR : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
        {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → (introLR γᴰ pᴰ Pᴰ.⋆ᴰ (Pᴰ.reind (P.⋆IdL _) $ π₂LR _ _)) ≡ pᴰ
      β₂LR {Γ} {Γᴰ} {p} {Δ} {Δᴰ} {γ} γᴰ pᴰ = Pᴰ.rectify $ Pᴰ.≡out $
        (Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
        ∙ Pᴰ.reind-filler _ _)
        ∙ (Pᴰ.≡in $ λ i → βᴰ (Γᴰ ×ⱽ p *Pᴰ) {p = _ , γᴰ , pᴰ} i .snd .snd)
    π₁LR_⟨_⟩ : ∀ {Γ} {p q : P.p[ Γ ]} Γᴰ → (p≡q : p ≡ q)
      → PathP (λ i → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p≡q i *Pᴰ⌉ , Γᴰ ])
          (π₁LR Γᴰ p)
          (π₁LR Γᴰ q)
    π₁LR Γᴰ ⟨ p≡q ⟩ i = π₁LR Γᴰ $ p≡q i

    π₂LR_⟨_⟩ : ∀ {Γ} {p q : P.p[ Γ ]} Γᴰ → (p≡q : p ≡ q)
      → PathP (λ i → Pᴰ.p[ C.id P.⋆ p≡q i ][ ⌈ Γᴰ ×ⱽ p≡q i *Pᴰ⌉ ])
          (π₂LR Γᴰ p)
          (π₂LR Γᴰ q)
    π₂LR Γᴰ ⟨ p≡q ⟩ i = π₂LR Γᴰ $ p≡q i

    funcLR : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ ⌈ Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    funcLR {p = p}{γ = γ} γᴰ =
      introLR (π₁LR _ (γ P.⋆ p) Cᴰ.⋆ⱽᴰ γᴰ) (Pᴰ.reind (P.⋆IdL _) $ (π₂LR _ (γ P.⋆ p)))

    funcLR-seq : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      {Θ}{Θᴰ}{δ : C [ Θ , Δ ]}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → PathP (λ i → Cᴰ [ δ C.⋆ γ ][ ⌈ Θᴰ ×ⱽ (P.⋆Assoc δ γ p i) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
          (funcLR {p = p} (δᴰ Cᴰ.⋆ᴰ γᴰ))
          (funcLR δᴰ Cᴰ.⋆ᴰ funcLR γᴰ)
    funcLR-seq {Γ} {Γᴰ} {p} {Δ} {Δᴰ} {γ} {Θ} {Θᴰ} {δ} γᴰ δᴰ =
      introLR⟨
        (λ i → π₁LR Θᴰ ⟨ P.⋆Assoc _ _ _ ⟩ i Cᴰ.⋆ⱽᴰ (δᴰ Cᴰ.⋆ᴰ γᴰ))
          ▷ (sym Cᴰ.⋆Assocⱽᴰᴰ
          ∙ (Cᴰ.≡out $ Cᴰ.⟨ Cᴰ.≡in (sym $ β₁LR _ _) ⟩⋆⟨ refl ⟩)
          ∙ (Cᴰ.⋆Assocᴰⱽᴰ))
      ⟩⟨
        -- solver?
        rectify
          ((congS₂ _∙_ refl (congS₂ _∙_ refl (sym $ congS₂Bifunct Pᴰ~ _ _ _ _) ∙ ((sym $ congS₂Bifunct Pᴰ~ _ _ _ _)))
          ∙ (sym $ congS₂Bifunct Pᴰ~ _ _ _ _))
          ∙ congS₂ (congS₂ Pᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))
        $
        compPathP (Pᴰ.≡out $ sym (Pᴰ.reind-filler _ _)) $
        compPathP (π₂LR Θᴰ ⟨ P.⋆Assoc _ _ _ ⟩) $
        compPathP ((Pᴰ.≡out $ Pᴰ.reind-filler _ _) ▷ (sym $ β₂LR _ _)) $
        (Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (Γᴰ ×ⱽ p *Pᴰ))
      where
        Pᴰ~ : P.p[ Θ ] → P.p[ Θ ] → Type _
        Pᴰ~ p p' = Pᴰ.p[ p ][ ⌈ Θᴰ ×ⱽ p' *Pᴰ⌉ ]

        Pᴰ~' : P.p[ Θ ] → P.p[ Θ ] → Type _
        Pᴰ~' p' p = Pᴰ~ p p'

    funcLR-id : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
      → PathP (λ i → Cᴰ [ C.id ][ ⌈ Γᴰ ×ⱽ P.⋆IdL p i *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
          (funcLR {Γᴰ = Γᴰ}{p = p} Cᴰ.idᴰ)
          Cᴰ.idᴰ
    funcLR-id {Γ}{Γᴰ}{p} =
      introLR⟨
        (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _)
        ◁ π₁LR _ ⟨ P.⋆IdL _ ⟩
        ⟩⟨
        rectify
          (sym (congS₂Bifunct Pᴰ~ _ _ _ _) ∙ (congS₂ (congS₂ Pᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _)))
          $
          compPathP (Pᴰ.≡out $ sym $ Pᴰ.reind-filler _ _) $
          π₂LR _ ⟨ P.⋆IdL p ⟩
        ⟩
      ▷ (sym $ weak-ηⱽ (Γᴰ ×ⱽ p *Pᴰ))
      where
        Pᴰ~ : (p : P.p[ Γ ])(p' : P.p[ Γ ]) → Type _
        Pᴰ~ p p' = Pᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p' *Pᴰ⌉ ]
