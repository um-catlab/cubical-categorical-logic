{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.LocalRepresentability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
import Cubical.Categories.Displayed.Constructions.Reindex.Base as ReindCatᴰ
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functor
open Functorᴰ
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} where
  LocallyRepresentableⱽPresheafᴰ
    : (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓPᴰ : Level) → Type _
  LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ =
    Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
    (α : PshHom P Q)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where
    reindLocallyRepresentableⱽ : LocallyRepresentableⱽ Qᴰ → LocallyRepresentableⱽ (reind α Qᴰ)
    reindLocallyRepresentableⱽ _×ⱽ_*Qᴰ Γᴰ p = (Γᴰ ×ⱽ (α .N-ob _ p) *Qᴰ) ◁PshIsoⱽ (idPshIsoᴰ ×ⱽIso invPshIsoⱽ (reindYo-seqIsoⱽ α Qᴰ p))

  reindLocallyRepresentableⱽPresheafᴰ : {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
    (α : PshHom Q P)
    → LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ
    → LocallyRepresentableⱽPresheafᴰ Q Cᴰ ℓPᴰ
  reindLocallyRepresentableⱽPresheafᴰ α Pᴰ = (reind α (Pᴰ .fst) , reindLocallyRepresentableⱽ α (Pᴰ .fst) (Pᴰ .snd))

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module LocallyRepresentableⱽAtNotation {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) {Γ}(Γᴰ : Cᴰ.ob[ Γ ])(p : ⟨ P .F-ob Γ ⟩)
    (Γᴰ×ⱽp*Pᴰ : UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)) where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ

    introLR : ∀
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
      → Cᴰ [ γ ][ Δᴰ , vertexⱽ Γᴰ×ⱽp*Pᴰ ]
    introLR γᴰ pᴰ = (introᴰ Γᴰ×ⱽp*Pᴰ) (γᴰ , pᴰ)

    π₁LR : Cᴰ.v[ Γ ] [ vertexⱽ (Γᴰ×ⱽp*Pᴰ) , Γᴰ ]
    π₁LR = fst $ elementⱽ Γᴰ×ⱽp*Pᴰ

    π₂LR : Pᴰ.p[ C.id P.⋆ p ][ vertexⱽ Γᴰ×ⱽp*Pᴰ ]
    π₂LR = snd $ elementⱽ $ Γᴰ×ⱽp*Pᴰ

    opaque
      β₁LR : ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , introLR γᴰ pᴰ Cᴰ.⋆ᴰ π₁LR)
            (_ ,  γᴰ)
      β₁LR γᴰ pᴰ = ≡×Snd (βᴰ Γᴰ×ⱽp*Pᴰ) .fst

      β₂LR : ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → Path Pᴰ.p[ _ , _ ]
            (_ , introLR γᴰ pᴰ Pᴰ.⋆ᴰ π₂LR)
            (_ , pᴰ)
      β₂LR γᴰ pᴰ =
        Pᴰ.reind-filler _ _ ∙ change-base⁻ (P._⋆ p) (≡×Snd (βᴰ Γᴰ×ⱽp*Pᴰ) .snd)

      introLR≡ : ∀ {Δ}{Δᴰ}{γ γ' : C [ Δ , Γ ]}
        {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
        {pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ]}
        {fᴰ : Cᴰ [ γ' ][ Δᴰ , vertexⱽ Γᴰ×ⱽp*Pᴰ ]}
        → Path Cᴰ.Hom[ _ , _ ]
            (γ , γᴰ)
            ((γ' C.⋆ C.id) , (fᴰ Cᴰ.⋆ᴰ π₁LR))
        → Path Pᴰ.p[ _ , _ ]
            (_ , pᴰ)
            (_ , (fᴰ Pᴰ.⋆ᴰ π₂LR))
        → Path Cᴰ.Hom[ _ , _ ]
            (γ , introLR γᴰ pᴰ)
            (γ' , fᴰ)
      introLR≡ γᴰ≡ pᴰ≡ = introᴰ≡ Γᴰ×ⱽp*Pᴰ (×≡Snd-hSet C.isSetHom
        γᴰ≡
        (change-base {C = Pᴰ.p[_][ _ ]} (P._⋆ _) P.isSetPsh (cong fst γᴰ≡)
          (pᴰ≡ ∙ Pᴰ.reind-filler _ _)))

      extensionalityLR : ∀ {Δ}{Δᴰ}{γ γ' : C [ Δ , Γ ]}
        {fᴰ : Cᴰ [ γ ][ Δᴰ , vertexⱽ Γᴰ×ⱽp*Pᴰ ]}
        {fᴰ' : Cᴰ [ γ' ][ Δᴰ , vertexⱽ Γᴰ×ⱽp*Pᴰ ]}
        → Path Cᴰ.Hom[ _ , _ ]
            ((γ  C.⋆ C.id) , (fᴰ  Cᴰ.⋆ᴰ π₁LR))
            ((γ' C.⋆ C.id) , (fᴰ' Cᴰ.⋆ᴰ π₁LR))
        → Path Pᴰ.p[ _ , _ ]
            (_ , (fᴰ  Pᴰ.⋆ᴰ π₂LR))
            (_ , (fᴰ' Pᴰ.⋆ᴰ π₂LR))
        → Path Cᴰ.Hom[ _ , _ ]
            (γ  , fᴰ)
            (γ' , fᴰ')
      extensionalityLR π₁LR≡ π₂LR≡ = extensionalityᴰ Γᴰ×ⱽp*Pᴰ (×≡Snd-hSet C.isSetHom π₁LR≡ (change-base {C = Pᴰ.p[_][ _ ]} (P._⋆ _) P.isSetPsh
        (cong fst π₁LR≡)
        (sym (Pᴰ.reind-filler _ _) ∙ π₂LR≡ ∙ Pᴰ.reind-filler _ _)))

  module LocallyRepresentableⱽNotation {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ) where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module LRⱽAt {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p} = LocallyRepresentableⱽAtNotation Pᴰ Γᴰ p (Γᴰ ×ⱽ p *Pᴰ)
      module LRⱽAtExp {Γ}(Γᴰ : Cᴰ.ob[ Γ ])(p) = LocallyRepresentableⱽAtNotation Pᴰ Γᴰ p (Γᴰ ×ⱽ p *Pᴰ)
    open LRⱽAt hiding (π₁LR; π₂LR) public
    open LRⱽAtExp using (π₁LR; π₂LR) public

    ⌈_×ⱽ_*Pᴰ⌉ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
    ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ = vertexⱽ $ Γᴰ ×ⱽ p *Pᴰ

    LR-cong : ∀ {Γ}{Γᴰ}{p q : P.p[ Γ ]}(p≡q : p ≡ q)
      → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ q *Pᴰ⌉ ]
    LR-cong p≡q = introLR (π₁LR _ _) (Pᴰ.reind P.⟨⟩⋆⟨ p≡q ⟩ (π₂LR _ _))

    funcLR : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ ⌈ Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    funcLR {p = p}{γ = γ} γᴰ =
      introLR (π₁LR _ (γ P.⋆ p) Cᴰ.⋆ⱽᴰ γᴰ) (Pᴰ.reind (P.⋆IdL _) $ (π₂LR _ (γ P.⋆ p)))

    opaque
      LR-cong≡pathToPshHom :
        ∀ {Γ}{Γᴰ}{p q : P.p[ Γ ]}(p≡q : p ≡ q)
        → LR-cong p≡q ≡ pathToCatIsoⱽ Cᴰ (cong ⌈ Γᴰ ×ⱽ_*Pᴰ⌉ p≡q) .fst
      LR-cong≡pathToPshHom = J (λ q p≡q → LR-cong p≡q ≡ pathToCatIsoⱽ Cᴰ (cong ⌈ _ ×ⱽ_*Pᴰ⌉ p≡q) .fst)
        (Cᴰ.rectify $ Cᴰ.≡out $
          (introLR≡ (sym $ Cᴰ.⋆IdL _)
            (sym (Pᴰ.reind-filler _ _)
            ∙ (sym $ Pᴰ.⋆IdL _)))
          ∙ Cᴰ.reind-filler _ _)

      app-naturality-lemma :
        ∀ {Δ Γ Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
          {p : P.p[ Γ ]}{pᴰ : Pᴰ.p[ p ][ Γᴰ ]}
        → Path (Σ[ γ' ∈ C [ Δ , Γ ] ] (Cᴰ [ γ' ][ Δᴰ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]))
            (C.id C.⋆ γ ,
              (introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) (γᴰ Pᴰ.⋆ᴰ pᴰ)) Cᴰ.⋆ᴰ funcLR γᴰ))
            (γ C.⋆ C.id ,
              (γᴰ Cᴰ.⋆ᴰ introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL p) pᴰ)))
      app-naturality-lemma = extensionalityLR
        (Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨⟩⋆⟨ β₁LR _ _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
        ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ β₁LR _ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _
        ∙ (sym $ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ β₁LR _ _ ⟩ ∙ Cᴰ.⋆IdR _ ) )
        (Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _ _) ⟩ ∙ β₂LR _ _ ∙ sym (Pᴰ.reind-filler _ _)
        ∙ (sym $ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _ _) ⟩))

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  (F : Functor C D)
  (Q : Presheaf D ℓQ)
  (α : PshHet F P Q)
  where
  private
    module P = PresheafNotation P
  preservesLocalReprⱽCone-lemma : ∀ {Γ} (p : P.p[ Γ ]) →
        (yoRec P p ⋆PshHom α)
        ≡
        (Functor→PshHet F _ ⋆PshHom (yoRec Q (α .N-ob _ p) ∘ˡ F))
  preservesLocalReprⱽCone-lemma p = makePshHomPath (funExt λ x → funExt λ γ → α .N-hom _ _ _ _)

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  {α : PshHet F P Q}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  (αᴰ : PshHetᴰ α Fᴰ Pᴰ Qᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  preservesLocalReprⱽCone : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) →
    PshHetⱽ Fᴰ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
               ((Dᴰ [-][-, Fᴰ .F-obᴰ Γᴰ ]) ×ⱽPsh reindYo (α .N-ob _ p) Qᴰ)
  preservesLocalReprⱽCone Γᴰ p =
    ×ⱽ-introHet Fᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ Functorᴰ→PshHetᴰ Fᴰ Γᴰ)
                   (×ⱽ-π₂ ⋆PshHomⱽᴰ
                      reind-introHet
                        (PshHomPathPshHomᴰ
                           (reind-π {α = yoRec P p} ⋆PshHomᴰ αᴰ)
                           (preservesLocalReprⱽCone-lemma F Q α p)))

  preservesLocalReprⱽ : LocallyRepresentableⱽ Pᴰ → Type _
  preservesLocalReprⱽ _×ⱽ_*Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → preservesUEⱽ {Fᴰ = Fᴰ} (preservesLocalReprⱽCone Γᴰ p) (Γᴰ ×ⱽ p *Pᴰ)

  preservesLocalReprⱽ→UEⱽ :
    (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ)
    → preservesLocalReprⱽ _×ⱽ_*Pᴰ
    → ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Dᴰ (F ⟅ Γ ⟆) ((Dᴰ [-][-, Fᴰ .F-obᴰ Γᴰ ]) ×ⱽPsh reindYo (α .N-ob _ p) Qᴰ)
  preservesLocalReprⱽ→UEⱽ _×ⱽ_*Pᴰ pres-⟨_×ⱽ_*Pᴰ⟩ Γᴰ p =
    preservesUEⱽ→UEⱽ (preservesLocalReprⱽCone Γᴰ p) (Γᴰ ×ⱽ p *Pᴰ) pres-⟨ Γᴰ ×ⱽ p *Pᴰ⟩

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf D ℓP}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ)
  (_×ⱽ_*FᴰPᴰ : LocallyRepresentableⱽ (reindFunc' Fᴰ Pᴰ))
  (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ)
  (presLRⱽ : preservesLocalReprⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*FᴰPᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    F⟨_×ⱽ_*FᴰPᴰ⟩ : ∀ {Γ}(Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ F ⟅ Γ ⟆ ]) → UniversalElementⱽ Dᴰ (F ⟅ Γ ⟆) ((Dᴰ [-][-, Fᴰ .F-obᴰ Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    F⟨_×ⱽ_*FᴰPᴰ⟩ = preservesLocalReprⱽ→UEⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*FᴰPᴰ presLRⱽ

  presLRⱽ-Isoⱽ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ F ⟅ Γ ⟆ ])
    → CatIsoⱽ Dᴰ (UniversalElementⱽ.vertexⱽ (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ))
                (Fᴰ .F-obᴰ $ UniversalElementⱽ.vertexⱽ (Γᴰ ×ⱽ p *FᴰPᴰ) )
  presLRⱽ-Isoⱽ Γᴰ p = UEⱽ-essUniq
    (F-obᴰ Fᴰ Γᴰ ×ⱽ p *Pᴰ)
    F⟨ Γᴰ ×ⱽ p *FᴰPᴰ⟩

  module _ {Δ}{Γ}{γ : C [ Δ , Γ ]}{Δᴰ}{Γᴰ : Cᴰ.ob[ Γ ]}(γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(p : P.p[ F ⟅ Γ ⟆ ]) where
    open UniversalElementⱽ
    private
      module LRPᴰ = LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ
      module LRFᴰPᴰ = LocallyRepresentableⱽNotation (reindFunc' Fᴰ Pᴰ) _×ⱽ_*FᴰPᴰ
      module F⟨LR⟩ {Γ}(Γᴰ : Cᴰ.ob[ Γ ]) p = LocallyRepresentableⱽAtNotation Pᴰ (Fᴰ .F-obᴰ Γᴰ) p (F⟨ Γᴰ ×ⱽ p *FᴰPᴰ⟩)
    opaque
      presLRⱽ-Isoⱽ-natural
        : Path (∫C Dᴰ [ _ , _ ])
            (_ , (presLRⱽ-Isoⱽ Δᴰ (F ⟪ γ ⟫ P.⋆ p) .fst Dᴰ.⋆ᴰ Fᴰ .F-homᴰ (LRFᴰPᴰ.funcLR γᴰ)))
            (_ , (LRPᴰ.funcLR (Fᴰ .F-homᴰ γᴰ) Dᴰ.⋆ᴰ presLRⱽ-Isoⱽ Γᴰ p .fst))
      presLRⱽ-Isoⱽ-natural = F⟨LR⟩.extensionalityLR _ _
        (Dᴰ.⋆Assoc _ _ _
        ∙ Dᴰ.⟨ refl ⟩⋆⟨
            Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
            ∙ sym ((∫F Fᴰ) .F-seq _ _)
            ∙ cong (∫F Fᴰ .F-hom) (LRFᴰPᴰ.β₁LR _ _ ∙ sym (Cᴰ.reind-filler _ _))
            ∙ ((∫F Fᴰ) .F-seq _ _)
        ⟩ ∙ sym (Dᴰ.⋆Assoc _ _ _)
        ∙ Dᴰ.⟨ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩ ∙ F⟨LR⟩.β₁LR _ _ _ _ ⟩⋆⟨⟩
        ∙ sym (Dᴰ.⋆Assoc _ _ _
          ∙ Dᴰ.⟨ refl ⟩⋆⟨ F⟨LR⟩.β₁LR _ _ _ _ ⟩
          ∙ LRPᴰ.β₁LR _ _
          ∙ sym (Dᴰ.reind-filler _ _)))
        (Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨⟩⋆⟨
          Pᴰ.⟨⟩⋆⟨
            sym (Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _)
          ⟩ ∙ LRFᴰPᴰ.β₂LR _ _
        ⟩ ∙ Pᴰ.⟨⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ∙ Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _
        ⟩ ∙ F⟨LR⟩.β₂LR _ _ _ _
        ∙ (sym $
        Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ F⟨LR⟩.β₂LR _ _ _ _ ⟩
        ∙ LRPᴰ.β₂LR _ _
        ∙ (sym $ Pᴰ.reind-filler _ _ )))
