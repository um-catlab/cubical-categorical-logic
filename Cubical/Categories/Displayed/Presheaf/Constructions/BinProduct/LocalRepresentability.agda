{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.LocalRepresentability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (∫F)
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
                   (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-introHet (PshHomPathPshHomᴰ (preservesLocalReprⱽCone-lemma F Q α p) (reind-π {α = yoRec P p} ⋆PshHomᴰ αᴰ)))

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
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Q : Presheaf D ℓQ}
  (F : Functor C D)
  ((Qᴰ , _×ⱽ_*Qᴰ) : LocallyRepresentableⱽPresheafᴰ Q Dᴰ ℓQᴰ)
  where
  private
    module Q = PresheafNotation Q
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Dᴰ = Fibers Dᴰ
  open UniversalElementⱽ
  reindFunc'Reindπ-LocallyRepresentableⱽ : LocallyRepresentableⱽ (reindFunc' (ReindCatᴰ.π Dᴰ F) Qᴰ)
  reindFunc'Reindπ-LocallyRepresentableⱽ {Γ} Γᴰ p =
    reindUEⱽ  (Γᴰ ×ⱽ p *Qᴰ)
    ◁PshIsoⱽ (reindⱽFunc×ⱽIsoⱽ {F = F} ⋆PshIsoⱽ (reindⱽFuncRepr {Dᴰ = Dᴰ}{F = F} ×ⱽIso
      (reindPshIsoⱽ reindFuncReind
      ⋆PshIsoⱽ reind-seqIsoⱽ (Functor→PshHet F Γ) (yoRec Q p ∘ˡ F) (reindFunc F Qᴰ)
      ⋆PshIsoⱽ reindPathIsoⱽ (sym $ yoRec≡ (Q ∘F (F ^opF)) (sym $ Q.⟨ F .F-id ⟩⋆⟨⟩ ∙ Q.⋆IdL _)))))

  -- Doing this without subst-isUniversalⱽ led to interminable type-checking
  Reindπ-preservesLocalReprⱽ : preservesLocalReprⱽ (ReindCatᴰ.π Dᴰ F) (reindFunc' (ReindCatᴰ.π Dᴰ F) Qᴰ) Qᴰ idPshHomᴰ reindFunc'Reindπ-LocallyRepresentableⱽ
  Reindπ-preservesLocalReprⱽ {Γ} Γᴰ q {Δ} {Δᴰ} {γ} = subst-isUniversalⱽ Dᴰ (F-ob F Γ) ((Dᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo q Qᴰ)
    (ΣPathP
    ( (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.reind-filler (λ i → F .F-id (~ i)) _ ∙ Dᴰ.reind-filler (λ i → F .F-id i) _)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler (λ i → (Q PresheafNotation.⋆ F .F-id (~ i)) q) _ ∙ Qᴰ.reind-filler (λ i →
                                                                                                                      funExt⁻
                                                                                                                      (funExt⁻
                                                                                                                       (λ i₁ →
                                                                                                                          N-ob
                                                                                                                          (yoRec≡ (Q ∘F (F ^opF))
                                                                                                                           (λ i₂ → ((λ i₃ → Q .F-hom (F .F-id i₃) q) ∙ Q.⋆IdL q) (~ i₂))
                                                                                                                           (~ i₁)))
                                                                                                                       Γ)
                                                                                                                      (Category.id C) i) _ ∙ Qᴰ.reind-filler (λ i →
                                                                                                                                                                funExt₂⁻
                                                                                                                                                                (λ i₁ → preservesLocalReprⱽCone-lemma F Q idPshHom q i₁ .N-ob) Γ
                                                                                                                                                                (Category.id C) i) _ ∙ Qᴰ.reind-filler (λ i → (Q PresheafNotation.⋆ F .F-id i) q) _)))
    (universalⱽ (Γᴰ ×ⱽ q *Qᴰ))

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ


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

    π₂LR-cong : ∀ {Γ} {p q : P.p[ Γ ]} Γᴰ
      → (p≡q : p ≡ q)
      → (id⋆p≡id⋆q : C.id P.⋆ p ≡ C.id P.⋆ q)
      → PathP (λ i → Pᴰ.p[ C.id P.⋆ q ][ ⌈ Γᴰ ×ⱽ p≡q i *Pᴰ⌉ ])
          (Pᴰ.reind id⋆p≡id⋆q (π₂LR Γᴰ p))
          (π₂LR Γᴰ q)
    π₂LR-cong Γᴰ p≡q id*p≡id*q =
      rectify ((sym (congS₂Bifunct Pᴰ~ _ _ _ _) ∙ (congS₂ (congS₂ Pᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))))
        (compPathP
          ((Pᴰ.≡out $ sym $ Pᴰ.reind-filler _ _))
          π₂LR _ ⟨ p≡q ⟩)
      where
        Pᴰ~ : (p : P.p[ _ ])(p' : P.p[ _ ]) → Type _
        Pᴰ~ p p' = Pᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p' *Pᴰ⌉ ]

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
        ∫ue.intro≡ (_ ×ⱽ _ *Pᴰ) (×≡Snd-hSet C.isSetHom
          (sym $ Cᴰ.⋆IdL _)
          (chacha-slide {C = Pᴰ.p[_][ _ ]} (P._⋆ _) P.isSetPsh (sym $ C.⋆IdL _)
            (sym (Pᴰ.reind-filler _ _)
            ∙ (sym $ Pᴰ.⋆IdL _)
            ∙ Pᴰ.reind-filler _ _ )))
          ∙ Cᴰ.reind-filler _ _)
    
      -- TODO: this was very slow, is it faster now?
      funcLR-seq : ∀
        {Γ}{Γᴰ}{p : P.p[ Γ ]}
        {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        {Θ}{Θᴰ}{δ : C [ Θ , Δ ]}
        (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
        → PathP (λ i → Cᴰ [ δ C.⋆ γ ][ ⌈ Θᴰ ×ⱽ (P.⋆Assoc δ γ p i) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
            (funcLR {p = p} (δᴰ Cᴰ.⋆ᴰ γᴰ))
            (funcLR δᴰ Cᴰ.⋆ᴰ funcLR γᴰ)
      funcLR-seq {Γ} {Γᴰ} {p} {Δ} {Δᴰ} {γ} {Θ} {Θᴰ} {δ} γᴰ δᴰ =
        PresheafᴰNotation.toPathPPshᴰ (Cᴰ [-][-, _ ]) (cong ⌈ _ ×ⱽ_*Pᴰ⌉ (P.⋆Assoc _ _ _))
          (∫ue.extensionality (_ ×ⱽ _ *Pᴰ) (×≡Snd-hSet C.isSetHom
            (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ ≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .fst ⟩
            ∙ sym (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ ≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .fst ⟩
            ∙ sym Cᴰ.∫⋆Assocᴰⱽᴰ
            ∙ Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ ≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .fst ⟩⋆⟨ refl ⟩
            ∙ sym ((sym (Cᴰ.≡in Cᴰ.⋆Assocᴰⱽᴰ) ∙ Cᴰ.⟨ sym (Cᴰ.reind-filler _ _) ∙ PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, _ ]) (λ i → ⌈ Θᴰ ×ⱽ P.⋆Assoc δ γ p i *Pᴰ⌉) (λ i → π₁LR Θᴰ (P.⋆Assoc δ γ p i)) ⟩⋆⟨ refl ⟩ ∙ Cᴰ.reind-filler _ _)
              ∙ sym (Cᴰ.≡in Cᴰ.⋆Assocⱽᴰᴰ))))
            (chacha-slide (P._⋆ p) P.isSetPsh
              C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩
              (sym (Pᴰ.reind-filler _ _) ∙ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ chacha-slide⁻ (P._⋆ p) (≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .snd) ⟩
              ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
              ∙ sym (sym (Pᴰ.reind-filler _ _) ∙ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ chacha-slide⁻ (P._⋆ p) (≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .snd) ∙ (sym $ Pᴰ.reind-filler _ _) ⟩
              ∙ Pᴰ.reind-filler _ _ ∙ chacha-slide⁻ (P._⋆ _) (≡×Snd (∫ue.β (_ ×ⱽ _ *Pᴰ)) .snd)
              ∙ sym (Pᴰ.reind-filler _ _)
              ∙ sym (PresheafᴰNotation.fromPathPPshᴰ' Pᴰ {p≡q = P.⟨⟩⋆⟨ P.⋆Assoc _ _ _ ⟩ } ((λ i → ⌈ Θᴰ ×ⱽ P.⋆Assoc δ γ p i *Pᴰ⌉)) λ i → π₂LR Θᴰ (P.⋆Assoc δ γ p i)))))))

      funcLR-id : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
        → PathP (λ i → Cᴰ [ C.id ][ ⌈ Γᴰ ×ⱽ P.⋆IdL p i *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
            (funcLR {Γᴰ = Γᴰ}{p = p} Cᴰ.idᴰ)
            Cᴰ.idᴰ
      funcLR-id {Γ}{Γᴰ}{p} = symP (PresheafᴰNotation.toPathPPshᴰ (Cᴰ [-][-, _ ]) ((cong ⌈ _ ×ⱽ_*Pᴰ⌉) (sym $ P.⋆IdL _))
        (Cᴰ.⋆IdR _ ∙ sym (∫ue.intro≡ (_ ×ⱽ _ *Pᴰ) (×≡Snd-hSet C.isSetHom
          ((sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _
          ∙ sym (PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, _ ]) ((cong ⌈ _ ×ⱽ_*Pᴰ⌉) (sym $ P.⋆IdL _)) (λ i → π₁LR Γᴰ (P.⋆IdL p (~ i)))))
          (chacha-slide (P._⋆ _) P.isSetPsh (sym $ C.⋆IdL _)
            ((sym $ Pᴰ.reind-filler _ _) ∙ sym ((sym $ Pᴰ.reind-filler _ _)
            ∙ PresheafᴰNotation.fromPathPPshᴰ' Pᴰ {p≡q = λ i → C.id P.⋆ P.⋆IdL p (~ i)} ((cong ⌈ _ ×ⱽ_*Pᴰ⌉) (sym $ P.⋆IdL _)) (λ i → π₂LR Γᴰ (P.⋆IdL p (~ i))))))))))

      app-naturality-lemma :
        ∀ {Δ Γ Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
          {p : P.p[ Γ ]}{pᴰ : Pᴰ.p[ p ][ Γᴰ ]}
        → Path (Σ[ γ' ∈ C [ Δ , Γ ] ] (Cᴰ [ γ' ][ Δᴰ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]))
            (C.id C.⋆ γ ,
              (introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) (γᴰ Pᴰ.⋆ᴰ pᴰ)) Cᴰ.⋆ᴰ funcLR γᴰ))
            (γ C.⋆ C.id ,
              (γᴰ Cᴰ.⋆ᴰ introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL p) pᴰ)))
      app-naturality-lemma {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {γᴰ} {p} {pᴰ} = sym $
          ∫ue.intro-natural (Γᴰ ×ⱽ p *Pᴰ)
          ∙ ∫ue.intro≡ (Γᴰ ×ⱽ p *Pᴰ) (×≡Snd-hSet C.isSetHom
            (Cᴰ.⋆IdR _
            ∙ (sym $ Cᴰ.⋆IdL _)
            ∙ Cᴰ.⟨ (sym $ ≡×Snd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .fst) ⟩⋆⟨ refl ⟩
            ∙ Cᴰ.⋆Assoc _ _ _
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym $ ≡×Snd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .fst) ⟩
            ∙ sym (Cᴰ.⋆Assoc _ _ _) )
            (chacha-slide (P._⋆ p) P.isSetPsh C.⟨ sym $ C.⋆IdL γ ⟩⋆⟨ refl ⟩ $ sym $
              sym (Pᴰ.reind-filler _ _)
              ∙ Pᴰ.⋆Assoc _ _ _
              ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ chacha-slide⁻ (P._⋆ p) (≡×Snd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .snd)  ⟩
              ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
              ∙ Pᴰ.reind-filler _ _ ∙ (chacha-slide⁻ (P._⋆ (γ P.⋆ p)) $ ≡×Snd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .snd)
              ∙ sym (Pᴰ.reind-filler _ _)
              ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler (sym $ P.⋆IdL p) pᴰ ⟩
              ∙ Pᴰ.reind-filler _ _
            ))
      -- TODO: test perf vs this original version
      -- sym $
      --   ∫ue.intro-natural (Γᴰ ×ⱽ p *Pᴰ)
      --   ∙ ∫ue.intro≡ (Γᴰ ×ⱽ p *Pᴰ) (ΣPathPSnd
      --     (Cᴰ.⋆IdR _
      --     ∙ (sym $ Cᴰ.⋆IdL _)
      --     ∙ Cᴰ.⟨ (sym $ PathPΣSnd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .fst) ⟩⋆⟨ refl ⟩
      --     ∙ Cᴰ.⋆Assoc _ _ _
      --     ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym $ PathPΣSnd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .fst) ⟩
      --     ∙ sym (Cᴰ.⋆Assoc _ _ _) )
      --     (Pᴰ.rectify $ Pᴰ.≡out $ sym $
      --       sym (Pᴰ.reind-filler _ _)
      --       ∙ Pᴰ.⋆Assoc _ _ _
      --       ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ (Pᴰ.≡in $ PathPΣSnd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .snd) ⟩
      --       ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
      --       ∙ Pᴰ.reind-filler _ _ ∙ (Pᴰ.≡in $ PathPΣSnd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .snd)
      --       ∙ sym (Pᴰ.reind-filler _ _)
      --       ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler (sym $ P.⋆IdL p) pᴰ ⟩
      --       ∙ Pᴰ.reind-filler _ _))

-- Goal: (C.id C.⋆ γ ,
--        introLR Cᴰ.idᴰ
--        (Pᴰ.reind (λ i → P.⋆IdL (γ P.⋆ p) (~ i)) (γᴰ Pᴰ.⋆ᴰ pᴰ))
--        Cᴰ.⋆ᴰ funcLR γᴰ)
--       ≡
--       (γ C.⋆ C.id ,
--        γᴰ Cᴰ.⋆ᴰ introLR Cᴰ.idᴰ (Pᴰ.reind (λ i → P.⋆IdL p (~ i)) pᴰ))

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
    opaque
      presLRⱽ-Isoⱽ-natural
        : Path (∫C Dᴰ [ _ , _ ])
            (_ , (presLRⱽ-Isoⱽ Δᴰ (F ⟪ γ ⟫ P.⋆ p) .fst Dᴰ.⋆ᴰ Fᴰ .F-homᴰ (LocallyRepresentableⱽNotation.funcLR (reindFunc' Fᴰ Pᴰ) _×ⱽ_*FᴰPᴰ γᴰ)))
            (_ , (LocallyRepresentableⱽNotation.funcLR Pᴰ _×ⱽ_*Pᴰ (Fᴰ .F-homᴰ γᴰ) Dᴰ.⋆ᴰ presLRⱽ-Isoⱽ Γᴰ p .fst))
      presLRⱽ-Isoⱽ-natural = extensionalityᴰ F⟨ Γᴰ ×ⱽ p *FᴰPᴰ⟩ (×≡Snd-hSet
        D.isSetHom
        (Dᴰ.⋆Assoc _ _ _
        ∙ Dᴰ.⟨ refl ⟩⋆⟨
            Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
            ∙ sym ((∫F Fᴰ) .F-seq _ _)
            ∙ cong (∫F Fᴰ .F-hom) (≡×Snd (βᴰ $ Γᴰ ×ⱽ p *FᴰPᴰ) .fst ∙ sym (Cᴰ.reind-filler _ _))
            ∙ ((∫F Fᴰ) .F-seq _ _)
        ⟩ ∙ sym (Dᴰ.⋆Assoc _ _ _)
        ∙ Dᴰ.⟨ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩ ∙ ≡×Snd (βᴰ $ F⟨ Δᴰ ×ⱽ (F ⟪ γ ⟫ P.⋆ p) *FᴰPᴰ⟩) .fst ⟩⋆⟨ refl ⟩
        ∙ sym (Dᴰ.⋆Assoc _ _ _
          ∙ Dᴰ.⟨ refl ⟩⋆⟨ ≡×Snd (βᴰ $ F⟨ Γᴰ ×ⱽ p *FᴰPᴰ⟩) .fst ⟩
          ∙  ≡×Snd (βᴰ $ (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ)) .fst
          ∙ sym (Dᴰ.reind-filler _ _)))
        (chacha-slide {C = λ Fγ⋆p → Pᴰ.p[ Fγ⋆p ][ vertexⱽ (Fᴰ .F-obᴰ Δᴰ ×ⱽ F ⟪ γ ⟫ P.⋆ p *Pᴰ) ]} (P._⋆ p) P.isSetPsh (D.⋆IdR _ ∙ D.⋆IdL _ ∙ sym (D.⋆IdR _ ∙ D.⋆IdR _))
          (sym (Pᴰ.reind-filler (λ i → P .F-seq D.id (D.id D.⋆ F .F-hom γ) (~ i) p) _)
          ∙ Pᴰ.⋆Assoc _ _ _
          ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.⟨⟩⋆⟨ sym (Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler (λ i → P .F-hom (F .F-id i) p) _) ⟩
                    ∙ Pᴰ.reind-filler _ _
                    ∙ chacha-slide⁻ (λ γ → F ⟪ γ ⟫ P.⋆ p) (≡×Snd (βᴰ (Γᴰ ×ⱽ p *FᴰPᴰ)) .snd)
          ⟩ ∙ Pᴰ.⟨⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ∙ (Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler (λ i → P .F-hom (F .F-id i) (P .F-hom (F-hom F γ) p)) _) ⟩ ∙ Pᴰ.reind-filler (λ i → P .F-seq D.id D.id (~ i) (P .F-hom (F-hom F γ) p)) _
          ∙ chacha-slide⁻ (P._⋆ (F ⟪ γ ⟫ P.⋆ p)) (≡×Snd (βᴰ (F⟨ Δᴰ ×ⱽ (F ⟪ γ ⟫ P.⋆ p) *FᴰPᴰ⟩)) .snd)
          ∙ sym (sym (Pᴰ.reind-filler (λ i → P .F-seq D.id (F .F-hom γ D.⋆ D.id) (~ i) p) _)
          ∙ Pᴰ.⋆Assoc _ _ _
          ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler (λ i → P .F-seq D.id D.id (~ i) p) _ ∙ chacha-slide⁻ (λ γ → γ P.⋆ p) (≡×Snd (βᴰ (F⟨ Γᴰ ×ⱽ p *FᴰPᴰ⟩)) .snd) ⟩
          ∙ Pᴰ.reind-filler (λ i → P .F-seq D.id (F .F-hom γ) (~ i) p) _ ∙ chacha-slide⁻ (λ γ → γ P.⋆ p) (≡×Snd (βᴰ (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ)) .snd)
          ∙ sym (Pᴰ.reind-filler (λ i → P .F-id i (P .F-hom (F .F-hom γ) p)) _))))
          )
