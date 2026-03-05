{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Bifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct hiding (Fst; Snd; Sym)
import Cubical.Categories.Instances.TotalCategory as ∫
open import Cubical.Categories.Bifunctor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
import Cubical.Categories.Displayed.Reasoning as Reasoning


private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓᴰ ℓᴰ' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'} where
  -- This is based on the BifunctorParAx definition
  record Bifunctorᴰ (F : Bifunctor C D E)
                    (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
                    (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
                    (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ')
     : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD (ℓ-max ℓD' (ℓ-max ℓE (ℓ-max ℓE'
            (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' (ℓ-max ℓDᴰ (ℓ-max ℓDᴰ'
            (ℓ-max ℓEᴰ ℓEᴰ'))))))))))) where
    no-eta-equality
    private
      module Cᴰ = Categoryᴰ Cᴰ
      module Dᴰ = Categoryᴰ Dᴰ
      module Eᴰ = Categoryᴰ Eᴰ
      module R = Reasoning Eᴰ
      module F = Bifunctor F

    field
      Bif-obᴰ : ∀ {c d} → (cᴰ : Cᴰ.ob[ c ]) → (dᴰ : Dᴰ.ob[ d ])
        → Eᴰ.ob[ F ⟅ c , d ⟆b ]
      Bif-homLᴰ : ∀ {c c' cᴰ cᴰ'} {f : C [ c , c' ]} (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
        {d} (dᴰ : Dᴰ.ob[ d ])
        → Eᴰ [ F ⟪ f ⟫l ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ ]
      Bif-homRᴰ : ∀ {c} (cᴰ : Cᴰ.ob[ c ]) {d d' dᴰ dᴰ'}
        {g : D [ d , d' ]} (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
        → Eᴰ [ F ⟪ g ⟫r ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ dᴰ' ]
      Bif-hom×ᴰ : ∀ {c c' d d'} {f : C [ c , c' ]}{g : D [ d , d' ]}
             {cᴰ cᴰ' dᴰ dᴰ'}
             (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
             (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
             → Eᴰ [ F ⟪ f , g ⟫× ][ Bif-obᴰ cᴰ dᴰ , Bif-obᴰ cᴰ' dᴰ' ]
      Bif-×-idᴰ : ∀ {c d cᴰ dᴰ}
        → Bif-hom×ᴰ (Cᴰ.idᴰ {p = cᴰ}) (Dᴰ.idᴰ {p = dᴰ})
            Eᴰ.≡[ F.Bif-×-id {c = c}{d = d} ]
          Eᴰ.idᴰ
      Bif-×-seqᴰ :
        ∀ {c c' c'' d d' d''}{cᴰ cᴰ' cᴰ'' dᴰ dᴰ' dᴰ''}
        → {f : C [ c , c' ]}{f' : C [ c' , c'' ]}
        → {g : D [ d , d' ]}{g' : D [ d' , d'' ]}
        → (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ]) (fᴰ' : Cᴰ [ f' ][ cᴰ' , cᴰ'' ])
        → (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ]) (gᴰ' : Dᴰ [ g' ][ dᴰ' , dᴰ'' ])
        → Bif-hom×ᴰ (fᴰ Cᴰ.⋆ᴰ fᴰ') (gᴰ Dᴰ.⋆ᴰ gᴰ')
            Eᴰ.≡[ F.Bif-×-seq f f' g g' ]
          (Bif-hom×ᴰ fᴰ gᴰ Eᴰ.⋆ᴰ Bif-hom×ᴰ fᴰ' gᴰ')
      Bif-L×-agreeᴰ : ∀ {c c' d}{cᴰ cᴰ' dᴰ}
        {f : C [ c , c' ]}
        (fᴰ : Cᴰ [ f ][ cᴰ , cᴰ' ])
        → Bif-homLᴰ fᴰ dᴰ Eᴰ.≡[ F.Bif-L×-agree {d = d} f ] Bif-hom×ᴰ fᴰ Dᴰ.idᴰ
      Bif-R×-agreeᴰ : ∀ {c d d'}{cᴰ dᴰ dᴰ'}
        {g : D [ d , d' ]}
        (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])
        → Bif-homRᴰ cᴰ gᴰ Eᴰ.≡[ F.Bif-R×-agree {c = c} g ] Bif-hom×ᴰ Cᴰ.idᴰ gᴰ

    Bif-R-idᴰ : ∀ {c d}{cᴰ dᴰ}
      → Bif-homRᴰ cᴰ (Dᴰ.idᴰ {d}{dᴰ})
          Eᴰ.≡[ F.Bif-R-id {c} ]
        Eᴰ.idᴰ
    Bif-R-idᴰ = R.rectify (R.≡out (R.≡in (Bif-R×-agreeᴰ _) ∙ R.≡in Bif-×-idᴰ))

    Bif-R-seqᴰ : ∀ {c d d' d''}{g : D [ d , d' ]}{g' : D [ d' , d'' ]}
                  {cᴰ : Cᴰ.ob[ c ]}{dᴰ dᴰ' dᴰ''}
                  (gᴰ : Dᴰ [ g ][ dᴰ , dᴰ' ])(gᴰ' : Dᴰ [ g' ][ dᴰ' , dᴰ'' ])
              → Bif-homRᴰ cᴰ (gᴰ Dᴰ.⋆ᴰ gᴰ')
                  Eᴰ.≡[ F.Bif-R-seq g g' ]
                Bif-homRᴰ cᴰ gᴰ Eᴰ.⋆ᴰ Bif-homRᴰ cᴰ gᴰ'
    Bif-R-seqᴰ gᴰ gᴰ' = R.rectify $ R.≡out $
      (R.≡in $ Bif-R×-agreeᴰ _)
      ∙ (R.≡in $ (λ i → Bif-hom×ᴰ (Cᴰ.⋆IdRᴰ Cᴰ.idᴰ (~ i)) (gᴰ Dᴰ.⋆ᴰ gᴰ')))
      ∙ (R.≡in $ Bif-×-seqᴰ _ _ _ _)
      ∙ R.⟨ sym $ R.≡in $ Bif-R×-agreeᴰ _ ⟩⋆⟨ sym $ R.≡in $ Bif-R×-agreeᴰ _ ⟩

private
  variable
    C D E C' D' E' : Category ℓ ℓ'
    Cᴰ Dᴰ Eᴰ Cᴰ' Dᴰ' Eᴰ' : Categoryᴰ C ℓ ℓ'

module _ {F : Bifunctor C D E} (Fᴰ : Bifunctorᴰ F Cᴰ Dᴰ Eᴰ) where
  private
    module Eᴰ = Reasoning Eᴰ
  ∫Bif : Bifunctor (∫.∫C Cᴰ) (∫.∫C Dᴰ) (∫.∫C Eᴰ)
  ∫Bif = mkBifunctorParAx ∫BifParAx where
    open BifunctorParAx
    ∫BifParAx : BifunctorParAx (∫.∫C Cᴰ) (∫.∫C Dᴰ) (∫.∫C Eᴰ)
    ∫BifParAx .Bif-ob (c , cᴰ) (d , dᴰ) =
      (Bifunctor.Bif-ob F c d) , (Fᴰ .Bifunctorᴰ.Bif-obᴰ cᴰ dᴰ)
    ∫BifParAx .Bif-homL (f , fᴰ) (d , dᴰ) =
      (Bifunctor.Bif-homL F f d) , (Fᴰ .Bifunctorᴰ.Bif-homLᴰ fᴰ dᴰ)
    ∫BifParAx .Bif-homR (c , cᴰ) (g , gᴰ) =
      (Bifunctor.Bif-homR F c g) , (Fᴰ .Bifunctorᴰ.Bif-homRᴰ cᴰ gᴰ)
    ∫BifParAx .Bif-hom× (f , fᴰ) (g , gᴰ) =
      (Bifunctor.Bif-hom× F f g) , (Fᴰ .Bifunctorᴰ.Bif-hom×ᴰ fᴰ gᴰ)
    ∫BifParAx .Bif-×-id = Eᴰ.≡in $ (Fᴰ .Bifunctorᴰ.Bif-×-idᴰ)
    ∫BifParAx .Bif-×-seq (f , fᴰ) (f' , fᴰ') (g , gᴰ) (g' , gᴰ') =
      Eᴰ.≡in $ Fᴰ .Bifunctorᴰ.Bif-×-seqᴰ fᴰ fᴰ' gᴰ gᴰ'
    ∫BifParAx .Bif-L×-agree (f , fᴰ) = Eᴰ.≡in $ Fᴰ .Bifunctorᴰ.Bif-L×-agreeᴰ fᴰ
    ∫BifParAx .Bif-R×-agree (g , gᴰ) = Eᴰ.≡in $ Fᴰ .Bifunctorᴰ.Bif-R×-agreeᴰ gᴰ

open Category
open Categoryᴰ
open Functorᴰ
open Bifunctorᴰ
appLᴰ : {F : Bifunctor C D E} (Fᴰ : Bifunctorᴰ F Cᴰ Dᴰ Eᴰ)
  {c : C .ob} (cᴰ : ob[_] Cᴰ c) → Functorᴰ (appL F c) Dᴰ Eᴰ
appLᴰ Fᴰ cᴰ .F-obᴰ dᴰ = Fᴰ .Bif-obᴰ cᴰ dᴰ
appLᴰ Fᴰ cᴰ .F-homᴰ gᴰ = Fᴰ .Bif-homRᴰ cᴰ gᴰ
appLᴰ Fᴰ cᴰ .F-idᴰ = Bif-R-idᴰ Fᴰ
appLᴰ Fᴰ cᴰ .Functorᴰ.F-seqᴰ = Bif-R-seqᴰ Fᴰ

appRᴰ : {F : Bifunctor C D E} (Fᴰ : Bifunctorᴰ F Cᴰ Dᴰ Eᴰ)
  {d : D .ob} (dᴰ : ob[_] Dᴰ d) → Functorᴰ (appR F d) Cᴰ Eᴰ
appRᴰ {Eᴰ = Eᴰ}{F = F} Fᴰ dᴰ = record
  { F-obᴰ = λ xᴰ → ∫appR .F-ob (_ , xᴰ) .snd
  ; F-homᴰ = λ fᴰ → ∫appR .F-hom (_ , fᴰ) .snd
  ; F-idᴰ =
    R.rectify $ λ i → ∫appR .F-id i .snd
  ; F-seqᴰ = λ fᴰ gᴰ → R.rectify $ λ i → ∫appR .F-seq (_ , fᴰ) (_ , gᴰ) i .snd
  } where
  open Functor
  module R = Reasoning Eᴰ
  ∫appR = appR (∫Bif Fᴰ) (_ , dᴰ)

module _ {F : Bifunctor C' D E} {G : Functor C C'}
  (Fᴰ : Bifunctorᴰ F Cᴰ' Dᴰ Eᴰ) (Gᴰ : Functorᴰ G Cᴰ Cᴰ') where
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Eᴰ = Reasoning Eᴰ
  compLᴰ : Bifunctorᴰ (compL F G) Cᴰ Dᴰ Eᴰ
  compLᴰ .Bif-obᴰ x = Fᴰ .Bif-obᴰ (F-obᴰ Gᴰ x)
  compLᴰ .Bif-homLᴰ fᴰ dᴰ = Fᴰ .Bif-homLᴰ (F-homᴰ Gᴰ fᴰ) dᴰ
  compLᴰ .Bif-homRᴰ cᴰ gᴰ = Fᴰ .Bif-homRᴰ (F-obᴰ Gᴰ cᴰ) gᴰ
  compLᴰ .Bif-hom×ᴰ fᴰ gᴰ = Fᴰ .Bif-hom×ᴰ (F-homᴰ Gᴰ fᴰ) gᴰ
  compLᴰ .Bif-×-idᴰ = Eᴰ.rectify $ Eᴰ.≡out $
    (Eᴰ.≡in $ λ i → Fᴰ .Bif-hom×ᴰ (Gᴰ .F-idᴰ i) Dᴰ.idᴰ)
    ∙ (Eᴰ.≡in $ Fᴰ .Bif-×-idᴰ)
  compLᴰ .Bif-×-seqᴰ fᴰ fᴰ' gᴰ gᴰ' = Eᴰ.rectify $ Eᴰ.≡out $
    (Eᴰ.≡in $ (λ i → Fᴰ .Bif-hom×ᴰ (Gᴰ .F-seqᴰ fᴰ fᴰ' i) (gᴰ Dᴰ.⋆ᴰ gᴰ')))
    ∙ (Eᴰ.≡in $ Fᴰ .Bif-×-seqᴰ _ _ _ _)
  compLᴰ .Bif-L×-agreeᴰ fᴰ = Eᴰ.rectify $ Fᴰ .Bif-L×-agreeᴰ _
  compLᴰ .Bif-R×-agreeᴰ gᴰ = Eᴰ.rectify $ Eᴰ.≡out $
    (Eᴰ.≡in $ Fᴰ .Bif-R×-agreeᴰ _)
    ∙ (Eᴰ.≡in $ λ i → Fᴰ .Bif-hom×ᴰ (Gᴰ .F-idᴰ (~ i)) gᴰ)

module _ {F : Bifunctor C D' E} {G : Functor D D'}
  (Fᴰ : Bifunctorᴰ F Cᴰ Dᴰ' Eᴰ) (Gᴰ : Functorᴰ G Dᴰ Dᴰ') where
  private
    module Eᴰ = Reasoning Eᴰ
    ∫compRᴰ = compR (∫Bif Fᴰ) (∫.∫F Gᴰ)
    module ∫compRᴰ = Bifunctor ∫compRᴰ
  compRᴰ : Bifunctorᴰ (compR F G) Cᴰ Dᴰ Eᴰ
  compRᴰ .Bif-obᴰ cᴰ dᴰ = ∫compRᴰ.Bif-ob (_ , cᴰ) (_ , dᴰ) .snd
  compRᴰ .Bif-homLᴰ fᴰ dᴰ = ∫compRᴰ.Bif-homL (_ , fᴰ) (_ , dᴰ) .snd
  compRᴰ .Bif-homRᴰ cᴰ gᴰ = ∫compRᴰ.Bif-homR (_ , cᴰ) (_ , gᴰ) .snd
  compRᴰ .Bif-hom×ᴰ fᴰ gᴰ = ∫compRᴰ.Bif-hom× (_ , fᴰ) (_ , gᴰ) .snd
  compRᴰ .Bif-×-idᴰ = Eᴰ.rectify $ λ i → ∫compRᴰ.Bif-×-id i .snd
  compRᴰ .Bif-×-seqᴰ fᴰ fᴰ' gᴰ gᴰ' = Eᴰ.rectify $ λ i →
    ∫compRᴰ.Bif-×-seq (_ , fᴰ) (_ , fᴰ') (_ , gᴰ) (_ , gᴰ') i .snd
  compRᴰ .Bif-L×-agreeᴰ fᴰ = Eᴰ.rectify $ λ i →
    ∫compRᴰ.Bif-L×-agree (_ , fᴰ) i .snd
  compRᴰ .Bif-R×-agreeᴰ gᴰ = Eᴰ.rectify $ λ i →
    ∫compRᴰ.Bif-R×-agree (_ , gᴰ) i .snd

module _ {F : Functor E E'}{G : Bifunctor C D E}
       (Fᴰ : Functorᴰ F Eᴰ Eᴰ')(Gᴰ : Bifunctorᴰ G Cᴰ Dᴰ Eᴰ)
  where
  private
    module Eᴰ' = Reasoning Eᴰ'
    ∫compFᴰ = compF (∫.∫F Fᴰ) (∫Bif Gᴰ)
    module ∫compFᴰ = Bifunctor ∫compFᴰ
  compFᴰ : Bifunctorᴰ (compF F G) Cᴰ Dᴰ Eᴰ'
  compFᴰ .Bif-obᴰ cᴰ dᴰ = ∫compFᴰ.Bif-ob (_ , cᴰ) (_ , dᴰ) .snd
  compFᴰ .Bif-homLᴰ fᴰ dᴰ = ∫compFᴰ.Bif-homL (_ , fᴰ) (_ , dᴰ) .snd
  compFᴰ .Bif-homRᴰ cᴰ gᴰ = ∫compFᴰ.Bif-homR (_ , cᴰ) (_ , gᴰ) .snd
  compFᴰ .Bif-hom×ᴰ fᴰ gᴰ = ∫compFᴰ.Bif-hom× (_ , fᴰ) (_ , gᴰ) .snd
  compFᴰ .Bif-×-idᴰ = Eᴰ'.rectify $ λ i → ∫compFᴰ.Bif-×-id i .snd
  compFᴰ .Bif-×-seqᴰ fᴰ fᴰ' gᴰ gᴰ' = Eᴰ'.rectify $ λ i →
    ∫compFᴰ.Bif-×-seq (_ , fᴰ) (_ , fᴰ') (_ , gᴰ) (_ , gᴰ') i .snd
  compFᴰ .Bif-L×-agreeᴰ fᴰ = Eᴰ'.rectify $ λ i →
    ∫compFᴰ.Bif-L×-agree (_ , fᴰ) i .snd
  compFᴰ .Bif-R×-agreeᴰ gᴰ = Eᴰ'.rectify $ λ i →
    ∫compFᴰ.Bif-R×-agree (_ , gᴰ) i .snd

module _ {F : Bifunctor C' D' E} {G : Functor C C'}{H : Functor D D'}
  (Fᴰ : Bifunctorᴰ F Cᴰ' Dᴰ' Eᴰ)(Gᴰ : Functorᴰ G Cᴰ Cᴰ')(Hᴰ : Functorᴰ H Dᴰ Dᴰ')
  where
  compLRᴰ : Bifunctorᴰ (F ∘Flr (G , H)) Cᴰ Dᴰ Eᴰ
  compLRᴰ = compRᴰ (compLᴰ Fᴰ Gᴰ) Hᴰ

module _ {F : Functor (C ×C D) E}
         (Fᴰ : Functorᴰ F (Cᴰ ×Cᴰ Dᴰ) Eᴰ) where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module Eᴰ = Reasoning Eᴰ
  ParFunctorᴰToBifunctorᴰ : Bifunctorᴰ (ParFunctorToBifunctor F) Cᴰ Dᴰ Eᴰ
  ParFunctorᴰToBifunctorᴰ .Bif-obᴰ cᴰ dᴰ = Fᴰ .F-obᴰ (cᴰ , dᴰ)
  ParFunctorᴰToBifunctorᴰ .Bif-homLᴰ fᴰ dᴰ = Fᴰ .F-homᴰ (fᴰ , Dᴰ.idᴰ)
  ParFunctorᴰToBifunctorᴰ .Bif-homRᴰ cᴰ gᴰ = Fᴰ .F-homᴰ (Cᴰ.idᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ .Bif-hom×ᴰ fᴰ gᴰ = Fᴰ .F-homᴰ (fᴰ , gᴰ)
  ParFunctorᴰToBifunctorᴰ .Bif-×-idᴰ = Fᴰ .F-idᴰ
  ParFunctorᴰToBifunctorᴰ .Bif-×-seqᴰ fᴰ fᴰ' gᴰ gᴰ' =
    Fᴰ .F-seqᴰ (fᴰ , gᴰ) (fᴰ' , gᴰ')
  ParFunctorᴰToBifunctorᴰ .Bif-L×-agreeᴰ fᴰ = refl
  ParFunctorᴰToBifunctorᴰ .Bif-R×-agreeᴰ gᴰ = refl
