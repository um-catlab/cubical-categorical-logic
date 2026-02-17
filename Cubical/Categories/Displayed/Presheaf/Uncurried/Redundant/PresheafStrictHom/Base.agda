{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom.Base where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions renaming
--   (push to pushPsh)
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base
open import Cubical.Categories.Presheaf.StrictHom

open Category
open Categoryᴰ
open Functor
open Iso
open NatIso
open NatTrans
open PshHomStrict

private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHetStrict F P Q)
  where
  PshHet→ElementFunctorᴰStrict : Functorᴰ F (RedundElement P) (RedundElement Q)
  PshHet→ElementFunctorᴰStrict =
    mkPropHomsFunctor (hasPropHomsRedundElement Q)
      (λ {x} → α .N-ob x)
      (elimPropBoth (P .F-ob _ .snd)
        (λ _ → isPropPathEq (Q .F-ob (F .F-ob _) .snd))
        (λ p → inl (α .N-hom _ _ _ _ _ p))
        λ where Eq.refl → symPE (Q .F-ob (F .F-ob _) .snd)
                            (inl (sym $ α .N-hom _ _ _ _ _ refl)))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/FᴰStrict_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHetStrict F P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /FᴰStrict α = ∫F {F = F} (Fᴰ ×ᴰF PshHet→ElementFunctorᴰStrict α)

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  module _ (Fᴰ : Functorⱽ Cᴰ Dᴰ) (α : PshHomStrict P Q) where
    _/FⱽStrict_ :  Functor (Cᴰ / P) (Dᴰ / Q)
    _/FⱽStrict_ = Fᴰ /FᴰStrict (α ⋆PshHomStrict Q→reindPshIdQ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  where

  module _ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    _*Strict_ : Presheafᴰ P Cᴰ ℓQᴰ
    _*Strict_ = reindPsh (Idᴰ /FⱽStrict α) Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  (α : PshHomStrict P Q)
  (β : PshHomStrict Qᴰ Rᴰ)
  where
  _*StrictF_ : PshHomStrict (α *Strict Qᴰ) (α *Strict Rᴰ)
  _*StrictF_ .N-ob = λ c → β .N-ob (F-ob ((Idᴰ /FⱽStrict α) ^opF) c)
  _*StrictF_ .N-hom = λ c c' f →
                         β .N-hom (F-ob ((Idᴰ /FⱽStrict α) ^opF) c)
                         (F-ob ((Idᴰ /FⱽStrict α) ^opF) c')
                         (F-hom ((Idᴰ /FⱽStrict α) ^opF) f)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ} where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  congN-obⱽ : ∀ {Γ}{Γᴰ}{p p'}{pᴰ pᴰ'}
    → (αⱽ : PshHomStrict Pᴰ Qᴰ)
    → pᴰ Pᴰ.∫≡ pᴰ'
    → αⱽ .N-ob (Γ , Γᴰ , p) pᴰ Qᴰ.∫≡ αⱽ .N-ob (Γ , Γᴰ , p') pᴰ'
  congN-obⱽ {Γ} {Γᴰ} {p} {p'} {pᴰ} {pᴰ'} αⱽ pᴰ≡qᴰ i .fst = pᴰ≡qᴰ i .fst
  congN-obⱽ {Γ} {Γᴰ} {p} {p'} {pᴰ} {pᴰ'} αⱽ pᴰ≡qᴰ i .snd = αⱽ .N-ob (Γ , Γᴰ , pᴰ≡qᴰ i .fst) (pᴰ≡qᴰ i .snd)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  *StrictIdIntro : PshHomStrict Pᴰ (idPshHomStrict *Strict Pᴰ)
  *StrictIdIntro .N-ob = λ c z → z
  *StrictIdIntro .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Pᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

  *StrictIdIntro⁻ : PshHomStrict (idPshHomStrict *Strict Pᴰ) Pᴰ
  *StrictIdIntro⁻ .N-ob = λ c z → z
  *StrictIdIntro⁻ .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Pᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ

  *StrictSeqIntro : PshHomStrict (α *Strict (β *Strict Rᴰ)) ((α ⋆PshHomStrict β) *Strict Rᴰ)
  *StrictSeqIntro .N-ob = λ c z → z
  *StrictSeqIntro .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Rᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

  *StrictSeqIntro⁻ : PshHomStrict ((α ⋆PshHomStrict β) *Strict Rᴰ) (α *Strict (β *Strict Rᴰ))
  *StrictSeqIntro⁻ .N-ob = λ c z → z
  *StrictSeqIntro⁻ .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Rᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  PshHomᴰStrict : Type _
  PshHomᴰStrict = PshHomStrict Pᴰ (α *Strict Qᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  idPshHomᴰStrict : PshHomᴰStrict idPshHomStrict Pᴰ Pᴰ
  idPshHomᴰStrict = *StrictIdIntro Pᴰ

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ)
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module P×Q = PresheafNotation (P ×Psh Q)
    module Pᴰ = PresheafᴰNotation Pᴰ

  ΣPsh : Presheafᴰ P Cᴰ (ℓ-max ℓQ ℓPᴰ)
  ΣPsh .F-ob (Γ , Γᴰ , p) .fst = Σ[ q ∈ Q.p[ Γ ] ] Pᴰ.p[ p , q ][ Γᴰ ]
  ΣPsh .F-ob (Γ , Γᴰ , p) .snd =
    isSetΣ (Q .F-ob Γ .snd) (λ x → Pᴰ .F-ob (Γ , Γᴰ , p , x) .snd)
  ΣPsh .F-hom =
    Hom/-elim (λ γ γᴰ γ⋆p≡γp (q , pᴰ) → (γ Q.⋆ q) ,
      Pᴰ .F-hom (γ , (γᴰ , PathEq× P.isSetPsh Q.isSetPsh γ⋆p≡γp (inr Eq.refl))) pᴰ)
  ΣPsh .F-id = funExt λ (q , pᴰ) → ΣPathP ((Q.⋆IdL q) ,
    (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆IdL _))
  ΣPsh .F-seq _ _ =
    funExt λ (q , pᴰ) → ΣPathP (Q.⋆Assoc _ _ _ , (Pᴰ.rectify $ Pᴰ.≡out $
      (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆Assoc _ _ _
      ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.⋆ᴰ-reind _ ⟩
      ∙ Pᴰ.⋆ᴰ-reind _))

  private
    module ΣPsh = PresheafᴰNotation ΣPsh

  ΣPsh-σ : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) ΣPsh)
  ΣPsh-σ .N-ob (_ , _ , (_ , q)) pᴰ = q , pᴰ
  ΣPsh-σ .N-hom _ _ =
    Hom/-elim λ γ γᴰ →
      elimPropEq P×Q.isSetPsh (λ _ → isPropΠ3 λ _ _ _ → ΣPsh.isSetPshᴰ _ _)
        λ {Eq.refl pᴰ pᴰ' e →
          (ΣPsh.rectifyOut $ sym $ ΣPsh.⋆ᴰ-reind _) ∙ ΣPathP (refl , e)}

  module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
    private
      module Rᴰ = PresheafᴰNotation Rᴰ
      ΣPsh-rec : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) Rᴰ) →
                 PshHomStrict ΣPsh Rᴰ
      ΣPsh-rec αᴰ .N-ob = λ c z →
        αᴰ .N-ob (c .fst , c .snd .fst , c .snd .snd , z .fst) (z .snd)
      ΣPsh-rec αᴰ .N-hom _ _ = Hom/-elim λ γ γᴰ →
        elimPropEq P.isSetPsh
          (λ _ → isPropΠ3 λ _ _ _ → Rᴰ.isSetPshᴰ _ _)
          (λ {Eq.refl p' p e →
            (Rᴰ.rectifyOut $ Rᴰ.⋆ᴰ-reind _)
            ∙ αᴰ .N-hom _ _
               (γ , γᴰ , PathEq× P.isSetPsh Q.isSetPsh (inr Eq.refl) (inl (cong fst e)))
               (p' .snd) (p .snd)
               (Pᴰ.rectifyOut ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in (cong snd e)))
           })

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (P : Presheaf C ℓP)
  where
  private
    module P = PresheafNotation P
    module P×P = PresheafNotation (P ×Psh P)

  PathEqPsh' : Functor ((∫C (RedundElement (P ×Psh P))) ^op) (PROP ℓP)
  PathEqPsh' = mkFunctor (PROP ℓP) hasPropHomsPROP
    (λ (_ , p , p') → PathEq p p' , isPropPathEq P.isSetPsh)
    λ {(x , p , p')}{(y , q , q')} (f , fp,fp'≡q,q') →
      elimPropEq P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
        (λ {Eq.refl → elimPropBoth P×P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
          (λ e → inl (sym (cong fst e) ∙ cong snd e))
          (λ eq → inr (Eq.sym (Eq.ap fst eq) Eq.∙ Eq.ap snd eq))
          fp,fp'≡q,q'})

  PathEqPsh : Presheafᴰ (P ×Psh P) Cᴰ ℓP
  PathEqPsh = PROP→SET ∘F PathEqPsh' ∘F (∫F (Sndⱽ Cᴰ (RedundElement (P ×Psh P))) ^opF)

  private
    module PathEqPsh = PresheafᴰNotation PathEqPsh

  Refl : PshHomᴰStrict ΔPshHomStrict UnitPsh PathEqPsh
  Refl .N-ob = λ c z → inr Eq.refl
  Refl .N-hom c c' _ _ _ _ = isPropPathEq P.isSetPsh _ _

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where

  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᴰ = PresheafᴰNotation Pᴰ

  PushPsh : Presheafᴰ Q Cᴰ (ℓP ⊔ℓ ℓPᴰ ⊔ℓ ℓQ)
  PushPsh =
    ΣPsh ((π₂ Q P *Strict Pᴰ) ×Psh
          (×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict α) *Strict PathEqPsh Q))

  private
    module PushPsh = PresheafᴰNotation PushPsh

  PushPsh-σ : PshHomᴰStrict α Pᴰ PushPsh
  PushPsh-σ .N-ob = λ c z → snd (c .snd) , z , inr Eq.refl
  PushPsh-σ .N-hom c c' =
    Hom/-elim (λ γ γᴰ → elimPropEq
      P.isSetPsh
      (λ _ → isPropΠ3 λ _ _ _ → PushPsh.isSetPshᴰ _ _)
      λ {Eq.refl pᴰ' pᴰ e → PushPsh.rectifyOut $
        (sym $ PushPsh.⋆ᴰ-reind _)
        ∙ ΣPathP (α .N-hom _ _ _ _ _ refl ,
            ΣPathP (refl , (ΣPathPProp (λ _ → isPropPathEq Q.isSetPsh)
            (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in e))))
        })

  module _ {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
    private
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Cᴰ = Fibers Cᴰ

    push-recStrictⱽ : PshHomᴰStrict α Pᴰ Qᴰ → PshHomStrict PushPsh Qᴰ
    push-recStrictⱽ αᴰ .N-ob (Γ , Γᴰ , q) (p , pᴰ , q≡αp) =
      Qᴰ .F-hom (Category.id C , Categoryᴰ.idᴰ Cᴰ , inl (Q.⋆IdL _ ∙ sym (PathEq→Path Q.isSetPsh q≡αp)))
        (αᴰ .N-ob (Γ , Γᴰ , p) pᴰ)
    push-recStrictⱽ αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , q') =
      Hom/-elim (λ γ γᴰ → elimPropPath Q.isSetPsh
        (λ _ → isPropΠ3 λ _ _ _ → Qᴰ.isSetPshᴰ _ _)
        λ γ⋆q'≡q (p , pᴰ , q'≡αp) (p' , pᴰ' , q≡αp') e →
          Qᴰ.rectifyOut $
          (sym $ Qᴰ.⋆ᴰ-reind _)
          ∙ Qᴰ.⟨⟩⋆⟨ sym $ Qᴰ.⋆ᴰ-reind _ ⟩
          ∙ sym (Qᴰ.⋆Assoc _ _ _)
          ∙ Qᴰ.⟨ Cᴰ.⋆IdR _ ⟩⋆⟨⟩
          ∙ ((sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _)
          ∙ (Qᴰ.≡in $ αᴰ .N-hom (Δ , Δᴰ , p') (Γ , Γᴰ , p)
                (γ , γᴰ , inl (cong fst e))
                pᴰ pᴰ'
                (Pᴰ.rectifyOut $ ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _)
                  ∙ Pᴰ.≡in (cong (λ z → z .snd .fst) e)))
          ∙ (sym $ Qᴰ.⋆IdL _)
          ∙ Qᴰ.⋆ᴰ-reind _)
