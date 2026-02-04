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

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Qᴰ = PresheafᴰNotation Qᴰ
      module α*↓Pᴰ = PresheafᴰNotation (PushPsh α Pᴰ)

    push-UMP : Iso (PshHomStrict (PushPsh α Pᴰ) Qᴰ) (PshHomᴰStrict α Pᴰ Qᴰ)
    -- push-UMP : Iso (PshHomⱽ (push α Pᴰ) Qᴰ) (PshHomᴰ α Pᴰ Qᴰ)
    push-UMP .fun βⱽ = PushPsh-σ α Pᴰ ⋆PshHomStrict (α *StrictF βⱽ)
    push-UMP .inv = push-recStrictⱽ α Pᴰ
    push-UMP .sec βⱽ =
      makePshHomStrictPath
        (funExt₂ λ _ _ → Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _ ∙ Qᴰ.⋆IdL _)
    push-UMP .ret βⱽ =
      makePshHomStrictPath
        (funExt₂ λ x → λ {(p , pᴰ , q≡αp) →
          -- {!!}
          elimPropPath Q.isSetPsh {M = λ pe →
           Qᴰ .F-hom
             (id C ,
              idᴰ Cᴰ ,
              inl
              (Q.⋆IdL
               (F-ob (∫F (Sndⱽ Cᴰ (RedundElement (Q ×Psh Q))) ^opF)
                (F-ob
                 ((Idᴰ /FⱽStrict ×PshIntroStrict (π₁ Q P) (π₂ Q P ⋆PshHomStrict α))
                  ^opF)
                 (x .fst , x .snd .fst , x .snd .snd , p))
                .snd .snd)
               ∙ (λ i → PathEq→Path Q.isSetPsh pe (~ i))))
             (βⱽ .N-ob
              (F-ob ((Idᴰ /FⱽStrict α) ^opF) (x .fst , x .snd .fst , p))
              (p , pᴰ , inr Eq.refl))
             ≡ βⱽ .N-ob x (p , pᴰ , pe)}

            (λ _ → Qᴰ.isSetPshᴰ _ _) (λ {q≡αp →
              Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆IdL _
              ∙ ΣPathP (sym q≡αp , (Qᴰ.rectifyOut $ congN-obⱽ βⱽ
                  (α*↓Pᴰ.≡in {pth = sym q≡αp} (
                     ΣPathP (refl ,
                             ΣPathP (refl ,
                                     isProp→PathP (λ _ _ → isPropPathEq Q.isSetPsh _) _ _))))))
            })
            q≡αp
          }
        )

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Cᴰ = Fibers Cᴰ

  -- Frobenius Reciprocity: ∃α (Pᴰ × α*Qᴰ) ≅ (∃α Pᴰ) × Qᴰ
  FrobeniusReciprocityStrict-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .Category.ob) →
    Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ] × Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ]) × PathEq q (α .N-ob Γ p))
        ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × PathEq q (α .N-ob Γ p)) × Qᴰ.p[ q ][ Γᴰ ])
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.fun (p , (pᴰ , qᴰ) , q≡αp) =
    (p , pᴰ , q≡αp) , Qᴰ.reind (sym $ PathEq→Path Q.isSetPsh q≡αp) qᴰ
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.inv ((p , pᴰ , q≡αp) , qᴰ) =
    p , (pᴰ , Qᴰ.reind (PathEq→Path Q.isSetPsh q≡αp) qᴰ) , q≡αp
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.sec ((p , pᴰ , q≡αp) , qᴰ) =
    ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _))
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.ret (p , (pᴰ , qᴰ) , q≡αp) =
    ΣPathP (refl , ΣPathP (ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _)) , refl))

  private
    -- ∃α (Pᴰ × α*Qᴰ)
    LHS : Presheafᴰ Q Cᴰ _
    LHS = PushPsh α (Pᴰ ×Psh (α *Strict Qᴰ))

    -- (∃α Pᴰ) × Qᴰ
    RHS : Presheafᴰ Q Cᴰ _
    RHS = (PushPsh α Pᴰ) ×Psh Qᴰ

    module LHSMod = PresheafᴰNotation LHS
    module RHSMod = PresheafᴰNotation RHS

  -- Naturality condition: for f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ] and p at (Γ,Γᴰ,q'),
  -- fun (iso at Δ,Δᴰ,q) (f ⋆ p) ≡ f ⋆ (fun (iso at Γ,Γᴰ,q') p)
  FrobeniusReciprocityStrict-natural :
    ∀ (Δ,Δᴰ,q : (Cᴰ / Q) .Category.ob) (Γ,Γᴰ,q' : (Cᴰ / Q) .Category.ob)
    (f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ])
    (p : ⟨ LHS .F-ob Γ,Γᴰ,q' ⟩) →
    fun (FrobeniusReciprocityStrict-ptwise Δ,Δᴰ,q) (LHS .F-hom f p)
      ≡
    RHS .F-hom f (fun (FrobeniusReciprocityStrict-ptwise Γ,Γᴰ,q') p)
  FrobeniusReciprocityStrict-natural (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q'≡q) (p , (pᴰ , qᴰ) , q'≡αp) =
    ΣPathP (refl , (Qᴰ.rectifyOut $
      Qᴰ.reind-filler⁻ _
      ∙ (sym $ Qᴰ.⋆ᴰ-reind _)
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩ ∙ Qᴰ.⋆ᴰ-reind _))

  FrobeniusReciprocityStrict : PshIsoStrict LHS RHS
  FrobeniusReciprocityStrict = Isos→PshIsoStrict
    FrobeniusReciprocityStrict-ptwise
    FrobeniusReciprocityStrict-natural

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
  where
  *Strict×ⱽ→×ⱽ*Strict :
    PshHomStrict (α *Strict (Qᴰ ×ⱽPsh Rᴰ)) ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
  *Strict×ⱽ→×ⱽ*Strict = pshhom (λ c z → z) (λ c c' f p' p z → z)

  ×ⱽ*Strict→*Strict×ⱽ :
    PshHomStrict
      ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
      (α *Strict (Qᴰ ×ⱽPsh Rᴰ))
  ×ⱽ*Strict→*Strict×ⱽ = pshhom (λ c z → z) (λ c c' f p' p z → z)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ

  _⋆PshHomᴰStrict_ :
    (αᴰ : PshHomᴰStrict α Pᴰ Qᴰ)
    (βᴰ : PshHomᴰStrict β Qᴰ Rᴰ) →
    PshHomᴰStrict (α ⋆PshHomStrict β) Pᴰ Rᴰ
  αᴰ ⋆PshHomᴰStrict βᴰ =
    αᴰ
    ⋆PshHomStrict (α *StrictF βᴰ)
    ⋆PshHomStrict *StrictSeqIntro

  infixr 9 _⋆PshHomᴰStrict_

module _
  (C : Category ℓC ℓC')
  (ℓP : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = Category PSH
    module Cᴰ = Fibers Cᴰ
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
  PRESHEAFᴰ .idᴰ = idPshHomᴰStrict
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰStrict_
  PRESHEAFᴰ .⋆IdLᴰ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .⋆IdRᴰ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .⋆Assocᴰ _ _ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHomStrict _ _
  private
    module PSHᴰ = Fibers PRESHEAFᴰ

  PSHᴰTerminalsⱽ : Terminalsⱽ PRESHEAFᴰ
  PSHᴰTerminalsⱽ P .fst = Unit*Psh
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .fun αᴰ = tt
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-ob = λ c _ → tt*
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-hom = λ _ _ _ _ _ _ → refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .sec _ = refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .ret _ = makePshHomStrictPath refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.nat _ _ _ _ = inr Eq.refl

  PSHᴰBPⱽ : BinProductsⱽ PRESHEAFᴰ
  PSHᴰBPⱽ Pᴰ Qᴰ =
    UEⱽ→Reprⱽ _ (λ {x = x₁} {y} f → Eq.refl) (record {
        v = Pᴰ ×ⱽPsh Qᴰ
      ; e = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Pᴰ ,
            π₂ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
      ; universal = record {
        nIso = λ c →
          (λ (αᴰ , βᴰ) → ×PshIntroStrict αᴰ βᴰ ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Pᴰ Qᴰ) ,
          (λ _ → ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)) ,
          λ _ → makePshHomStrictPath refl
          } })

  -- Slow, broke
  -- Something about using the record constructor inline vs hiding behind coprojections?
  -- Or is it about more annotations?
  -- PSHᴰFibration : Fibration PRESHEAFᴰ λ f g h → Eq.refl
  -- PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl)
  --   (record {
  --     v = α *Strict Pᴰ
  --   ; e = idPshHomStrict
  --   ; universal = {!!} })

  -- Fast, woke
  PSHᴰFibrationUE : FibrationUE PRESHEAFᴰ (λ f g h → Eq.refl) λ {x} {y} f → Eq.refl
  PSHᴰFibrationUE α Pᴰ .UEⱽ.v = α *Strict Pᴰ
  PSHᴰFibrationUE α Pᴰ .UEⱽ.e = idPshHomStrict
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .fst βᴰ =
    βᴰ ⋆PshHomStrict *StrictSeqIntro⁻
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .fst _ =
    makePshHomStrictPath refl
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .snd _ =
    makePshHomStrictPath refl

  PSHᴰFibration : Fibration PRESHEAFᴰ (λ f g h → Eq.refl)
  PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl) (PSHᴰFibrationUE α Pᴰ)
