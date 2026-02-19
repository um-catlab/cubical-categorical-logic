{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Instance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHom
open PshIso

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

  ΣPshEq : Presheafᴰ P Cᴰ (ℓ-max ℓQ ℓPᴰ)
  ΣPshEq .F-ob (Γ , Γᴰ , p) .fst = Σ[ q ∈ Q.p[ Γ ] ] Pᴰ.p[ p , q ][ Γᴰ ]
  ΣPshEq .F-ob (Γ , Γᴰ , p) .snd =
    isSetΣ (Q .F-ob Γ .snd) (λ x → Pᴰ .F-ob (Γ , Γᴰ , p , x) .snd)
  ΣPshEq .F-hom (γ , γᴰ , Eq.refl) (q , pᴰ) = γ Q.⋆ q , Pᴰ .F-hom (γ , γᴰ , Eq.refl) pᴰ
  ΣPshEq .F-id {x = x} i (q , pᴰ) = opq i
    where
    -- opaque reind gets stuck here
    -- Its frustrating to write out the signature below
    -- A point in favor of PathEq
    opaque
      unfolding depReasoning.reind
      opq : (transp
           (λ i₁ →
              Σ (fst (F-ob Q (x .fst)))
              (λ q₁ →
                 fst
                 (Pᴰ .F-ob
                  (x .fst ,
                   x .snd .fst ,
                   hcomp
                   (λ i₂ .o →
                      transp (λ i₃ → fst (F-ob P (x .fst))) i₂
                      (primPOr i₁ (~ i₁) (λ .o₁ → P .F-id i₂ (x .snd .snd))
                       (λ .o₁ → P .F-hom (C .id) (x .snd .snd)) o))
                   (transp (λ i₂ → fst (F-ob P (x .fst))) i0
                    (P .F-hom (C .id) (x .snd .snd)))
                   , q₁))))
           i0
           (Q .F-hom (C .id) (transp (λ i₁ → fst (F-ob Q (x .fst))) i0 q) ,
            Pᴰ .F-hom (C .id , Categoryᴰ.idᴰ Cᴰ , Eq.refl)
            (transp
             (λ i₁ →
                fst
                (Pᴰ .F-ob
                 (x .fst ,
                  x .snd .fst ,
                  x .snd .snd , transp (λ i₂ → fst (F-ob Q (x .fst))) (~ i₁) q)))
             i0 pᴰ)))
        ≡
        (q , pᴰ)
      opq = ΣPathP
        (transportRefl _ ∙ Q.⟨⟩⋆⟨ transportRefl _ ⟩ ∙ Q.⋆IdL _ ,
          (Pᴰ.rectifyOut $ Pᴰ.reind-filler⁻ _ ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler⁻ _ ⟩ ∙ Pᴰ.⋆IdL _))

    -- funExt λ (q , pᴰ) → ΣPathP ({!!} , (Pᴰ.rectifyOut $ {!Pᴰ.reind-filler⁻ _ ∙ ?!}))
    -- (Pᴰ.rectifyOut $ ?))
  ΣPshEq .F-seq _ _ = {!!}
    -- funExt λ (q , pᴰ) → ΣPathP (Q.⋆Assoc _ _ _ , (Pᴰ.rectify $ Pᴰ.≡out $
    --   (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆Assoc _ _ _
    --   ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.⋆ᴰ-reind _ ⟩
    --   ∙ Pᴰ.⋆ᴰ-reind _))

--   private
--     module ΣPsh = PresheafᴰNotation ΣPsh


--   ΣPsh-σ : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) ΣPsh)
--   ΣPsh-σ .N-ob (_ , _ , (_ , q)) pᴰ = q , pᴰ
--   ΣPsh-σ .N-hom _ _ =
--     Hom/-elim λ γ γᴰ →
--       elimPropEq P×Q.isSetPsh (λ _ → isPropΠ3 λ _ _ _ → ΣPsh.isSetPshᴰ _ _)
--         λ {Eq.refl pᴰ pᴰ' e →
--           (ΣPsh.rectifyOut $ sym $ ΣPsh.⋆ᴰ-reind _) ∙ ΣPathP (refl , e)}

--   module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
--     private
--       module Rᴰ = PresheafᴰNotation Rᴰ
--       ΣPsh-rec : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) Rᴰ) →
--                  PshHomStrict ΣPsh Rᴰ
--       ΣPsh-rec αᴰ .N-ob = λ c z →
--         αᴰ .N-ob (c .fst , c .snd .fst , c .snd .snd , z .fst) (z .snd)
--       ΣPsh-rec αᴰ .N-hom _ _ = Hom/-elim λ γ γᴰ →
--         elimPropEq P.isSetPsh
--           (λ _ → isPropΠ3 λ _ _ _ → Rᴰ.isSetPshᴰ _ _)
--           (λ {Eq.refl p' p e →
--             (Rᴰ.rectifyOut $ Rᴰ.⋆ᴰ-reind _)
--             ∙ αᴰ .N-hom _ _
--                (γ , γᴰ , PathEq× P.isSetPsh Q.isSetPsh (inr Eq.refl) (inl (cong fst e)))
--                (p' .snd) (p .snd)
--                (Pᴰ.rectifyOut ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in (cong snd e)))
--            })

-- module _ {C : Category ℓC ℓC'}
--   {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   (P : Presheaf C ℓP)
--   where
--   private
--     module P = PresheafNotation P
--     module P×P = PresheafNotation (P ×Psh P)

--   PathEqPsh' : Functor ((∫C (RedundElement (P ×Psh P))) ^op) (PROP ℓP)
--   PathEqPsh' = mkFunctor (PROP ℓP) hasPropHomsPROP
--     (λ (_ , p , p') → PathEq p p' , isPropPathEq P.isSetPsh)
--     λ {(x , p , p')}{(y , q , q')} (f , fp,fp'≡q,q') →
--       elimPropEq P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
--         (λ {Eq.refl → elimPropBoth P×P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
--           (λ e → inl (sym (cong fst e) ∙ cong snd e))
--           (λ eq → inr (Eq.sym (Eq.ap fst eq) Eq.∙ Eq.ap snd eq))
--           fp,fp'≡q,q'})

--   PathEqPsh : Presheafᴰ (P ×Psh P) Cᴰ ℓP
--   PathEqPsh = PROP→SET ∘F PathEqPsh' ∘F (∫F (Sndⱽ Cᴰ (RedundElement (P ×Psh P))) ^opF)

--   private
--     module PathEqPsh = PresheafᴰNotation PathEqPsh

--   Refl : PshHomᴰStrict ΔPshHomStrict UnitPsh PathEqPsh
--   Refl .N-ob = λ c z → inr Eq.refl
--   Refl .N-hom c c' _ _ _ _ = isPropPathEq P.isSetPsh _ _

-- module _ {C : Category ℓC ℓC'}
--   {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ}
--   (α : PshHomStrict P Q)
--   (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
--   where

--   private
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--     module Pᴰ = PresheafᴰNotation Pᴰ

--   PushPsh : Presheafᴰ Q Cᴰ (ℓP ⊔ℓ ℓPᴰ ⊔ℓ ℓQ)
--   PushPsh =
--     ΣPsh ((π₂ Q P *Strict Pᴰ) ×Psh
--           (×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict α) *Strict PathEqPsh Q))

--   private
--     module PushPsh = PresheafᴰNotation PushPsh

--   PushPsh-σ : PshHomᴰStrict α Pᴰ PushPsh
--   PushPsh-σ .N-ob = λ c z → snd (c .snd) , z , inr Eq.refl
--   PushPsh-σ .N-hom c c' =
--     Hom/-elim (λ γ γᴰ → elimPropEq
--       P.isSetPsh
--       (λ _ → isPropΠ3 λ _ _ _ → PushPsh.isSetPshᴰ _ _)
--       λ {Eq.refl pᴰ' pᴰ e → PushPsh.rectifyOut $
--         (sym $ PushPsh.⋆ᴰ-reind _)
--         ∙ ΣPathP (α .N-hom _ _ _ _ _ refl ,
--             ΣPathP (refl , (ΣPathPProp (λ _ → isPropPathEq Q.isSetPsh)
--             (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in e))))
--         })

--   module _ {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
--     private
--       module Qᴰ = PresheafᴰNotation Qᴰ
--       module Cᴰ = Fibers Cᴰ

--     push-recStrictⱽ : PshHomᴰStrict α Pᴰ Qᴰ → PshHomStrict PushPsh Qᴰ
--     push-recStrictⱽ αᴰ .N-ob (Γ , Γᴰ , q) (p , pᴰ , q≡αp) =
--       Qᴰ .F-hom (Category.id C , Categoryᴰ.idᴰ Cᴰ , inl (Q.⋆IdL _ ∙ sym (PathEq→Path Q.isSetPsh q≡αp)))
--         (αᴰ .N-ob (Γ , Γᴰ , p) pᴰ)
--     push-recStrictⱽ αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , q') =
--       Hom/-elim (λ γ γᴰ → elimPropPath Q.isSetPsh
--         (λ _ → isPropΠ3 λ _ _ _ → Qᴰ.isSetPshᴰ _ _)
--         λ γ⋆q'≡q (p , pᴰ , q'≡αp) (p' , pᴰ' , q≡αp') e →
--           Qᴰ.rectifyOut $
--           (sym $ Qᴰ.⋆ᴰ-reind _)
--           ∙ Qᴰ.⟨⟩⋆⟨ sym $ Qᴰ.⋆ᴰ-reind _ ⟩
--           ∙ sym (Qᴰ.⋆Assoc _ _ _)
--           ∙ Qᴰ.⟨ Cᴰ.⋆IdR _ ⟩⋆⟨⟩
--           ∙ ((sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _)
--           ∙ (Qᴰ.≡in $ αᴰ .N-hom (Δ , Δᴰ , p') (Γ , Γᴰ , p)
--                 (γ , γᴰ , inl (cong fst e))
--                 pᴰ pᴰ'
--                 (Pᴰ.rectifyOut $ ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _)
--                   ∙ Pᴰ.≡in (cong (λ z → z .snd .fst) e)))
--           ∙ (sym $ Qᴰ.⋆IdL _)
--           ∙ Qᴰ.⋆ᴰ-reind _)

-- module _ {C : Category ℓC ℓC'}
--   {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ}
--   (α : PshHomStrict P Q)
--   (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
--   (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
--   where
--     private
--       module P = PresheafNotation P
--       module Q = PresheafNotation Q
--       module Qᴰ = PresheafᴰNotation Qᴰ
--       module α*↓Pᴰ = PresheafᴰNotation (PushPsh α Pᴰ)

--     push-UMP : Iso (PshHomStrict (PushPsh α Pᴰ) Qᴰ) (PshHomᴰStrict α Pᴰ Qᴰ)
--     -- push-UMP : Iso (PshHomⱽ (push α Pᴰ) Qᴰ) (PshHomᴰ α Pᴰ Qᴰ)
--     push-UMP .fun βⱽ = PushPsh-σ α Pᴰ ⋆PshHomStrict (α *StrictF βⱽ)
--     push-UMP .inv = push-recStrictⱽ α Pᴰ
--     push-UMP .sec βⱽ =
--       makePshHomStrictPath
--         (funExt₂ λ _ _ → Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _ ∙ Qᴰ.⋆IdL _)
--     push-UMP .ret βⱽ =
--       makePshHomStrictPath
--         (funExt₂ λ x → λ {(p , pᴰ , q≡αp) →
--           -- {!!}
--           elimPropPath Q.isSetPsh {M = λ pe →
--            Qᴰ .F-hom
--              (id C ,
--               idᴰ Cᴰ ,
--               inl
--               (Q.⋆IdL
--                (F-ob (∫F (Sndⱽ Cᴰ (RedundElement (Q ×Psh Q))) ^opF)
--                 (F-ob
--                  ((Idᴰ /FⱽStrict ×PshIntroStrict (π₁ Q P) (π₂ Q P ⋆PshHomStrict α))
--                   ^opF)
--                  (x .fst , x .snd .fst , x .snd .snd , p))
--                 .snd .snd)
--                ∙ (λ i → PathEq→Path Q.isSetPsh pe (~ i))))
--              (βⱽ .N-ob
--               (F-ob ((Idᴰ /FⱽStrict α) ^opF) (x .fst , x .snd .fst , p))
--               (p , pᴰ , inr Eq.refl))
--              ≡ βⱽ .N-ob x (p , pᴰ , pe)}

--             (λ _ → Qᴰ.isSetPshᴰ _ _) (λ {q≡αp →
--               Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆IdL _
--               ∙ ΣPathP (sym q≡αp , (Qᴰ.rectifyOut $ congN-obⱽ βⱽ
--                   (α*↓Pᴰ.≡in {pth = sym q≡αp} (
--                      ΣPathP (refl ,
--                              ΣPathP (refl ,
--                                      isProp→PathP (λ _ _ → isPropPathEq Q.isSetPsh _) _ _))))))
--             })
--             q≡αp
--           }
--         )

-- module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
--   (α : PshHomStrict P Q)
--   (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
--   (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
--   where
--   private
--     module C = Category C
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--     module Pᴰ = PresheafᴰNotation Pᴰ
--     module Qᴰ = PresheafᴰNotation Qᴰ
--     module Cᴰ = Fibers Cᴰ

--   -- Frobenius Reciprocity: ∃α (Pᴰ × α*Qᴰ) ≅ (∃α Pᴰ) × Qᴰ
--   FrobeniusReciprocityStrict-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .Category.ob) →
--     Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ] × Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ]) × PathEq q (α .N-ob Γ p))
--         ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × PathEq q (α .N-ob Γ p)) × Qᴰ.p[ q ][ Γᴰ ])
--   FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.fun (p , (pᴰ , qᴰ) , q≡αp) =
--     (p , pᴰ , q≡αp) , Qᴰ.reind (sym $ PathEq→Path Q.isSetPsh q≡αp) qᴰ
--   FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.inv ((p , pᴰ , q≡αp) , qᴰ) =
--     p , (pᴰ , Qᴰ.reind (PathEq→Path Q.isSetPsh q≡αp) qᴰ) , q≡αp
--   FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.sec ((p , pᴰ , q≡αp) , qᴰ) =
--     ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _))
--   FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.ret (p , (pᴰ , qᴰ) , q≡αp) =
--     ΣPathP (refl , ΣPathP (ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _)) , refl))

--   private
--     -- ∃α (Pᴰ × α*Qᴰ)
--     LHS : Presheafᴰ Q Cᴰ _
--     LHS = PushPsh α (Pᴰ ×Psh (α *Strict Qᴰ))

--     -- (∃α Pᴰ) × Qᴰ
--     RHS : Presheafᴰ Q Cᴰ _
--     RHS = (PushPsh α Pᴰ) ×Psh Qᴰ

--     module LHSMod = PresheafᴰNotation LHS
--     module RHSMod = PresheafᴰNotation RHS

--   -- Naturality condition: for f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ] and p at (Γ,Γᴰ,q'),
--   -- fun (iso at Δ,Δᴰ,q) (f ⋆ p) ≡ f ⋆ (fun (iso at Γ,Γᴰ,q') p)
--   FrobeniusReciprocityStrict-natural :
--     ∀ (Δ,Δᴰ,q : (Cᴰ / Q) .Category.ob) (Γ,Γᴰ,q' : (Cᴰ / Q) .Category.ob)
--     (f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ])
--     (p : ⟨ LHS .F-ob Γ,Γᴰ,q' ⟩) →
--     fun (FrobeniusReciprocityStrict-ptwise Δ,Δᴰ,q) (LHS .F-hom f p)
--       ≡
--     RHS .F-hom f (fun (FrobeniusReciprocityStrict-ptwise Γ,Γᴰ,q') p)
--   FrobeniusReciprocityStrict-natural (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q'≡q) (p , (pᴰ , qᴰ) , q'≡αp) =
--     ΣPathP (refl , (Qᴰ.rectifyOut $
--       Qᴰ.reind-filler⁻ _
--       ∙ (sym $ Qᴰ.⋆ᴰ-reind _)
--       ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩ ∙ Qᴰ.⋆ᴰ-reind _))

--   FrobeniusReciprocityStrict : PshIsoStrict LHS RHS
--   FrobeniusReciprocityStrict = Isos→PshIsoStrict
--     FrobeniusReciprocityStrict-ptwise
--     FrobeniusReciprocityStrict-natural

-- module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ}
--   (α : PshHomStrict P Q)
--   (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
--   (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
--   where
--   *Strict×ⱽ→×ⱽ*Strict :
--     PshHomStrict (α *Strict (Qᴰ ×ⱽPsh Rᴰ)) ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
--   *Strict×ⱽ→×ⱽ*Strict = pshhom (λ c z → z) (λ c c' f p' p z → z)

--   ×ⱽ*Strict→*Strict×ⱽ :
--     PshHomStrict
--       ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
--       (α *Strict (Qᴰ ×ⱽPsh Rᴰ))
--   ×ⱽ*Strict→*Strict×ⱽ = pshhom (λ c z → z) (λ c c' f p' p z → z)

--   private
--     F : Functor (Cᴰ / P) (Cᴰ / Q)
--     F = Idᴰ /FⱽStrict α

--   *Strict⇒ⱽ→⇒ⱽ*Strict :
--     PshHomStrict
--       (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
--       ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
--   *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-ob c' (γ , qᴰ) =
--     f .N-ob (F ⟅ c' ⟆) (F ⟪ γ ⟫ , qᴰ)
--   *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-hom c'' c' e (γ' , qᴰ') (γ , qᴰ) eq =
--     f .N-hom (F ⟅ c'' ⟆) (F ⟅ c' ⟆) (F ⟪ e ⟫) (F ⟪ γ' ⟫ , qᴰ') (F ⟪ γ ⟫ , qᴰ)
--       (ΣPathP (sym (F .F-seq e γ') ∙ cong (F .F-hom) (cong fst eq) , cong snd eq))
--   *Strict⇒ⱽ→⇒ⱽ*Strict .N-hom c c' h f' f eq =
--     makePshHomStrictPath (funExt₂ λ d (γ , qᴰ) →
--       cong (λ δ → f' .N-ob (F ⟅ d ⟆) (δ , qᴰ)) (F .F-seq γ h)
--       ∙ funExt⁻ (funExt⁻ (cong N-ob eq) (F ⟅ d ⟆)) (F ⟪ γ ⟫ , qᴰ))

--   private
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--     module Qᴰ = PresheafᴰNotation Qᴰ
--     module Rᴰ = PresheafᴰNotation Rᴰ

--   ⇒ⱽ*Strict→*Strict⇒ⱽ :
--     PshHomStrict
--       ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
--       (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
--   ⇒ⱽ*Strict→*Strict⇒ⱽ =
--     push-UMP α ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) (Qᴰ ⇒PshLargeStrict Rᴰ) .Iso.fun
--       (λPshHomStrict Qᴰ Rᴰ
--         (invPshIsoStrict
--           (FrobeniusReciprocityStrict α
--            ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) Qᴰ)
--              .PshIsoStrict.trans
--           ⋆PshHomStrict push-UMP α (((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) ×Psh
--                                      (α *Strict Qᴰ)) Rᴰ .inv
--                         (appPshHomStrict (α *Strict Qᴰ) (α *Strict Rᴰ))))

-- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ}
--   {R : Presheaf C ℓR}
--   {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
--   {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
--   {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
--   {α : PshHomStrict P Q}
--   {β : PshHomStrict Q R}
--   where
--   private
--     module Pᴰ = PresheafᴰNotation Pᴰ
--     module Qᴰ = PresheafᴰNotation Qᴰ
--     module Rᴰ = PresheafᴰNotation Rᴰ

--   _⋆PshHomᴰStrict_ :
--     (αᴰ : PshHomᴰStrict α Pᴰ Qᴰ)
--     (βᴰ : PshHomᴰStrict β Qᴰ Rᴰ) →
--     PshHomᴰStrict (α ⋆PshHomStrict β) Pᴰ Rᴰ
--   αᴰ ⋆PshHomᴰStrict βᴰ =
--     αᴰ
--     ⋆PshHomStrict (α *StrictF βᴰ)
--     ⋆PshHomStrict *StrictSeqIntro

--   infixr 9 _⋆PshHomᴰStrict_

-- module _
--   (C : Category ℓC ℓC')
--   (ℓP : Level)
--   (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--   (ℓPᴰ : Level)
--   where
--   private
--     PSH = PRESHEAF C ℓP
--     module PSH = Category PSH
--     module Cᴰ = Fibers Cᴰ
--   PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
--   PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
--   PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
--   PRESHEAFᴰ .idᴰ = idPshHomᴰStrict
--   PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰStrict_
--   PRESHEAFᴰ .⋆IdLᴰ _ = makePshHomStrictPath refl
--   PRESHEAFᴰ .⋆IdRᴰ _ = makePshHomStrictPath refl
--   PRESHEAFᴰ .⋆Assocᴰ _ _ _ = makePshHomStrictPath refl
--   PRESHEAFᴰ .isSetHomᴰ = isSetPshHomStrict _ _
--   private
--     module PSHᴰ = Fibers PRESHEAFᴰ

--   PSHᴰTerminalsⱽ : Terminalsⱽ PRESHEAFᴰ
--   PSHᴰTerminalsⱽ P .fst = Unit*Psh
--   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .fun αᴰ = tt
--   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-ob = λ c _ → tt*
--   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-hom = λ _ _ _ _ _ _ → refl
--   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .sec _ = refl
--   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .ret _ = makePshHomStrictPath refl
--   PSHᴰTerminalsⱽ P .snd .PshIso'.nat _ _ _ _ = inr Eq.refl

--   PSHᴰBPⱽ : BinProductsⱽ PRESHEAFᴰ
--   PSHᴰBPⱽ Pᴰ Qᴰ =
--     UEⱽ→Reprⱽ _ (λ {x = x₁} {y} f → Eq.refl) (record {
--         v = Pᴰ ×ⱽPsh Qᴰ
--       ; e = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Pᴰ ,
--             π₂ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
--       ; universal = record {
--         nIso = λ c →
--           (λ (αᴰ , βᴰ) → ×PshIntroStrict αᴰ βᴰ ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Pᴰ Qᴰ) ,
--           (λ _ → ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)) ,
--           λ _ → makePshHomStrictPath refl
--           } })

--   -- Slow, broke
--   -- Something about using the record constructor inline vs hiding behind coprojections?
--   -- Or is it about more annotations?
--   -- PSHᴰFibration : Fibration PRESHEAFᴰ λ f g h → Eq.refl
--   -- PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl)
--   --   (record {
--   --     v = α *Strict Pᴰ
--   --   ; e = idPshHomStrict
--   --   ; universal = {!!} })

--   -- Fast, woke
--   PSHᴰFibrationUE : FibrationUE PRESHEAFᴰ (λ f g h → Eq.refl) λ {x} {y} f → Eq.refl
--   PSHᴰFibrationUE α Pᴰ .UEⱽ.v = α *Strict Pᴰ
--   PSHᴰFibrationUE α Pᴰ .UEⱽ.e = idPshHomStrict
--   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .fst βᴰ =
--     βᴰ ⋆PshHomStrict *StrictSeqIntro⁻
--   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .fst _ =
--     makePshHomStrictPath refl
--   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .snd _ =
--     makePshHomStrictPath refl

--   PSHᴰFibration : Fibration PRESHEAFᴰ (λ f g h → Eq.refl)
--   PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl) (PSHᴰFibrationUE α Pᴰ)

-- module _
--   (C : Category ℓC ℓC')
--   (ℓP : Level)
--   (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--   (ℓPᴰ : Level)
--   where
--   private
--      the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
--      the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
--      PSHᴰ = PRESHEAFᴰ C the-ℓ Cᴰ the-ℓᴰ
--      module PSHᴰ = Fibers PSHᴰ
--   module _ {P : Presheaf C the-ℓ} (Pᴰ : Presheafᴰ P Cᴰ the-ℓᴰ) where
--     private
--       module Pᴰ = PresheafᴰNotation Pᴰ

--     PSHᴰLRⱽ : LRⱽ PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
--     PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
--       where
--         module Qᴰ = PresheafᴰNotation Qᴰ

--         lrⱽue : UEⱽ
--                  ((PSHᴰ [-][-, Qᴰ ]) ×ⱽPsh
--                   reindᴰRedundPshHom
--                   (yoRecHom PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
--                   (PSHᴰ [-][-, Pᴰ ]))
--                  (λ {x} {y} f → Eq.refl)
--         lrⱽue .UEⱽ.v = Qᴰ ×ⱽPsh (α *Strict Pᴰ)
--         lrⱽue .UEⱽ.e .fst = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
--         lrⱽue .UEⱽ.e .snd = π₂ _ _
--         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .fst (αᴰ , βᴰ) =
--           ×PshIntroStrict αᴰ βᴰ
--           ⋆PshHomStrict ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictSeqIntro⁻)
--           ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Qᴰ (α *Strict Pᴰ)
--         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .fst _ =
--           ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)
--         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .snd _ =
--           makePshHomStrictPath refl

--     -- PSHᴰExpsⱽ : Exponentialsⱽ PSHᴰ
--     --   (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl) Pᴰ PSHᴰLRⱽ
--     -- PSHᴰExpsⱽ Qᴰ =
--     --   ?
--       -- UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) (expUE Qᴰ)
--       -- where
--       -- expUE : ExponentialsⱽUE PSHᴰ
--       --   (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl)
--       --   Pᴰ PSHᴰLRⱽ (λ {x} {y} f → Eq.refl)
--       -- expUE Qᴰ .UEⱽ.v = Pᴰ ⇒PshLargeStrict Qᴰ
--       -- -- Pᴰ⇒Qᴰ × Id*Pᴰ → Id*Qᴰ
--       -- expUE Qᴰ .UEⱽ.e =
--       --   {!!}
--       --   -- ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictIdIntro⁻ Pᴰ)
--       --   -- ⋆PshHomStrict appPshHomStrict Pᴰ Qᴰ
--       --   -- ⋆PshHomStrict *StrictIdIntro Qᴰ
--       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .fst αᴰ =
--       --   {!!}
--       --   -- λPshHomStrict (α *Strict Pᴰ) (α *Strict Qᴰ) αᴰ
--       --   -- ⋆PshHomStrict ⇒ⱽ*Strict→*Strict⇒ⱽ α Pᴰ Qᴰ
--       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .fst αᴰ =
--       --   {!!}
--       --   -- makePshHomStrictPath (funExt₂ λ u v →
--       --   --   Qᴰ.rectifyOut $ {!!} ∙ {!!})
--       --   -- where module Qᴰ = PresheafᴰNotation Qᴰ
--       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .snd αᴰ =
--       --   {!!}
--       --   -- makePshHomStrictPath {!!}
--       --   -- where module Qᴰ = PresheafᴰNotation Qᴰ
