{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --type-in-type #-}

module Cubical.Categories.CBPV.Instances.Demo where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma 

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.FromCat
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Instances.TransitionSystem
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets 
  renaming(SET to SETScwf)
open import Cubical.Categories.Instances.FunctorAlgebras

open Category
open Functor
open EnrichedFunctor
open EnrichedCategory
open MonoidalCategory
open NatTrans
open TSystem
open TSystem[_,_]

module duh (ℓ : Level)(F : Functor (SET ℓ)(SET ℓ)) where 

  set = (SET ℓ)
  V = PshMon.𝓟Mon set ℓ
  alg : Category ℓ-zero ℓ-zero 
  alg = AlgebrasCategory F
  E : EnrichedCategory V (ℓ-suc ℓ) 
  E = Cat→Enriched alg
  open Algebra
  open AlgebraHom
  -- Alg 

  V[_,_] = V .Hom[_,_]
  E[_,_] = E .Hom[_,_]
  selfSet = self set ℓ
  self[_,_] = selfSet .Hom[_,_]

  -- computation maps as 𝓥[Γ , UB]
  cTm' : EnrichedFunctor V E selfSet
  cTm' .F-ob (algebra B α) = LiftF ∘F (set [-, B ])
  cTm' .F-hom = adjL _ _ (
    natTrans 
      (λ Γ ((lift k) , (lift m)) → lift λ γ → k γ .carrierHom (m γ)) 
      (λ f → funExt λ _ → cong lift refl))
  cTm' .F-id = helper _ _ (makeNatTransPath refl)
  cTm' .F-seq = helper _ _ (makeNatTransPath refl)

  SetModel : CBPVModel _ _ _ _ _ _
  SetModel .fst = SETScwf ℓ
  SetModel .snd .fst = E
  SetModel .snd .snd = cTm'


module _ (ℓ : Level)(F : Functor (SET ℓ)(SET ℓ)) where 
  open import Cubical.Categories.WithFamilies.Simple.Functor
  open import Cubical.Categories.CBPV.Functor
  open import Cubical.Categories.CBPV.Instances.DefinedSubstitution hiding (F ; cTm')
  open import Cubical.Categories.Presheaf.Morphism.Alt
  open import Cubical.Categories.Presheaf.Constructions.Reindex
  open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
  open import Cubical.Categories.Enriched.NaturalTransformation.Base
  open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBaseFunctor
  open PshHom

  open duh ℓ F

  clCtx : Ctx → Type ℓ-zero 
  clCtx = Sub[ · ,_]

  Fctx : Functor SubCat (SET ℓ-zero) 
  Fctx .F-ob Γ = (clCtx Γ) , SubCat .isSetHom
  Fctx .F-hom γ x = x ⋆⟨ SubCat ⟩ γ
  Fctx .F-id = funExt (SubCat .⋆IdR)
  Fctx .F-seq γ δ = funExt λ ρ → sym (SubCat .⋆Assoc _ _ _)

  clVty : VTy → Type ℓ-zero 
  clVty = · ⊢v_

  Fvty : VTy → hSet ℓ-zero 
  Fvty A = clVty A , isSetVal

  -- NatTrans (vTm A) (SET[-, Fvty A] ∘ Fctx)
  Fvtm : {A : VTy} → PshHet Fctx (vTm A) ((SET ℓ-zero)[-, Fvty A ]) 
  Fvtm {A} .N-ob Γ v γ = subv γ v -- a closing substitution
  Fvtm {A} .N-hom Δ Γ γ v = funExt λ Δ∙ → sym (subv⋆ Δ∙ γ v )

  Fv : PreFunctor scwf (SETScwf ℓ-zero) 
  Fv .fst = Fctx
  Fv .snd .fst = Fvty
  Fv .snd .snd = Fvtm

  Fcty : CTy → Algebra F
  Fcty B = algebra B* αB where 
    B* : hSet ℓ-zero 
    B* = (· ⊢c B , isSetComp)

    αB : ⟨ F .F-ob B* ⟩ → ⟨ B* ⟩ 
    αB Fb = {!   !}
    -- IsAlgebra F (· ⊢c B , isSetComp) , {!   !}

  Fstk : EnrichedFunctor (PshMon.𝓟Mon SubCat ℓ-zero) 
    (LiftE stacks) 
    (BaseChange Fctx ℓ-zero ℓ-zero E)
  Fstk .F-ob  = Fcty
  Fstk .F-hom .N-ob Γ (lift k) = lift (lift 
    λ γ* → algebraHom (plug' (subk γ* k)) (funExt {!   !}))
  Fstk .F-hom .N-hom γ = funExt λ (lift k) → 
    cong lift (cong lift (funExt λ γ* → 
      AlgebraHom≡ F (cong plug' (subk⋆ _ _ _))))
  Fstk .F-id = makeNatTransPath (funExt λ _ → funExt λ _ → 
    cong lift (cong lift (funExt λ _ → 
      AlgebraHom≡ F refl)))
  Fstk .F-seq = makeNatTransPath (funExt λ _ → funExt λ _ → 
    cong lift (cong lift (funExt λ _ → 
      AlgebraHom≡ F (funExt λ _ → {!   !}))))

  Fctm : EnrichedNatTrans
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero) (LiftEF cTm ℓ-zero)
    (LiftSelf ℓ-zero ℓ-zero))
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero) Fstk
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero) (BaseChangeF Fctx ℓ-zero cTm')
      (BaseLiftSelf Fctx ℓ-zero)))
  Fctm .EnrichedNatTrans.E-N-ob B = adjL _ _ (
    natTrans 
      (λ Γ (tt* , lift m) → lift (lift λ γ* → subc γ* m)) 
      λ γ → funExt λ _ → cong lift (cong lift (funExt λ _ → {!   !})))
  Fctm .EnrichedNatTrans.E-N-hom = {!   !}

  Fcbpv : CBPVFunctor CBPVDefSubst SetModel
  Fcbpv .fst = Fv
  Fcbpv .snd .fst = Fstk
  Fcbpv .snd .snd = Fctm



  
  {-}
  -- no.. not a set.. but an algebra.. 
  -- with the carrier being · ⊢c B
  Fcty : CTy → hSet ℓ-zero 
  Fcty B = · ⊢c B , isSetComp

  -- plug here should be a bad code smell.. 
  -- there is an abstraction leak
  -- democratic SCwF model Set does not need such additional data for example
  -- ..no
  Fstk : EnrichedFunctor ((PshMon.𝓟Mon SubCat ℓ-zero)) (LiftE stacks) ((BaseChange Fctx ℓ-zero ℓ-zero (E ℓ-zero))) 
  Fstk .F-ob = Fcty
  Fstk .F-hom .N-ob Γ (lift k)= lift (lift λ γ* m* → plug' (subk γ* k) m*)
  Fstk .F-hom .N-hom γ = funExt λ _ → cong lift (cong lift (funExt λ _ → cong plug' {!   !}))
  Fstk .F-id = makeNatTransPath refl
  Fstk .F-seq = makeNatTransPath (funExt λ _ → funExt λ _ → cong lift (cong lift {!   !}))

  Fctm : EnrichedNatTrans
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero)
    (LiftEF
      Cubical.Categories.CBPV.Instances.DefinedSubstitution.cTm ℓ-zero)
    (LiftSelf
      ℓ-zero ℓ-zero))
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero) Fstk
    (eseq (PshMon.𝓟Mon SubCat ℓ-zero)
      (BaseChangeF
      Fctx ℓ-zero (cTm' ℓ-zero))
      (BaseLiftSelf
      Fctx ℓ-zero)))
  Fctm .EnrichedNatTrans.E-N-ob B = adjL _ _ (
    natTrans 
      (λ Γ (tt , (lift m)) → lift (lift λ γ* → subc γ* m)) 
      λ γ → funExt λ _ → cong lift (cong lift (funExt λ _ → {!   !})))
  Fctm .EnrichedNatTrans.E-N-hom = {!   !}

  F : CBPVFunctor CBPVDefSubst (SetModel ℓ-zero)
  F .fst = Fv
  F .snd .fst = Fstk
  F .snd .snd = Fctm


  -}

















  {-
  computations : ob E → ob selfSet
  computations S .F-ob Γ = 
    (⟨ Γ ⟩ → Lift ⟨ state S ⟩) , 
    isSet→ (isOfHLevelLift 2 (state S .snd))
  computations S .F-hom γ m = m ∘S γ
  computations S .F-id = refl
  computations S .F-seq _ _ = refl

  stackhom : (X Y : ob E) → 
    V[ E[ X , Y ] , self[ computations X , computations Y ] ]
  stackhom X Y = adjL _ _ (
    natTrans 
      (λ Γ (lift tsys , s) Γ∙ → lift (tsys Γ∙ .s-map (s Γ∙ .lower)) )
      λ f → funExt λ _ → funExt λ _ → refl)

  cTm : EnrichedFunctor V E selfSet
  cTm .F-ob = computations
  cTm .F-hom {X}{Y} = stackhom X Y
  cTm .F-id = 
    helper _ _ (
      makeNatTransPath (funExt λ Γ → funExt λ (tt* , s) → funExt λ Γ∙ → refl))
    --makeNatTransPath (funExt λ Γ → funExt λ tt → makePshHomPath refl)
  cTm .F-seq = 
    helper _ _ (
      makeNatTransPath (funExt λ Γ → funExt λ ((lift tsys , lift tsys'), s) → 
        funExt λ Γ∙ → refl)
    )
    -- makeNatTransPath (funExt λ Γ → funExt λ (k , k') → makePshHomPath refl)
  -}