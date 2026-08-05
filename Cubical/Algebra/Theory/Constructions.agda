-- Coproducts and tensor products of algebraic theories
module Cubical.Algebra.Theory.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinCoproduct

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Theories

private
  variable
    ℓ ℓ' ℓ'' ℓE ℓU ℓv ℓw ℓX : Level
    ℓ1 ℓ2 : Level

open AlgTheorySig
open AlgTheoryEqns using (eqns; vars; lhs; rhs)
open SigMap
open SetSig

module _ {ℓ1 ℓ2} (σ : AlgTheorySig ℓ1 ℓ') (τ : AlgTheorySig ℓ2 ℓ') where
  _⊕Sig_ : AlgTheorySig (ℓ-max ℓ1 ℓ2) ℓ'
  _⊕Sig_ .ops = σ .ops ⊎ τ .ops
  _⊕Sig_ .arities (inl f) = σ .arities f
  _⊕Sig_ .arities (inr g) = τ .arities g

  inlSig : SigMap σ _⊕Sig_
  inlSig .onOps = inl
  inlSig .unArity op a = a

  inrSig : SigMap τ _⊕Sig_
  inrSig .onOps = inr
  inrSig .unArity op a = a

module _ {σ τ υ : AlgTheorySig ℓ ℓ'}
  (F : SigMap σ υ) (G : SigMap τ υ) where
  [_,_]Sig : SigMap (σ ⊕Sig τ) υ
  [_,_]Sig .onOps (inl f) = F .onOps f
  [_,_]Sig .onOps (inr g) = G .onOps g
  [_,_]Sig .unArity (inl f) a = F .unArity f a
  [_,_]Sig .unArity (inr g) a = G .unArity g a

  ⊕Sigβl : (inlSig σ τ ⋆SigMap [_,_]Sig) ≡ F
  ⊕Sigβl = refl

  ⊕Sigβr : (inrSig σ τ ⋆SigMap [_,_]Sig) ≡ G
  ⊕Sigβr = refl

module _ {σ τ υ : AlgTheorySig ℓ ℓ'} where
  ⊕SigMapIso : Iso (SigMap (σ ⊕Sig τ) υ) (SigMap σ υ × SigMap τ υ)
  ⊕SigMapIso .Iso.fun H =
    (inlSig σ τ ⋆SigMap H) , (inrSig σ τ ⋆SigMap H)
  ⊕SigMapIso .Iso.inv (F , G) = [ F , G ]Sig
  ⊕SigMapIso .Iso.sec _ = refl
  ⊕SigMapIso .Iso.ret H i .onOps (inl f) = H .onOps (inl f)
  ⊕SigMapIso .Iso.ret H i .onOps (inr g) = H .onOps (inr g)
  ⊕SigMapIso .Iso.ret H i .unArity (inl f) a = H .unArity (inl f) a
  ⊕SigMapIso .Iso.ret H i .unArity (inr g) a = H .unArity (inr g) a

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (τeq : AlgTheoryEqns τ ℓE ℓv) where

  _⊕Eqns_ : AlgTheoryEqns (σ ⊕Sig τ) (ℓ-max ℓ'' ℓE) ℓv
  _⊕Eqns_ .eqns = σeq .eqns ⊎ τeq .eqns
  _⊕Eqns_ .vars (inl e) = σeq .vars e
  _⊕Eqns_ .vars (inr e) = τeq .vars e
  _⊕Eqns_ .lhs (inl e) = mapTm (inlSig σ τ) (σeq .lhs e)
  _⊕Eqns_ .lhs (inr e) = mapTm (inrSig σ τ) (τeq .lhs e)
  _⊕Eqns_ .rhs (inl e) = mapTm (inlSig σ τ) (σeq .rhs e)
  _⊕Eqns_ .rhs (inr e) = mapTm (inrSig σ τ) (τeq .rhs e)

  pInl : PresEqns σeq _⊕Eqns_ ℓX (inlSig σ τ)
  pInl X B e ρ =
    TmRec-mapTm (inlSig σ τ) (Alg.⟨_⟩⟦_⟧op B) ρ (σeq .lhs e)
    ∙ Alg.⟦_⟧eqn B (inl e) ρ
    ∙ sym (TmRec-mapTm (inlSig σ τ) (Alg.⟨_⟩⟦_⟧op B) ρ (σeq .rhs e))

  pInr : PresEqns τeq _⊕Eqns_ ℓX (inrSig σ τ)
  pInr X B e ρ =
    TmRec-mapTm (inrSig σ τ) (Alg.⟨_⟩⟦_⟧op B) ρ (τeq .lhs e)
    ∙ Alg.⟦_⟧eqn B (inr e) ρ
    ∙ sym (TmRec-mapTm (inrSig σ τ) (Alg.⟨_⟩⟦_⟧op B) ρ (τeq .rhs e))

module _ {σ τ υ : AlgTheorySig ℓ ℓ'}
  {σeq : AlgTheoryEqns σ ℓ'' ℓv} {τeq : AlgTheoryEqns τ ℓE ℓv}
  {υeq : AlgTheoryEqns υ ℓU ℓv}
  {F : SigMap σ υ} {G : SigMap τ υ}
  (pF : PresEqns σeq υeq ℓX F) (pG : PresEqns τeq υeq ℓX G) where

  [_,_]Eqns : PresEqns (σeq ⊕Eqns τeq) υeq ℓX [ F , G ]Sig
  [_,_]Eqns X B (inl e) ρ =
    sym (TmRec-mapTm (inlSig σ τ) β ρ (σeq .lhs e))
    ∙ pF X B e ρ
    ∙ TmRec-mapTm (inlSig σ τ) β ρ (σeq .rhs e)
    where β = reOps [ F , G ]Sig (Alg.⟨_⟩⟦_⟧op B)
  [_,_]Eqns X B (inr e) ρ =
    sym (TmRec-mapTm (inrSig σ τ) β ρ (τeq .lhs e))
    ∙ pG X B e ρ
    ∙ TmRec-mapTm (inrSig σ τ) β ρ (τeq .rhs e)
    where β = reOps [ F , G ]Sig (Alg.⟨_⟩⟦_⟧op B)

module _ (σ τ : SetSig ℓ ℓ') where
  _⊕SetSig_ : SetSig ℓ ℓ'
  _⊕SetSig_ .sig = σ .sig ⊕Sig τ .sig
  _⊕SetSig_ .isSetOps = isSet⊎ (σ .isSetOps) (τ .isSetOps)
  _⊕SetSig_ .isSetArities (inl f) = σ .isSetArities f
  _⊕SetSig_ .isSetArities (inr g) = τ .isSetArities g

  SIGBinCoproduct : BinCoproduct (SIG ℓ ℓ') σ τ
  SIGBinCoproduct .BinCoproduct.binCoprodOb = _⊕SetSig_
  SIGBinCoproduct .BinCoproduct.binCoprodInj₁ = inlSig (σ .sig) (τ .sig)
  SIGBinCoproduct .BinCoproduct.binCoprodInj₂ = inrSig (σ .sig) (τ .sig)
  SIGBinCoproduct .BinCoproduct.univProp {z = υ} F G .fst =
    [ F , G ]Sig , refl , refl
  SIGBinCoproduct .BinCoproduct.univProp {z = υ} F G .snd (H , p , q) =
    Σ≡Prop
      (λ _ → isProp× (isSetSigMap (υ .isSetOps) (σ .isSetArities) _ _)
                     (isSetSigMap (υ .isSetOps) (τ .isSetArities) _ _))
      (cong₂ (λ F' G' → [ F' , G' ]Sig) (sym p) (sym q)
       ∙ ⊕SigMapIso .Iso.ret H)

module _ (ℓX : Level) {σ τ : SetSig ℓ ℓ'}
  (σeq : AlgTheoryEqns (σ .sig) ℓ'' ℓv)
  (τeq : AlgTheoryEqns (τ .sig) ℓ'' ℓv) where

  private
    module TH = Category (THEORY ℓ ℓ' ℓ'' ℓv ℓX)

  ⊕Theory : TH.ob
  ⊕Theory = (σ ⊕SetSig τ) , (σeq ⊕Eqns τeq)

  inlTheory : TH.Hom[ (σ , σeq) , ⊕Theory ]
  inlTheory = inlSig (σ .sig) (τ .sig) , pInl σeq τeq

  inrTheory : TH.Hom[ (τ , τeq) , ⊕Theory ]
  inrTheory = inrSig (σ .sig) (τ .sig) , pInr σeq τeq

  THEORYBinCoproduct
    : BinCoproduct (THEORY ℓ ℓ' ℓ'' ℓv ℓX) (σ , σeq) (τ , τeq)
  THEORYBinCoproduct .BinCoproduct.binCoprodOb = ⊕Theory
  THEORYBinCoproduct .BinCoproduct.binCoprodInj₁ = inlTheory
  THEORYBinCoproduct .BinCoproduct.binCoprodInj₂ = inrTheory
  THEORYBinCoproduct .BinCoproduct.univProp
    {z = υ , υeq} (F , pF) (G , pG) .fst =
    ([ F , G ]Sig , [ pF , pG ]Eqns)
    , Σ≡Prop (λ f → isPropPresEqns {σeq = σeq} {τeq = υeq} {F = f}) refl
    , Σ≡Prop (λ f → isPropPresEqns {σeq = τeq} {τeq = υeq} {F = f}) refl
  THEORYBinCoproduct .BinCoproduct.univProp
    {z = υ , υeq} (F , pF) (G , pG) .snd ((H , pH) , p , q) =
    Σ≡Prop
      (λ f → isProp×
        (TH.isSetHom {x = σ , σeq} {y = υ , υeq} _ _)
        (TH.isSetHom {x = τ , τeq} {y = υ , υeq} _ _))
      (Σ≡Prop
        (λ f → isPropPresEqns
          {σeq = σeq ⊕Eqns τeq} {τeq = υeq} {F = f})
        (cong₂ (λ F' G' → [ F' , G' ]Sig)
          (sym (cong fst p)) (sym (cong fst q))
         ∙ ⊕SigMapIso .Iso.ret H))

module _ {σ : AlgTheorySig ℓ ℓ'} {σeq : AlgTheoryEqns σ ℓ'' ℓv}
  {X : Type ℓX} (isSetX : isSet X) where

  AlgExt : {B C : Alg σeq X}
    → Alg.⟨_⟩⟦_⟧op B ≡ Alg.⟨_⟩⟦_⟧op C → B ≡ C
  AlgExt p i .Alg.⟨_⟩⟦_⟧op = p i
  AlgExt {B} {C} p i .Alg.⟦_⟧eqn =
    isProp→PathP
      (λ j → isPropΠ2 λ e ρ →
        isSetX (TmRec (p j) ρ (σeq .lhs e)) (TmRec (p j) ρ (σeq .rhs e)))
      (Alg.⟦_⟧eqn B) (Alg.⟦_⟧eqn C) i

module _ {σ : AlgTheorySig ℓ1 ℓ'} {τ : AlgTheorySig ℓ2 ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) (τeq : AlgTheoryEqns τ ℓE ℓv)
  (X : hSet ℓX) where

  ⊕AlgOps : Alg σeq ⟨ X ⟩ → Alg τeq ⟨ X ⟩
    → ∀ (op : (σ ⊕Sig τ) .ops) → ((σ ⊕Sig τ) .arities op → ⟨ X ⟩) → ⟨ X ⟩
  ⊕AlgOps Bσ Bτ (inl f) = Alg.⟨_⟩⟦_⟧op Bσ f
  ⊕AlgOps Bσ Bτ (inr g) = Alg.⟨_⟩⟦_⟧op Bτ g

  ⊕Alg : Alg σeq ⟨ X ⟩ → Alg τeq ⟨ X ⟩ → Alg (σeq ⊕Eqns τeq) ⟨ X ⟩
  ⊕Alg Bσ Bτ .Alg.⟨_⟩⟦_⟧op = ⊕AlgOps Bσ Bτ
  ⊕Alg Bσ Bτ .Alg.⟦_⟧eqn (inl e) ρ =
    sym (TmRec-mapTm (inlSig σ τ) (⊕AlgOps Bσ Bτ) ρ (σeq .lhs e))
    ∙ Alg.⟦_⟧eqn Bσ e ρ
    ∙ TmRec-mapTm (inlSig σ τ) (⊕AlgOps Bσ Bτ) ρ (σeq .rhs e)
  ⊕Alg Bσ Bτ .Alg.⟦_⟧eqn (inr e) ρ =
    sym (TmRec-mapTm (inrSig σ τ) (⊕AlgOps Bσ Bτ) ρ (τeq .lhs e))
    ∙ Alg.⟦_⟧eqn Bτ e ρ
    ∙ TmRec-mapTm (inrSig σ τ) (⊕AlgOps Bσ Bτ) ρ (τeq .rhs e)

  ⊕AlgIso : Iso (Alg (σeq ⊕Eqns τeq) ⟨ X ⟩)
                (Alg σeq ⟨ X ⟩ × Alg τeq ⟨ X ⟩)
  ⊕AlgIso .Iso.fun B =
    reindexModel (pInl σeq τeq) X B , reindexModel (pInr σeq τeq) X B
  ⊕AlgIso .Iso.inv (Bσ , Bτ) = ⊕Alg Bσ Bτ
  ⊕AlgIso .Iso.sec (Bσ , Bτ) =
    ΣPathP (AlgExt (X .snd) refl , AlgExt (X .snd) refl)
  ⊕AlgIso .Iso.ret B =
    AlgExt (X .snd) (funExt λ { (inl f) → refl ; (inr g) → refl })

module _ {υ : AlgTheorySig ℓ ℓ'} where
  renTm : {V : Type ℓv} {W : Type ℓw} → (V → W) → Tm υ V → Tm υ W
  renTm f (var v) = var (f v)
  renTm f (node op ts) = node op (λ a → renTm f (ts a))

  TmRec-renTm : {X : Type ℓX}
    (α : ∀ (op : υ .ops) → (υ .arities op → X) → X)
    {V : Type ℓv} {W : Type ℓw} (ρ : W → X) (f : V → W) (M : Tm υ V)
    → TmRec α (ρ ∘ f) M ≡ TmRec α ρ (renTm f M)
  TmRec-renTm α ρ f (var v) = refl
  TmRec-renTm α ρ f (node op ts) =
    cong (α op) (funExt λ a → TmRec-renTm α ρ f (ts a))

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv)
  {X : Type ℓX} (B : Alg σeq X) {A : Type ℓw} where
  private module B = Alg B

  powerOps : ∀ (op : σ .ops) → (σ .arities op → (A → X)) → (A → X)
  powerOps op x a = B.⟨ op ⟩⟦ (λ i → x i a) ⟧op

  TmRec-power : {V : Type ℓv} (ρ : V → (A → X)) (M : Tm σ V) (a : A)
    → TmRec powerOps ρ M a ≡ TmRec B.⟨_⟩⟦_⟧op (λ v → ρ v a) M
  TmRec-power ρ (var v) a = refl
  TmRec-power ρ (node op ts) a =
    cong B.⟨ op ⟩⟦_⟧op (funExt λ i → TmRec-power ρ (ts i) a)

  powerAlg : Alg σeq (A → X)
  powerAlg .Alg.⟨_⟩⟦_⟧op = powerOps
  powerAlg .Alg.⟦_⟧eqn e ρ = funExt λ a →
    TmRec-power ρ (σeq .lhs e) a
    ∙ B.⟦ e ⟧eqn (λ v → ρ v a)
    ∙ sym (TmRec-power ρ (σeq .rhs e) a)

module _ (ℓw : Level) {σ τ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' (ℓ-max ℓw ℓ'))
  (τeq : AlgTheoryEqns τ ℓE (ℓ-max ℓw ℓ')) where

  ⊗Eqns : AlgTheoryEqns (σ ⊕Sig τ)
    (ℓ-max (ℓ-max ℓ'' ℓE) ℓ) (ℓ-max ℓw ℓ')
  ⊗Eqns .eqns = σeq .eqns ⊎ (τeq .eqns ⊎ (σ .ops × τ .ops))
  ⊗Eqns .vars (inl e) = Lift ℓ' (σeq .vars e)
  ⊗Eqns .vars (inr (inl e)) = Lift ℓ' (τeq .vars e)
  ⊗Eqns .vars (inr (inr (f , g))) =
    Lift ℓw (σ .arities f × τ .arities g)
  ⊗Eqns .lhs (inl e) = renTm lift (mapTm (inlSig σ τ) (σeq .lhs e))
  ⊗Eqns .lhs (inr (inl e)) =
    renTm lift (mapTm (inrSig σ τ) (τeq .lhs e))
  ⊗Eqns .lhs (inr (inr (f , g))) =
    node (inl f) (λ a → node (inr g) (λ b → var (lift (a , b))))
  ⊗Eqns .rhs (inl e) = renTm lift (mapTm (inlSig σ τ) (σeq .rhs e))
  ⊗Eqns .rhs (inr (inl e)) =
    renTm lift (mapTm (inrSig σ τ) (τeq .rhs e))
  ⊗Eqns .rhs (inr (inr (f , g))) =
    node (inr g) (λ b → node (inl f) (λ a → var (lift (a , b))))

  pInl⊗ : PresEqns σeq ⊗Eqns ℓX (inlSig σ τ)
  pInl⊗ X B e ρ =
    TmRec-mapTm (inlSig σ τ) α ρ (σeq .lhs e)
    ∙ TmRec-renTm α ρ' lift (mapTm (inlSig σ τ) (σeq .lhs e))
    ∙ Alg.⟦_⟧eqn B (inl e) ρ'
    ∙ sym (TmRec-renTm α ρ' lift (mapTm (inlSig σ τ) (σeq .rhs e)))
    ∙ sym (TmRec-mapTm (inlSig σ τ) α ρ (σeq .rhs e))
    where
      α = Alg.⟨_⟩⟦_⟧op B
      ρ' : ⊗Eqns .vars (inl e) → ⟨ X ⟩
      ρ' = ρ ∘ lower

  pInr⊗ : PresEqns τeq ⊗Eqns ℓX (inrSig σ τ)
  pInr⊗ X B e ρ =
    TmRec-mapTm (inrSig σ τ) α ρ (τeq .lhs e)
    ∙ TmRec-renTm α ρ' lift (mapTm (inrSig σ τ) (τeq .lhs e))
    ∙ Alg.⟦_⟧eqn B (inr (inl e)) ρ'
    ∙ sym (TmRec-renTm α ρ' lift (mapTm (inrSig σ τ) (τeq .rhs e)))
    ∙ sym (TmRec-mapTm (inrSig σ τ) α ρ (τeq .rhs e))
    where
      α = Alg.⟨_⟩⟦_⟧op B
      ρ' : ⊗Eqns .vars (inr (inl e)) → ⟨ X ⟩
      ρ' = ρ ∘ lower

  ⊕→⊗ : PresEqns (σeq ⊕Eqns τeq) ⊗Eqns ℓX idSigMap
  ⊕→⊗ X B (inl e) ρ =
    TmRec-renTm α (ρ ∘ lower) lift (mapTm (inlSig σ τ) (σeq .lhs e))
    ∙ Alg.⟦_⟧eqn B (inl e) (ρ ∘ lower)
    ∙ sym (TmRec-renTm α (ρ ∘ lower) lift
        (mapTm (inlSig σ τ) (σeq .rhs e)))
    where α = Alg.⟨_⟩⟦_⟧op B
  ⊕→⊗ X B (inr e) ρ =
    TmRec-renTm α (ρ ∘ lower) lift (mapTm (inrSig σ τ) (τeq .lhs e))
    ∙ Alg.⟦_⟧eqn B (inr (inl e)) (ρ ∘ lower)
    ∙ sym (TmRec-renTm α (ρ ∘ lower) lift
        (mapTm (inrSig σ τ) (τeq .rhs e)))
    where α = Alg.⟨_⟩⟦_⟧op B

module _ (ℓw : Level) {σ τ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' (ℓ-max ℓw ℓ'))
  (τeq : AlgTheoryEqns τ ℓE (ℓ-max ℓw ℓ'))
  (X : hSet ℓX) where

  ⊗σModel : Alg (⊗Eqns ℓw σeq τeq) ⟨ X ⟩ → Alg σeq ⟨ X ⟩
  ⊗σModel = reindexModel (pInl⊗ ℓw σeq τeq) X

  ⊗τModel : Alg (⊗Eqns ℓw σeq τeq) ⟨ X ⟩ → Alg τeq ⟨ X ⟩
  ⊗τModel = reindexModel (pInr⊗ ℓw σeq τeq) X

  ⊗opHomo : (B : Alg (⊗Eqns ℓw σeq τeq) ⟨ X ⟩) (f : σ .ops)
    → Homo τeq (Alg.⟨_⟩⟦_⟧op (⊗σModel B) f)
        (powerAlg τeq (⊗τModel B)) (⊗τModel B)
  ⊗opHomo B f .Homo.op-hom g x y eq =
    cong (Alg.⟨_⟩⟦_⟧op B (inl f)) eq
    ∙ Alg.⟦_⟧eqn B (inr (inr (f , g)))
        (λ p → x (p .lower .snd) (p .lower .fst))

  ⊗Model : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓE))
                       (ℓ-max (ℓ-max ℓw ℓ') ℓX))
  ⊗Model = Σ[ BB ∈ (Alg σeq ⟨ X ⟩ × Alg τeq ⟨ X ⟩) ]
    (∀ (f : σ .ops)
      → Homo τeq (Alg.⟨_⟩⟦_⟧op (BB .fst) f)
          (powerAlg τeq (BB .snd)) (BB .snd))

  ⊗Alg : ⊗Model → Alg (⊗Eqns ℓw σeq τeq) ⟨ X ⟩
  ⊗Alg ((Bσ , Bτ) , h) .Alg.⟨_⟩⟦_⟧op = ⊕AlgOps σeq τeq X Bσ Bτ
  ⊗Alg ((Bσ , Bτ) , h) .Alg.⟦_⟧eqn (inl e) ρ =
    sym (TmRec-renTm α ρ lift (mapTm (inlSig σ τ) (σeq .lhs e)))
    ∙ sym (TmRec-mapTm (inlSig σ τ) α (ρ ∘ lift) (σeq .lhs e))
    ∙ Alg.⟦_⟧eqn Bσ e (ρ ∘ lift)
    ∙ TmRec-mapTm (inlSig σ τ) α (ρ ∘ lift) (σeq .rhs e)
    ∙ TmRec-renTm α ρ lift (mapTm (inlSig σ τ) (σeq .rhs e))
    where α = ⊕AlgOps σeq τeq X Bσ Bτ
  ⊗Alg ((Bσ , Bτ) , h) .Alg.⟦_⟧eqn (inr (inl e)) ρ =
    sym (TmRec-renTm α ρ lift (mapTm (inrSig σ τ) (τeq .lhs e)))
    ∙ sym (TmRec-mapTm (inrSig σ τ) α (ρ ∘ lift) (τeq .lhs e))
    ∙ Alg.⟦_⟧eqn Bτ e (ρ ∘ lift)
    ∙ TmRec-mapTm (inrSig σ τ) α (ρ ∘ lift) (τeq .rhs e)
    ∙ TmRec-renTm α ρ lift (mapTm (inrSig σ τ) (τeq .rhs e))
    where α = ⊕AlgOps σeq τeq X Bσ Bτ
  ⊗Alg ((Bσ , Bτ) , h) .Alg.⟦_⟧eqn (inr (inr (f , g))) ρ =
    Homo.op-hom' (h f) g (λ b a → ρ (lift (a , b)))

  ⊗AlgIso : Iso (Alg (⊗Eqns ℓw σeq τeq) ⟨ X ⟩) ⊗Model
  ⊗AlgIso .Iso.fun B = (⊗σModel B , ⊗τModel B) , ⊗opHomo B
  ⊗AlgIso .Iso.inv = ⊗Alg
  ⊗AlgIso .Iso.sec ((Bσ , Bτ) , h) =
    Σ≡Prop (λ _ → isPropΠ λ _ → isPropHomo τeq (X .snd))
      (ΣPathP (AlgExt (X .snd) refl , AlgExt (X .snd) refl))
  ⊗AlgIso .Iso.ret B =
    AlgExt (X .snd) (funExt λ { (inl f) → refl ; (inr g) → refl })
