{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning

open Category
open Functor
open Categoryᴰ
open Contravariant
open NatTrans

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓSET : Level

---- TODO: move to Functor/
--module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
--  (F : Functor C D)(G : Functor D E) where
--  ∘F^opF : (G ∘F F) ^opF ≡ (G ^opF) ∘F (F ^opF)
--  ∘F^opF = Functor≡ (λ _ → refl) (λ _ → refl)
--module _ {A : Type ℓSET}{p : A ≡ A}{ok : (λ x → x) ≡ transport p} where
--  bar : p ≡ refl
--  bar = {!!}
--module _ {A : Type ℓSET}{p : A ≡ A}{ok : (λ x → x) ≡ transport p}
--  {s : isSet A} {a : A} where
--  foo : PathP (λ i → p i) a a
--  foo = {!!}
--module _ {A : Type ℓSET}{p : A ≡ A}{a : A} where
--  rect : transport p a ≡ a
--  rect = {!!}

module _ (C : Category ℓC ℓC') ℓSET ℓSETᴰ where
  module _ (P : Presheaf C ℓSET) where
    -- TODO: this is a name clash with the other Presheafᴰ, which is different
    -- (and not a displayed presheaf in the strictest sense of "displayed X")
    Presheafᴰ : Type _
    Presheafᴰ = Presheaf (∫ᴾ P) ℓSETᴰ
  module _ {P Q : Presheaf C ℓSET} (α : P ⇒ Q) where
    ∫ᴾ⇒ : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾ⇒ .F-ob (Γ , ϕ) = Γ , (α ⟦ Γ ⟧) ϕ
    -- the paths don't matter-- we're in a hSet (but it can make goals look crazy)
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = f , funExt⁻ (sym (α .N-hom f)) ψ ∙ congS (α ⟦ Γ ⟧) p
    ∫ᴾ⇒ .F-id {x = Γ , ϕ} = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    ∫ᴾ⇒ .F-seq {x = Γ , ϕ} (f , p) (g , q) = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    module _ (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
      -- TODO: pretty sure this is right, but we should check on paper
      NatTransᴰ : Type _
      NatTransᴰ = Pᴰ ⇒ (Qᴰ ∘F (∫ᴾ⇒ ^opF))
      module _ (αᴰ : NatTransᴰ) where
        _ : ((Γ , ϕ) : Σ[ Γ ∈ C .ob ] ⟨ P ⟅ Γ ⟆ ⟩) →
          ⟨ Pᴰ  ⟅ Γ , ϕ ⟆ ⟩ → ⟨ Qᴰ ⟅ (Γ , (α ⟦ Γ ⟧) ϕ) ⟆ ⟩
        _ = αᴰ .N-ob

        _ : {(Γ , ϕ) (Δ , ψ) : (∫ᴾ P) .ob} ((f , p) : (∫ᴾ P) [ (Γ , ϕ) , (Δ , ψ) ]) →
          αᴰ ⟦ Γ , ϕ ⟧ ∘S Pᴰ ⟪ f , p ⟫
          ≡
          Qᴰ ⟪ f , _ ⟫ ∘S αᴰ ⟦ Δ , ψ ⟧
        _ = αᴰ .N-hom
  idTransᴰ : {P : Presheaf C ℓSET}{Pᴰ : Presheafᴰ P} →
    NatTransᴰ (idTrans P) Pᴰ Pᴰ
  idTransᴰ .N-ob (Γ , ϕ) = λ x → x
  idTransᴰ {P} {Pᴰ} .N-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = funExt (λ ϕᴰ →
    congS (λ x → (Pᴰ ⟪ f , x ⟫) ϕᴰ) ((P ⟅ Δ ⟆) .snd _ _ _ _))
  module _ {P Q R : Presheaf C ℓSET}(α : P ⇒ Q)(β : Q ⇒ R) where
    ∫ᴾ⇒∘ : ∫ᴾ⇒ (seqTrans α β) ≡ ∫ᴾ⇒ β ∘F ∫ᴾ⇒ α
    ∫ᴾ⇒∘ = Functor≡ (λ _ → refl) (λ _ → ΣPathP (refl , (R ⟅ _ ⟆) .snd _ _ _ _))
  module _ {P}{Q}{R}{α}{β}{Pᴰ : Presheafᴰ P}{Qᴰ : Presheafᴰ Q}{Rᴰ : Presheafᴰ R}
    (αᴰ : NatTransᴰ α Pᴰ Qᴰ)(βᴰ : NatTransᴰ β Qᴰ Rᴰ) where
    ---- abstract definition by pasting/whiskering
    --seqTransᴰ : NatTransᴰ (seqTrans α β) Pᴰ Rᴰ
    --seqTransᴰ = seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) (pathToNatTrans
    --  (sym (congS (λ x → Rᴰ ∘F x)
    --    (congS _^opF (∫ᴾ⇒∘ α β) ∙ ∘F^opF _ _) ∙ F-assoc))))
    -- whiskering definition that avoids pathToNatTrans
    seqTransᴰ'' : NatTransᴰ (seqTrans α β) Pᴰ Rᴰ
    seqTransᴰ'' = seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) (natTrans
      (λ (Γ , ϕ) βαϕᴰ → βαϕᴰ)
      (λ (f , p) → funExt (λ βαϕᴰ →
        congS (λ x → (Rᴰ ⟪ f , x ⟫) βαϕᴰ) ((R ⟅ _ ⟆) .snd _ _ _ _)))))
    ---- manual definition with less tranpsports
    --seqTransᴰ' : NatTransᴰ (seqTrans α β) Pᴰ Rᴰ
    --seqTransᴰ' .N-ob (Γ , ϕ) = βᴰ ⟦ Γ , (α ⟦ Γ ⟧) ϕ ⟧ ∘S αᴰ ⟦ Γ , ϕ ⟧
    --seqTransᴰ' .N-hom (f , p) = {!!}
    ---- apparently the pasting definition just has extremely bad definitional behavior
    --coh : seqTransᴰ .N-ob ≡ seqTransᴰ' .N-ob
    --coh = funExt (λ (Γ , ϕ) → funExt (λ ϕᴰ → {!!}))
    -- but this one is okay
    coh' : seqTransᴰ'' .N-ob ≡ λ (Γ , ϕ) → βᴰ ⟦ Γ , (α ⟦ Γ ⟧) ϕ ⟧ ∘S αᴰ ⟦ Γ , ϕ ⟧
    coh' = refl
  module _ {P}{Q}{α}{Pᴰ : Presheafᴰ P}{Qᴰ : Presheafᴰ Q} (αᴰ : NatTransᴰ α Pᴰ Qᴰ)
    (Γ : C .ob)(ϕ : ⟨ P ⟅ Γ ⟆ ⟩)(ϕᴰ : ⟨ Pᴰ ⟅ Γ , ϕ ⟆ ⟩) where
    _ : seqTrans α (idTrans Q) ≡ α
    _ = PresheafCategory C ℓSET .⋆IdR α
    p : ⟨ Qᴰ ⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆ ⟩ ≡ ⟨ Qᴰ ⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆ ⟩
    p = congS (λ x → ⟨ (Qᴰ ∘F (∫ᴾ⇒ x ^opF)) ⟅ Γ , ϕ ⟆ ⟩) (PresheafCategory C ℓSET .⋆IdR α)
    -- huhhhhhhh
    -- TODO
    q : p ≡ refl
    q = refl

    goal' : (seqTransᴰ'' αᴰ idTransᴰ) .N-ob (Γ , ϕ) ϕᴰ ≡ αᴰ .N-ob (Γ , ϕ) ϕᴰ
    goal' = {!!}
    goal : PathP (λ i → p i)
        ((seqTransᴰ'' αᴰ idTransᴰ ⟦ Γ , ϕ ⟧) ϕᴰ)
        ((αᴰ ⟦ Γ , ϕ ⟧) ϕᴰ)
    -- TODO: clean this up
    goal = toPathP (congS (λ x → transport x ((seqTransᴰ'' αᴰ idTransᴰ ⟦ Γ , ϕ ⟧) ϕᴰ)) q ∙
      transportRefl _ ∙ goal')

  PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  PRESHEAFᴰ .ob[_] = Presheafᴰ
  PRESHEAFᴰ .Hom[_][_,_] = NatTransᴰ
  PRESHEAFᴰ .idᴰ = idTransᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = seqTransᴰ''
  PRESHEAFᴰ .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
    (funExt (λ (Γ , ϕ) → funExt λ ϕᴰ → {!!}))
--Have: F-ob Qᴰ (Γ , α .N-ob Γ ϕ) .fst
--Have: F-ob Qᴰ (Γ , N-ob α Γ ϕ) .fst
  PRESHEAFᴰ .⋆IdRᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdR _))
    (funExt (λ (Γ , ϕ) → funExt (λ ϕᴰ → goal αᴰ Γ ϕ ϕᴰ)))
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makeNatTransPathP refl
    (congS (λ x → Sᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆Assoc _ _ _))
    (funExt (λ (Γ , ϕ) → funExt (λ ϕᴰ → {!!})))
  PRESHEAFᴰ .isSetHomᴰ = isSetNatTrans

  --PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  --PRESHEAFᴰ .ob[_] P = Presheafᴰ P
  --PRESHEAFᴰ .Hom[_][_,_] α Pᴰ Qᴰ = NatTransᴰ α Pᴰ Qᴰ
  --PRESHEAFᴰ .idᴰ {x = P} {p = Pᴰ} .fst Γ ϕ ϕᴰ = ϕᴰ
  --PRESHEAFᴰ .idᴰ {x = P} {p = Pᴰ} .snd {Γ = Γ} {Δ = Δ} f ϕ ϕᴰ =
  --  subst (λ x →
  --    PathP (λ i → ⟨ Pᴰ.⟅ _ , x i ϕ ⟆ ⟩)
  --    (Pᴰ.actionᴰ f _ ϕᴰ) (Pᴰ.actionᴰ f _ ϕᴰ))
  --  triv refl
  --  where
  --    module Pᴰ = PresheafᴰNotation P Pᴰ
  --    triv : refl ≡ PresheafCategory C ℓSET .id {x = P} .NatTrans.N-hom f
  --    triv = compPathRefl ∙ congS (λ x → refl ∙ x) compPathRefl
  --PRESHEAFᴰ ._⋆ᴰ_ αᴰ βᴰ = {!!}
  --PRESHEAFᴰ .⋆IdLᴰ = {!!}
  --PRESHEAFᴰ .⋆IdRᴰ = {!!}
  --PRESHEAFᴰ .⋆Assocᴰ = {!!}
  --PRESHEAFᴰ .isSetHomᴰ = {!!}
