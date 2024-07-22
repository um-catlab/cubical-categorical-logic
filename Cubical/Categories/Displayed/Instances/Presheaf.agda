{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf using (UniversalElementᴰ)

open Category
open Functor
open Categoryᴰ
open Contravariant
open NatTrans

private
  variable ℓA ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓSET : Level

module _ (C : Category ℓC ℓC') ℓSET ℓSETᴰ where
  module _ (P : Presheaf C ℓSET) where
    -- TODO: this is a name clash with the other Presheafᴰ, which is different
    -- (and not a displayed presheaf in the strictest sense of "displayed X")
    Presheafᴰ : Type _
    Presheafᴰ = Presheaf (∫ᴾ P) ℓSETᴰ
  module _ {P Q : Presheaf C ℓSET} (α : P ⇒ Q) where
    ∫ᴾ⇒ : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾ⇒ .F-ob (Γ , ϕ) = Γ , (α ⟦ Γ ⟧) ϕ
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) .fst = f
    -- the paths don't matter-- we're in a hSet
    -- (but it can make goals look crazy)
    ∫ᴾ⇒ .F-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) .snd = funExt⁻ (sym (α .N-hom f)) ψ ∙ congS (α ⟦ Γ ⟧) p
    ∫ᴾ⇒ .F-id {x = Γ , ϕ} = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    ∫ᴾ⇒ .F-seq {x = Γ , ϕ} (f , p) (g , q) = ΣPathP (refl , (Q ⟅ Γ ⟆) .snd _ _ _ _)
    module _ (Pᴰ : Presheafᴰ P)(Qᴰ : Presheafᴰ Q) where
      -- data of (α-displayed natural transformations) of displayed presheaves
      NatTransᴰ : Type _
      NatTransᴰ = Pᴰ ⇒ (Qᴰ ∘F (∫ᴾ⇒ ^opF))
      -- "tests", to verify this encoding is exactly the data we want
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
  idTransᴰ .N-ob (Γ , ϕ) = idfun _
  idTransᴰ {P} {Pᴰ} .N-hom {x = Γ , ϕ} {y = Δ , ψ} (f , p) = funExt (λ ϕᴰ →
    congS (λ x → (Pᴰ ⟪ f , x ⟫) ϕᴰ) ((P ⟅ Δ ⟆) .snd _ _ _ _))
  module _ {P}{Q}{R}{α}{β}{Pᴰ : Presheafᴰ P}{Qᴰ : Presheafᴰ Q}{Rᴰ : Presheafᴰ R}
    (αᴰ : NatTransᴰ α Pᴰ Qᴰ)(βᴰ : NatTransᴰ β Qᴰ Rᴰ) where
    -- definition by pasting, st .N-ob has desirable definitional behavior
    seqTransᴰ : NatTransᴰ (seqTrans α β) Pᴰ Rᴰ
    seqTransᴰ = seqTrans αᴰ (seqTrans (βᴰ ∘ˡ (∫ᴾ⇒ α ^opF)) fixup)
      where
      -- `((Rᴰ ∘F (∫ᴾ⇒ β ^opF)) ∘F (∫ᴾ⇒ α ^opF)) ≡
      -- (Rᴰ ∘F (∫ᴾ⇒ (seqTrans α β) ^opF))` holds, but pathToNatTrans gives
      -- .N-ob bad definitional behavior
      fixup : NatTrans
        ((Rᴰ ∘F (∫ᴾ⇒ β ^opF)) ∘F (∫ᴾ⇒ α ^opF))
        (Rᴰ ∘F (∫ᴾ⇒ (seqTrans α β) ^opF))
      fixup = natTrans (λ (Γ , ϕ) → idfun _)
        (λ (f , p) → funExt (λ βαϕᴰ →
          congS (λ x → (Rᴰ ⟪ f , x ⟫) βαϕᴰ) ((R ⟅ _ ⟆) .snd _ _ _ _)))
    -- "test"
    _ : seqTransᴰ .N-ob ≡ λ (Γ , ϕ) → βᴰ ⟦ Γ , (α ⟦ Γ ⟧) ϕ ⟧ ∘S αᴰ ⟦ Γ , ϕ ⟧
    _ = refl

  PRESHEAFᴰ : Categoryᴰ (PresheafCategory C ℓSET) _ _
  PRESHEAFᴰ .ob[_] = Presheafᴰ
  PRESHEAFᴰ .Hom[_][_,_] = NatTransᴰ
  PRESHEAFᴰ .idᴰ = idTransᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = seqTransᴰ
  PRESHEAFᴰ .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
    refl
  PRESHEAFᴰ .⋆IdRᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
    makeNatTransPathP refl
    (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdR _))
    refl
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makeNatTransPathP refl
    (congS (λ x → Sᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆Assoc _ _ _))
    refl
  PRESHEAFᴰ .isSetHomᴰ = isSetNatTrans

module _ (C : Category ℓC ℓC') {ℓS : Level} where
  open UniversalElementᴰ

  -- TODO: why ℓS but ℓ-zero?
  PRESHEAFᴰ-VerticalTerminals : VerticalTerminals (PRESHEAFᴰ C ℓ-zero _)
  PRESHEAFᴰ-VerticalTerminals P .vertexᴰ = ⊤𝓟 {ℓS = ℓS} .fst
  PRESHEAFᴰ-VerticalTerminals P .elementᴰ = tt
  PRESHEAFᴰ-VerticalTerminals P .universalᴰ .equiv-proof _ =
    uniqueExists (natTrans (λ _ _ → tt*) (λ _ → funExt (λ _ → refl)))
    (isPropUnit _ _)
    (λ _ → isSetUnit _ _)
    (λ _ _ → makeNatTransPath (funExt (λ _ → funExt (λ _ → isPropUnit* _ _))))

  -- TODO: this is basically ×𝓟, but with some extra coherences thrown in
  -- Is there a way to reuse more code?
  -- But trying to use ×𝓟 naively is giving me path issues
  module _ (P : Presheaf C ℓ-zero) (Pᴰ Pᴰ' : Presheafᴰ C ℓ-zero _ P) where
    prod : Presheafᴰ C ℓ-zero _ P
    prod = ×𝓟 {ℓS = ℓS} Pᴰ Pᴰ' .BinProduct.binProdOb
    π₁ : NatTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) (idTrans P) prod Pᴰ
    π₁ = natTrans (λ _ → fst) (λ (f , p) → funExt (λ x₁ → congS (λ x → (Pᴰ ⟪ x ⟫) (x₁ .fst)) (ΣPathP (refl , (P ⟅ _ ⟆) .snd _ _ _ _))))
    --_ : π₁ .N-hom ≡ seqTrans (×𝓟 {ℓS = ℓS} Pᴰ Pᴰ' .BinProduct.binProdPr₁) (idTransᴰ _ _ _) .N-hom
    --_ = {!!}
    π₂ : NatTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) (idTrans P) prod Pᴰ'
    π₂ = natTrans (λ _ → snd) (λ (f , p) → funExt (λ x₁ → congS (λ x → (Pᴰ' ⟪ x ⟫) (x₁ .snd)) (ΣPathP (refl , (P ⟅ _ ⟆) .snd _ _ _ _))))

  PRESHEAFᴰ-VerticalPoducts' : VerticalBinProducts (PRESHEAFᴰ C ℓ-zero _)
  PRESHEAFᴰ-VerticalPoducts' {d = P} (Pᴰ , Pᴰ') .vertexᴰ = prod P Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalPoducts' {d = P} (Pᴰ , Pᴰ') .elementᴰ .fst = seqTrans (×𝓟 {ℓS = ℓS} Pᴰ Pᴰ' .BinProduct.binProdPr₁) (idTransᴰ _ _ _)
  PRESHEAFᴰ-VerticalPoducts' {d = P} (Pᴰ , Pᴰ') .elementᴰ .snd = seqTrans (×𝓟 {ℓS = ℓS} Pᴰ Pᴰ' .BinProduct.binProdPr₂) (idTransᴰ _ _ _)
  PRESHEAFᴰ-VerticalPoducts' {d = P} (Pᴰ , Pᴰ') .universalᴰ {x = Q} {xᴰ = Qᴰ} {f = α} .equiv-proof (id∘αᴰ , id∘αᴰ') =
    uniqueExists
    {!!}
    {!!}
    {!!}
    {!!}

  PRESHEAFᴰ-VerticalPoducts : VerticalBinProducts (PRESHEAFᴰ C ℓ-zero _)
  PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .vertexᴰ = prod P Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .elementᴰ .fst = π₁ P Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .elementᴰ .snd = π₂ P Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .universalᴰ {x = Q} {xᴰ = Qᴰ} {f = α} .equiv-proof (id∘αᴰ , id∘αᴰ') =
    uniqueExists
    foo
    bar
    (λ a' → isSet× isSetNatTrans isSetNatTrans
      (seqTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) a' (PRESHEAFᴰ-VerticalPoducts (Pᴰ , Pᴰ') .elementᴰ .fst) ,
      seqTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) a' (PRESHEAFᴰ-VerticalPoducts (Pᴰ , Pᴰ') .elementᴰ .snd))
      (id∘αᴰ , id∘αᴰ'))
    λ a' p → makeNatTransPath (funExt (λ x → funExt (λ x₁ → ≡-× (funExt⁻ (funExt⁻ (sym (congS (N-ob ∘S fst) p)) x) x₁) ((funExt⁻ (funExt⁻ (sym (congS (N-ob ∘S snd) p)) x) x₁)))))
    where
    foo : NatTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) α Qᴰ (PRESHEAFᴰ-VerticalPoducts (Pᴰ , Pᴰ') .vertexᴰ)
    foo = natTrans
      (λ (Γ , ϕ) ϕᴰ → (id∘αᴰ ⟦ Γ , ϕ ⟧) ϕᴰ , (id∘αᴰ' ⟦ Γ , ϕ ⟧) ϕᴰ)
      λ {x = Γ,ϕ}{y = Δ,ψ} (f , p) → funExt (λ ϕᴰ →
        ≡-×
        (funExt⁻ (id∘αᴰ .N-hom (f , p)) ϕᴰ ∙ congS (λ x → (Pᴰ ⟪ x ⟫) ((id∘αᴰ ⟦ Γ,ϕ ⟧) ϕᴰ)) (ΣPathP (refl , ((P ⟅ _ ⟆) .snd _ _ _ _))))
        (funExt⁻ (id∘αᴰ' .N-hom (f , p)) ϕᴰ ∙ congS (λ x → (Pᴰ' ⟪ x ⟫) ((id∘αᴰ' ⟦ Γ,ϕ ⟧) ϕᴰ)) (ΣPathP (refl , ((P ⟅ _ ⟆) .snd _ _ _ _)))))
    bar : (seqTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) foo (PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .elementᴰ .fst) ,
      seqTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) foo (PRESHEAFᴰ-VerticalPoducts {d = P} (Pᴰ , Pᴰ') .elementᴰ .snd))
      ≡
      (id∘αᴰ , id∘αᴰ')
    bar = ≡-× (makeNatTransPath refl) (makeNatTransPath refl)
--Goal: NatTrans
--      (funcComp (Cubical.Categories.Presheaf.Constructions.Bob Pᴰ Pᴰ')
--       (∫ᴾ⇒ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) α ^opF))
--      (funcComp Pᴰ
--       (∫ᴾ⇒ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) (seqTrans α (idTrans P))
--        ^opF))
    --π₁ = natTrans (λ _ → fst) λ (f , p) → funExt (λ x → λ i → {!!})
    --coh : NatTrans
    --      (funcComp ((PRESHEAFᴰ-VerticalPoducts (Pᴰ , Pᴰ') .vertexᴰ))
    --       (∫ᴾ⇒ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) α ^opF))
    --      (funcComp Pᴰ
    --       (∫ᴾ⇒ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) (seqTrans α (idTrans P))
    --        ^opF))
    --coh = {!!}

    --⟨id∘αᴰ,id∘αᴰ'⟩ : NatTransᴰ C ℓ-zero (ℓ-max (ℓ-max ℓC ℓC') ℓS) α Qᴰ (PRESHEAFᴰ-VerticalPoducts (Pᴰ , Pᴰ') .vertexᴰ)
    --⟨id∘αᴰ,id∘αᴰ'⟩ = natTrans
    --  (λ (Γ , ϕ) ϕᴰ → (id∘αᴰ ⟦ Γ , ϕ ⟧) ϕᴰ , (id∘αᴰ' ⟦ Γ , ϕ ⟧) ϕᴰ)
    --  (λ {x = Γ,ϕ}{y = Δ,ψ} (f , p) → funExt (λ ϕᴰ →
    --    ≡-× (funExt⁻ (id∘αᴰ .N-hom (f , p)) ϕᴰ ∙
    --      λ i → (Pᴰ ⟪ (∫ᴾ⇒ _ _ (ℓ-max (ℓ-max ℓC ℓC') ℓS) (PresheafCategory _ _ .⋆IdR α i) ⟪ f , p ⟫) ⟫) ((id∘αᴰ ⟦ Γ,ϕ ⟧) ϕᴰ))
    --    (funExt⁻ (id∘αᴰ' .N-hom (f , p)) ϕᴰ ∙
    --      λ i → (Pᴰ' ⟪ (∫ᴾ⇒ _ _ (ℓ-max (ℓ-max ℓC ℓC') ℓS) (PresheafCategory _ _ .⋆IdR α i) ⟪ f , p ⟫) ⟫) ((id∘αᴰ' ⟦ Γ,ϕ ⟧) ϕᴰ))))
