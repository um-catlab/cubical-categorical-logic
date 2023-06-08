{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.UnderlyingGraph where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma
open import Cubical.Categories.Isomorphism

open import Cubical.Data.Graph.Properties

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓg ℓg' ℓh ℓh' : Level

open Category
open isIso
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

-- Underlying graph of a category
Ugr : ∀ {ℓc ℓc'} (𝓒 : Category ℓc ℓc') → Graph ℓc ℓc'
Ugr 𝓒 .Node = 𝓒 .ob
Ugr 𝓒 .Edge = 𝓒 .Hom[_,_]

Uhom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : Category ℓc ℓc'}
       {𝓓 : Category ℓd ℓd'} (F : Functor 𝓒 𝓓)
     → GraphHom (Ugr 𝓒) (Ugr 𝓓)
Uhom F ._$g_ = Functor.F-ob F
Uhom F ._<$g>_ = Functor.F-hom F

module _ (G : Graph ℓg ℓg') (𝓒 : Category ℓc ℓc') where
  Interp : Type _
  Interp = GraphHom G (Ugr 𝓒)

  InterpTrans : Interp → Interp → Type _
  InterpTrans ı ı' =
    Σ[ f ∈ (∀ v → 𝓒 [ ı $g v , ı' $g v ])]
    (∀ {v}{w}(e : G .Edge v w) → f w ∘⟨ 𝓒 ⟩ (ı <$g> e) ≡ ı' <$g> e ∘⟨ 𝓒 ⟩ f v)

  isInterpIso : {ı ı' : Interp} → InterpTrans ı ı' → Type (ℓ-max ℓg ℓc')
  isInterpIso α = ∀ v → isIso 𝓒 (α .fst v)

  InterpIso : Interp → Interp → Type _
  InterpIso ı ı' = Σ (InterpTrans ı ı') isInterpIso

  idInterpIso : {ı : Interp} → InterpIso ı ı
  idInterpIso .fst .fst v = 𝓒 .id
  idInterpIso .fst .snd e = 𝓒 .⋆IdR _ ∙ sym (𝓒 .⋆IdL _)
  idInterpIso .snd v = idCatIso .snd

  -- if 𝓒 is univalent, this should be an equivalence
  pathToInterpIso : {ı ı' : Interp} → ı ≡ ı' → InterpIso ı ı'
  pathToInterpIso {ı}{ı'} p = transport (λ i → InterpIso ı (p i)) idInterpIso

  isIsoInterpIso : {ı ı' : Interp} (α : InterpIso ı ı') →
                   ∀ v → CatIso 𝓒 (ı $g v) (ı' $g v)
  isIsoInterpIso α v = (α .fst .fst v) , (α .snd v)

  _∘InterpIso_ : {ı ı' ı'' : Interp} →
                 InterpIso ı' ı'' → InterpIso ı ı' → InterpIso ı ı''
  (α ∘InterpIso β) .fst .fst v = α .fst .fst v ∘⟨ 𝓒 ⟩ β .fst .fst v
  (α ∘InterpIso β) .fst .snd e =
    sym (𝓒 .⋆Assoc _ _ _)
    ∙ cong (comp' 𝓒 (α .fst .fst _)) (β .fst .snd e)
    ∙ 𝓒 .⋆Assoc _ _ _
    ∙ cong (seq' 𝓒 (β .fst .fst _)) (α .fst .snd e)
    ∙ sym (𝓒 .⋆Assoc _ _ _)
  (α ∘InterpIso β) .snd v =
    compIso (isIsoInterpIso α v) (isIsoInterpIso β v) .snd

  module InterpReasoning (ı : Interp) (ı' : Interp) (α : InterpIso ı ı') where
    open isIso
    sqRL : ∀ {v w} → {e : G .Edge v w}
         → ı <$g> e ≡ α .fst .fst v ⋆⟨ 𝓒 ⟩ ı' <$g> e ⋆⟨ 𝓒 ⟩ α .snd w .inv
    sqRL {v}{w}{e} = invMoveR (isIso→areInv (α .snd w)) (α .fst .snd e)

    -- copied from NaturalTransformation.Base
    sqLL : ∀ {v w} → {e : G .Edge v w}
         → ı' <$g> e ⋆⟨ 𝓒 ⟩ α .snd w .inv ≡ α .snd v .inv ⋆⟨ 𝓒 ⟩ (ı <$g> e)
    sqLL {v}{w}{e} =
      invMoveL (isIso→areInv (α .snd v)) (sym (sqRL ∙ 𝓒 .⋆Assoc _ _ _))

module _ {G : Graph ℓg ℓg'}{𝓒 : Category ℓc ℓc'} where
  private
    ITrans = InterpTrans G 𝓒
    IIso = InterpIso G 𝓒

  InterpTrans≡ : ∀ {ı ı'}{α β : ITrans ı ı'} →
                 (∀ v →  α .fst v ≡ β .fst v) → α ≡ β
  InterpTrans≡ p =
    Σ≡Prop (λ x → isPropImplicitΠ
              (λ _ → isPropImplicitΠ
                λ _ → isPropΠ (λ e → 𝓒 .isSetHom _ _))) (funExt p)



  InterpIso≡ : ∀ {ı ı'}{α β : IIso ı ı'} →
               (∀ v → α .fst .fst v ≡ β .fst .fst v) → α ≡ β
  InterpIso≡ p = Σ≡Prop (λ x → isPropΠ (λ x → isPropIsIso _)) (InterpTrans≡ p)

seqInterpIso : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' ı'' : Interp G 𝓒}
             → InterpIso G 𝓒 ı ı'
             → InterpIso G 𝓒 ı' ı''
             → InterpIso G 𝓒 ı ı''
seqInterpIso α α' = _∘InterpIso_ _ _ α' α

_⋆InterpIso_ = seqInterpIso

seqInterpIsoIdR : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' : Interp G 𝓒}
             → (α : InterpIso G 𝓒 ı ı')
             → (seqInterpIso α (idInterpIso _ _)) ≡ α
seqInterpIsoIdR {𝓒 = 𝓒} α = InterpIso≡ λ v → 𝓒 .⋆IdR _

seqInterpIsoIdL : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' : Interp G 𝓒}
             → (α : InterpIso G 𝓒 ı ı')
             → (seqInterpIso (idInterpIso _ _) α) ≡ α
seqInterpIsoIdL {𝓒 = 𝓒} α = InterpIso≡ λ v → 𝓒 .⋆IdL _

seqInterpIsoAssoc : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
                  → {ı ı' ı'' ı''' : Interp G 𝓒}
                  → (α : InterpIso G 𝓒 ı ı')
                  → (α' : InterpIso G 𝓒 ı' ı'')
                  → (α'' : InterpIso G 𝓒 ı'' ı''')
                  → seqInterpIso (seqInterpIso α α') α'' ≡
                    seqInterpIso α (seqInterpIso α' α'')
seqInterpIsoAssoc {𝓒 = 𝓒} α α' α'' = InterpIso≡ λ v → 𝓒 .⋆Assoc _ _ _

symInterpIso : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' : Interp G 𝓒}
             → InterpIso G 𝓒 ı ı'
             → InterpIso G 𝓒 ı' ı
symInterpIso α .fst .fst v = α .snd v .inv
symInterpIso α .fst .snd e = InterpReasoning.sqLL _ _ _ _ α
symInterpIso α .snd v .inv = α .fst .fst v
symInterpIso α .snd v .sec = α .snd v .ret
symInterpIso α .snd v .ret = α .snd v .sec

symInterpIsoInvl : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' : Interp G 𝓒}
             → (α : InterpIso G 𝓒 ı ı')
             → seqInterpIso (symInterpIso α) α ≡ idInterpIso _ _
symInterpIsoInvl α = InterpIso≡ (λ v → α .snd v .sec)

symInterpIsoInvr : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
             → {ı ı' : Interp G 𝓒}
             → (α : InterpIso G 𝓒 ı ı')
             → seqInterpIso α (symInterpIso α) ≡ idInterpIso _ _
symInterpIsoInvr α = InterpIso≡ (λ v → α .snd v .ret)

symInterpIsoId : ∀ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'} → {ı : Interp G 𝓒}
               → symInterpIso {𝓒 = 𝓒} (idInterpIso _ _ {ı}) ≡
                 idInterpIso _ _ {ı}
symInterpIsoId = InterpIso≡ (λ v → refl)

_⋆Interp_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : Category ℓc ℓc'}
              {𝓓 : Category ℓd ℓd'}
              (ı : Interp G 𝓒)
              (F : Functor 𝓒 𝓓)
              → Interp G 𝓓
(ı ⋆Interp F) ._$g_ x = Functor.F-ob F (ı $g x)
(ı ⋆Interp F) ._<$g>_ e = Functor.F-hom F (ı <$g> e)

_∘Interp_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : Category ℓc ℓc'}
              {𝓓 : Category ℓd ℓd'}
              (F : Functor 𝓒 𝓓)
              (ı : Interp G 𝓒)
              → Interp G 𝓓
F ∘Interp ı = ı ⋆Interp F

module _ {G : Graph ℓg ℓg'}{H : Graph ℓh ℓh'} {𝓒 : Category ℓc ℓc'} where
  -- homogeneous whiskering of an interpiso with a graph homomorphism
  _∘ˡInterp_ : ∀ {ı ı' : Interp H 𝓒} (α : InterpIso H 𝓒 ı ı')
            (ϕ : GraphHom G H)
             → InterpIso G 𝓒 (ı ∘GrHom ϕ) (ı' ∘GrHom ϕ)
  (α ∘ˡInterp ϕ) .fst .fst v = α .fst .fst (ϕ $g v)
  (α ∘ˡInterp ϕ) .fst .snd e = α .fst .snd (ϕ <$g> e)
  (α ∘ˡInterp ϕ) .snd v = α .snd (ϕ $g v)

module _ {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'} where
  -- "heterogeneous" whiskering of an interprIso with a functor
  _⊙ʳInterp_ : ∀ (K : Functor 𝓒 𝓓) {ı ı' : Interp G 𝓒} →
    (α : InterpIso G 𝓒 ı ı')
        → InterpIso G 𝓓 (K ∘Interp ı) (K ∘Interp ı')
  (K ⊙ʳInterp α) .fst .fst v = K ⟪ α .fst .fst v ⟫
  (K ⊙ʳInterp α) .fst .snd e = preserveCommF {F = K}(α .fst .snd e)
  (K ⊙ʳInterp α) .snd v = preserveIsosF {F = K} (isIsoInterpIso _ _ α v) .snd

  ⊙ʳInterp-IdIso : ∀ {K : Functor 𝓒 𝓓}{ı : Interp G 𝓒} →
    K ⊙ʳInterp (idInterpIso _ _ {ı}) ≡ idInterpIso _ _
  ⊙ʳInterp-IdIso {K} = InterpIso≡ λ v → K .F-id

  ⊙ʳInterp-CompIso : ∀ {K : Functor 𝓒 𝓓}{ı ı' ı'' : Interp G 𝓒}
                     (α : InterpIso _ _ ı ı') (β : InterpIso _ _ ı' ı'')
                   → K ⊙ʳInterp (α ⋆InterpIso β) ≡
                       (K ⊙ʳInterp α) ⋆InterpIso (K ⊙ʳInterp β)
  ⊙ʳInterp-CompIso {K} α β = InterpIso≡ λ v → K .F-seq _ _

  -- "heterogeneous" whiskering of an interpretation with a natural isomorphism
  _⊙ˡInterp_ : ∀ {F F' : Functor 𝓒 𝓓} (α : NatIso F F')
               (ı : Interp G 𝓒) → InterpIso G 𝓓 (F ∘Interp ı) (F' ∘Interp ı)
  (α ⊙ˡInterp ı) .fst .fst v = α .trans .N-ob (ı $g v)
  (α ⊙ˡInterp ı) .fst .snd e = α .trans .N-hom (ı <$g> e)
  (α ⊙ˡInterp ı) .snd v = α .nIso (ı $g v)

  ⊙ˡInterp-Seq : ∀ {F F' F'' : Functor 𝓒 𝓓}
                 (α : NatIso F F')(α' : NatIso F' F'') (ı : Interp G 𝓒)
    → (seqNatIso α α') ⊙ˡInterp ı ≡ seqInterpIso (α ⊙ˡInterp ı) (α' ⊙ˡInterp ı)
  ⊙ˡInterp-Seq α α' ı = InterpIso≡ λ v → refl

  ⊙ˡInterp-Sym : ∀ {F F' : Functor 𝓒 𝓓} (α : NatIso F F') (ı : Interp G 𝓒)
    → symNatIso α ⊙ˡInterp ı ≡ symInterpIso (α ⊙ˡInterp ı)
  ⊙ˡInterp-Sym α ı = InterpIso≡ (λ v → refl)

  ⊙ˡInterp-Id : ∀ {F : Functor 𝓒 𝓓} (ı : Interp G 𝓒)
    → idNatIso F ⊙ˡInterp ı ≡ idInterpIso _ _
  ⊙ˡInterp-Id ı = InterpIso≡ (λ v → refl)

  private
    _∙I_ : ∀ {ı ı' ı'' : Interp G 𝓓} → InterpIso G 𝓓 ı ı' →
           InterpIso G 𝓓 ı' ı'' → InterpIso G 𝓓 ı ı''
    α ∙I β = _∘InterpIso_ G 𝓓 β α

  -- "parallel" composition of a natural isomorphism and an interp isomorphism
  _⊙Interp_ : ∀ {F F' : Functor 𝓒 𝓓} (α : NatIso F F')
              {ı ı' : Interp G 𝓒} → (β : InterpIso _ 𝓒 ı ı') →
            InterpIso G 𝓓 (F ∘Interp ı) (F' ∘Interp ı')
  _⊙Interp_ {F}{F'} α {ı}{ı'} β = (F ⊙ʳInterp β) ∙I (α ⊙ˡInterp ı')


⊙ʳInterpIdF : {G : Graph ℓg ℓg'}{𝓒 : Category ℓc ℓc'} {ı ı' : Interp G 𝓒} →
              (α : InterpIso G 𝓒 ı ı')
            → Id ⊙ʳInterp α ≡ α
⊙ʳInterpIdF α = InterpIso≡ (λ v → refl)

⊙ʳInterpCompF : {G : Graph ℓg ℓg'}{𝓒 : Category ℓc ℓc'}
                {𝓓 : Category ℓd ℓd'}{𝓔 : Category ℓe ℓe'}
                 (K : Functor 𝓓 𝓔) (J : Functor 𝓒 𝓓)
                 {ı ı' : Interp G 𝓒} → (α : InterpIso G 𝓒 ı ı')
              → (K ∘F J) ⊙ʳInterp α ≡ K ⊙ʳInterp (J ⊙ʳInterp α)
⊙ʳInterpCompF K J α = InterpIso≡ λ v → refl

∘ʳ⊙ˡ≡⊙ʳ⊙ˡ : {G : Graph ℓg ℓg'} {𝓒 : Category ℓc ℓc'}
        (ı : Interp G 𝓒)
        {𝓓 : Category ℓd ℓd'} {F F' : Functor 𝓒 𝓓}
        (α : NatIso F F')
        {𝓔 : Category ℓe ℓe'}
        (K : Functor 𝓓 𝓔)
     → (K ∘ʳi α) ⊙ˡInterp ı ≡ K ⊙ʳInterp (α ⊙ˡInterp ı)
∘ʳ⊙ˡ≡⊙ʳ⊙ˡ ı α K = refl
