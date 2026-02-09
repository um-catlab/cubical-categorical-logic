module HyperDoc.Effects.ManualWriter where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Preorder
open import Cubical.Functions.Logic
open import Cubical.Foundations.Powerset

import Cubical.Data.Equality as Eq 

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.HITs.PropositionalTruncation.Base

open PreorderStr

private
  variable ℓS ℓ ℓ' ℓ''  : Level

module Writer (Char : hSet ℓS) where
  WriterAlg : ∀ ℓ → Type (ℓ-max ℓS (ℓ-suc ℓ))
  WriterAlg ℓ = Σ[ X ∈ Type ℓ ] (⟨ Char ⟩ → X → X)

  WriterHom : WriterAlg ℓ → WriterAlg ℓ' → Type (ℓ-max (ℓ-max ℓS ℓ) ℓ')
  WriterHom B B' = Σ[ f ∈ (B .fst → B' .fst) ]
    (∀ c b → B' .snd c (f b) ≡ f (B .snd c b))

  WriterHom≡ : {B : WriterAlg ℓ}{B' : WriterAlg ℓ'}
    → {ϕ ψ : WriterHom B B'}
    → isSet (B' .fst)
    → ϕ .fst ≡ ψ .fst → ϕ ≡ ψ
  WriterHom≡ isSetB' x = ΣPathPProp (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isSetB' _ _)))
    x

  idHom : {B : WriterAlg ℓ} → WriterHom B B
  idHom .fst = λ z → z
  idHom .snd = λ _ _ → refl

  _⋆Hom_ : {B : WriterAlg ℓ}{B' : WriterAlg ℓ'}{B'' : WriterAlg ℓ''}
    (ϕ : WriterHom B B') (ψ : WriterHom B' B'')
    → WriterHom B B''
  (ϕ ⋆Hom ψ) .fst = λ z → ψ .fst (ϕ .fst z)
  (ϕ ⋆Hom ψ) .snd c b = ψ .snd c (ϕ .fst b) ∙ cong (ψ .fst) (ϕ .snd c b)

  open Category
  WRITERALG : ∀ ℓ → Category (ℓ-max ℓS (ℓ-suc ℓ)) (ℓ-max ℓS ℓ)
  WRITERALG ℓ .ob = Σ[ B ∈ WriterAlg ℓ ] isSet (B .fst)
  WRITERALG ℓ .Hom[_,_] (B , _) (B' , _) = WriterHom B B'
  WRITERALG ℓ .id = idHom
  WRITERALG ℓ ._⋆_ {y = (B' , _)}{z = (B'' , _)} = _⋆Hom_ {B' = B'}{B'' = B''}
  WRITERALG ℓ .⋆IdL {y = B'} ϕ = WriterHom≡ {B' = B' .fst} (B' .snd) refl
  WRITERALG ℓ .⋆IdR {y = B'} ϕ = WriterHom≡ {B' = B' .fst} (B' .snd) refl
  WRITERALG ℓ .⋆Assoc {w = B''} σ ϕ Ψ = WriterHom≡ {B' = B'' .fst} (B'' .snd) refl
  WRITERALG ℓ .isSetHom {y = B'} = isSetΣ (isSet→ (B' .snd)) λ _ → isProp→isSet (isPropΠ (λ _ → isPropΠ (λ _ → B' .snd _ _)))

  -- Note: this is equivalent to List ⟨ Char ⟩ × X
  data |FreeWriterAlg| (X : Type ℓ) : Type (ℓ-max ℓ ℓS) where
    ret : X → |FreeWriterAlg| X
    c* : ⟨ Char ⟩ → |FreeWriterAlg| X → |FreeWriterAlg| X

  FreeWriterAlg : (X : Type ℓ) → WriterAlg (ℓ-max ℓ ℓS)
  FreeWriterAlg X .fst = |FreeWriterAlg| X
  FreeWriterAlg X .snd = c*

  module _ {X : Type ℓ} (B : WriterAlg ℓ')
    (f : X → B .fst)
    where
    |ext| : |FreeWriterAlg| X → B .fst
    |ext| (ret x) = f x
    |ext| (c* c t) = B .snd c (|ext| t)

    ext : WriterHom (FreeWriterAlg X) B
    ext .fst = |ext|
    ext .snd c (ret x) = refl
    ext .snd c (c* x b) = refl

    -- Universal property: ext is inverse to pre-composition with ret

  -- A subalgebra is a congruence relation
  -- this is without any hlevel restriction for better inference
  {-SubAlg : (B : WriterAlg ℓ) → (ℓ' : Level) → Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-suc ℓ'))
  SubAlg B ℓ' = Σ[ Q ∈ ((B .fst) → Type ℓ') ]
    (∀ c b → Q b → Q (B .snd c b)) -}
{-
  module _ {B : WriterAlg ℓ}{B' : WriterAlg ℓ'} where
    pull : (ϕ : WriterHom B B') (Q : SubAlg B' ℓ'') → SubAlg B ℓ''
    pull ϕ Q .fst b = Q .fst (ϕ .fst b)
    pull ϕ Q .snd c b Q⟨ϕb⟩ = subst (Q .fst) (ϕ .snd c b) (Q .snd c (ϕ .fst b) Q⟨ϕb⟩) -}

  module _ {Char : Type ℓ}{B : WriterAlg ℓ'}  where
    module _ (f : Char → B .fst) (P : Char → hProp ℓ'') where
      -- Note: this type is equivalent to
      -- |push| b = Σ[ a ∈ A ] Σ[ cs ∈ List Char ] b ≡ cs * (f a) where * is the extension of B .snd to lists
      data |push| : B .fst → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓS))) where
        ret∈ : ∀ a a' → ⟨ P a ⟩  → a' Eq.≡ (f a) → |push| a'
        c*-cong : ∀ c b b' → |push| b →  (B .snd c b) Eq.≡ b' → |push| b'
        -- add a squash if you want it to be a Prop

  Closed : (A : WriterAlg ℓ) → ℙ ⟨ A ⟩ → Type (ℓ-max ℓS ℓ)
  Closed A P = (w : ⟨ Char ⟩)(a : A .fst) → a ∈ P → A .snd w a ∈ P

  isPropClosed : (A : WriterAlg ℓ) → (P : ℙ (A .fst)) → isProp (Closed A P) 
  isPropClosed A P p q = funExt λ w → funExt λ a → funExt λ Pa → P (A .snd w a) .snd (p w a Pa) (q w a Pa)

  SubAlg : (A : WriterAlg ℓ) → Type (ℓ-max ℓS (ℓ-suc ℓ))
  SubAlg A = Σ[ P ∈ ℙ (A .fst) ] Closed A P

  module _ {B B' : WriterAlg ℓ} where
    pull : (ϕ : WriterHom B B') (Q : SubAlg B') → SubAlg B
    pull ϕ Q .fst b = Q .fst (ϕ .fst b)
    pull ϕ Q .snd c b Q⟨ϕb⟩ = substₚ (Q .fst) ∣ (ϕ .snd c b) ∣₁  (Q .snd c (ϕ .fst b) Q⟨ϕb⟩)

    subAlg≡ : {X Y : SubAlg B} → (X .fst ≡ Y .fst) → X ≡ Y
    subAlg≡ {X}{Y} prf = ΣPathP (prf , toPathP (isPropClosed B (Y .fst) _ (Y .snd))) 

    subAlg≡' : {X Y : SubAlg B} → ((b : B .fst) → ⟨ X .fst b ⇔ Y .fst b ⟩) → X ≡ Y
    subAlg≡' {X}{Y} prf = subAlg≡ (funExt λ b → ⇔toPath (prf b .fst)  (prf b .snd)) 

  subAlgPo : ob (WRITERALG ℓ) → ob (POSET  (ℓ-max ℓS (ℓ-suc ℓ)) ℓ ) 
  subAlgPo A .fst .fst = SubAlg (A .fst)
  subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
  subAlgPo A .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  subAlgPo A .snd = {!   !}
