module HyperDoc.Effects.ManualWriter where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

private
  variable ℓS ℓ ℓ' ℓ'' : Level

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
  SubAlg : (B : WriterAlg ℓ) → (ℓ' : Level) → Type (ℓ-max (ℓ-max ℓS ℓ) (ℓ-suc ℓ'))
  SubAlg B ℓ' = Σ[ Q ∈ ((B .fst) → Type ℓ') ]
    (∀ c b → Q b → Q (B .snd c b))

  module _ {B : WriterAlg ℓ}{B' : WriterAlg ℓ'} where
    pull : (ϕ : WriterHom B B') (Q : SubAlg B' ℓ'') → SubAlg B ℓ''
    pull ϕ Q .fst b = Q .fst (ϕ .fst b)
    pull ϕ Q .snd c b Q⟨ϕb⟩ = subst (Q .fst) (ϕ .snd c b) (Q .snd c (ϕ .fst b) Q⟨ϕb⟩)

  module _ {Char : Type ℓ}{B : WriterAlg ℓ'}  where
    module _ (f : Char → B .fst) (P : Char → Type ℓ'') where
      -- Note: this type is equivalent to
      -- |push| b = Σ[ a ∈ A ] Σ[ cs ∈ List Char ] b ≡ cs * (f a) where * is the extension of B .snd to lists
      data |push| : B .fst → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓS))) where
        ret∈ : ∀ a → P a → |push| (f a)
        c*-cong : ∀ c b → |push| b → |push| (B .snd c b)
        -- add a squash if you want it to be a Prop
