-- Algebras for the theory of a Boolean state.
-- The free algebras are given by the state monad.
module Cubical.Algebra.State where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level

record StateAlg (X : Type ℓ) : Type ℓ where
  field
    rd : X → X → X
    wt : Bool → X → X
    wt-rd : ∀ b xt xf → wt b (rd xt xf) ≡ wt b (if b then xt else xf)
    rd-wt : ∀ x → x ≡ rd (wt true x) (wt false x)
    wt-wt : ∀ b1 b2 x → (wt b1 $ wt b2 x) ≡ wt b2 x

  rd-rd : ∀ xtt xtf xft xff
    → rd (rd xtt xtf) (rd xft xff) ≡ rd xtt xff
  rd-rd xtt xtf xft xff =
    rd-wt _
    ∙ cong₂ rd
      (wt-rd _ _ _ ∙ wt-rd _ _ _ ∙ (sym $ wt-rd _ _ _))
      (wt-rd _ _ _ ∙ wt-rd _ _ _ ∙ (sym $ wt-rd _ _ _))
    ∙ (sym $ rd-wt _)

  rd-idempotent : ∀ x → rd x x ≡ x
  rd-idempotent x =
    rd-wt _
    ∙ cong₂ rd (wt-rd _ _ _) (wt-rd _ _ _)
    ∙ (sym $ rd-wt _)

record Homo {X : Type ℓ} {X' : Type ℓ'}
  (f : X → X') (B : StateAlg X) (B' : StateAlg X')
  : Type (ℓ-max ℓ' ℓ) where
  private
    module B = StateAlg B
    module B' = StateAlg B'
  field
    rd-hom : ∀ xt xf → f (B.rd xt xf) ≡ B'.rd (f xt) (f xf)
    wt-hom : ∀ b x → f (B.wt b x) ≡ B'.wt b (f x)

isPropHomo : {X : Type ℓ} {Y : Type ℓ'}
  {f : X → Y} {B : StateAlg X} {B' : StateAlg Y}
  → isSet Y → isProp (Homo f B B')
isPropHomo isSetY ϕ ψ i .Homo.rd-hom xt xf =
  isSetY _ _ (ϕ .Homo.rd-hom xt xf) (ψ .Homo.rd-hom xt xf) i
isPropHomo isSetY ϕ ψ i .Homo.wt-hom b x =
  isSetY _ _ (ϕ .Homo.wt-hom b x) (ψ .Homo.wt-hom b x) i

module _ {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X}{B' : StateAlg X'}
  (ϕ : Σ (X → X') (λ f → Homo f B B'))
  (ψ : Σ (X → X') (λ g → Homo g B B'))
  (isSetX' : isSet X')
  where
  ∫Homo≡ : ϕ .fst ≡ ψ .fst → ϕ ≡ ψ
  ∫Homo≡ ϕ≡ψ i .fst = ϕ≡ψ i
  ∫Homo≡ ϕ≡ψ i .snd =
    isProp→PathP {B = λ i → Homo (ϕ≡ψ i) B B'}
      (λ i → isPropHomo isSetX') (ϕ .snd) (ψ .snd) i

module _ {X : Type ℓ} {B : StateAlg X} where
  open StateAlg B
  idHomo : Homo (λ x → x) B B
  idHomo .Homo.rd-hom _ _ = refl
  idHomo .Homo.wt-hom _ _ = refl

module _ {X : Type ℓ} {X' : Type ℓ'} {X'' : Type ℓ''}
  {B : StateAlg X} {B' : StateAlg X'} {B'' : StateAlg X''}
  {f : X → X'} {g : X' → X''}
  (ϕ : Homo f B B')
  (ψ : Homo g B' B'')
  where
  _⋆Homo_ : Homo (g ∘ f) B B''
  _⋆Homo_ .Homo.rd-hom xt xf = cong g (ϕ .Homo.rd-hom _ _) ∙ ψ .Homo.rd-hom _ _
  _⋆Homo_ .Homo.wt-hom b x = cong g (ϕ .Homo.wt-hom _ _) ∙ ψ .Homo.wt-hom _ _

record StateAlgᴰ {X : Type ℓ} (B : StateAlg X)
  (Xᴰ : X → Type ℓᴰ) : Type (ℓ-max ℓ ℓᴰ) where
  open StateAlg B
  open depReasoning Xᴰ public
  field
    rdᴰ : ∀ {xt xf} → Xᴰ xt → Xᴰ xf → Xᴰ (rd xt xf)
    wtᴰ : ∀ {x} b → Xᴰ x → Xᴰ (wt b x)
    wt-rdᴰ : ∀ b xt xf xtᴰ xfᴰ
      → wtᴰ b (rdᴰ xtᴰ xfᴰ) P≡[ wt-rd b xt xf ] wtᴰ b (Bool.elim {A = λ b → Xᴰ (if b then xt else xf)} xtᴰ xfᴰ b)
    rd-wtᴰ : ∀ x xᴰ
      → xᴰ P≡[ rd-wt x ] rdᴰ (wtᴰ true xᴰ) (wtᴰ false xᴰ)
    wt-wtᴰ : ∀ b b' x xᴰ
      → wtᴰ b (wtᴰ b' xᴰ) P≡[ wt-wt b b' x ] wtᴰ b' xᴰ

  ∫ : StateAlg (Σ X Xᴰ)
  ∫ .StateAlg.rd (_ , xtᴰ) (_ , xfᴰ) = _ , rdᴰ xtᴰ xfᴰ
  ∫ .StateAlg.wt b (_ , xᴰ) = _ , wtᴰ b xᴰ
  ∫ .StateAlg.wt-rd false xt xf = ΣPathP (_ , wt-rdᴰ _ _ _ _ _)
  ∫ .StateAlg.wt-rd true xt xf = ΣPathP (_ , wt-rdᴰ _ _ _ _ _)
  ∫ .StateAlg.rd-wt (x , xᴰ) = ΣPathP (_ , rd-wtᴰ _ _)
  ∫ .StateAlg.wt-wt b1 b2 (x , xᴰ) = ΣPathP (_ , wt-wtᴰ _ _ _ _)

module _ {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  (ϕ : Homo f B B')
  {Xᴰ' : X' → Type ℓᴰ'} (Bᴰ' : StateAlgᴰ B' Xᴰ')
  (isSetX' : isSet X')
  where
  private
    module B = StateAlg B
    module B' = StateAlg B'
    module ϕ = Homo ϕ
    module Bᴰ' where
      open StateAlgᴰ Bᴰ' public
      open hSetReasoning (_ , isSetX') Xᴰ' using (rectifyOut) public

    rdᴰ : ∀ {xt xf} → Xᴰ' (f xt) → Xᴰ' (f xf) → Xᴰ' (f (B.rd xt xf))
    rdᴰ {xt} {xf} xtᴰ xfᴰ =
      Bᴰ'.reind (sym (ϕ.rd-hom xt xf)) (Bᴰ'.rdᴰ xtᴰ xfᴰ)

    wtᴰ : ∀ {x} b → Xᴰ' (f x) → Xᴰ' (f (B.wt b x))
    wtᴰ {x} b xᴰ = Bᴰ'.reind (sym (ϕ.wt-hom b x)) (Bᴰ'.wtᴰ b xᴰ)

    rdᴰ-filler : ∀ {xt xf} (xtᴰ : Xᴰ' (f xt)) (xfᴰ : Xᴰ' (f xf))
      → Path (Σ X' Xᴰ')
          (f (B.rd xt xf) , rdᴰ xtᴰ xfᴰ)
          (B'.rd (f xt) (f xf) , Bᴰ'.rdᴰ xtᴰ xfᴰ)
    rdᴰ-filler {xt} {xf} xtᴰ xfᴰ =
      sym (Bᴰ'.reind-filler (sym (ϕ.rd-hom xt xf)))

    wtᴰ-filler : ∀ {x} b (xᴰ : Xᴰ' (f x))
      → Path (Σ X' Xᴰ')
          (f (B.wt b x) , wtᴰ b xᴰ)
          (B'.wt b (f x) , Bᴰ'.wtᴰ b xᴰ)
    wtᴰ-filler {x} b xᴰ =
      sym (Bᴰ'.reind-filler (sym (ϕ.wt-hom b x)))

  reindexStateAlgᴰ : StateAlgᴰ B (Xᴰ' ∘ f)
  reindexStateAlgᴰ .StateAlgᴰ.rdᴰ = rdᴰ
  reindexStateAlgᴰ .StateAlgᴰ.wtᴰ = wtᴰ
  reindexStateAlgᴰ .StateAlgᴰ.wt-rdᴰ false xt xf xtᴰ xfᴰ =
    Bᴰ'.rectifyOut $
      wtᴰ-filler false (rdᴰ xtᴰ xfᴰ)
      ∙ cong (Bᴰ'.∫ .StateAlg.wt false) (rdᴰ-filler xtᴰ xfᴰ)
      ∙ Bᴰ'.∫ .StateAlg.wt-rd false (f xt , xtᴰ) (f xf , xfᴰ)
      ∙ sym (wtᴰ-filler false xfᴰ)
  reindexStateAlgᴰ .StateAlgᴰ.wt-rdᴰ true xt xf xtᴰ xfᴰ =
    Bᴰ'.rectifyOut $
      wtᴰ-filler true (rdᴰ xtᴰ xfᴰ)
      ∙ cong (Bᴰ'.∫ .StateAlg.wt true) (rdᴰ-filler xtᴰ xfᴰ)
      ∙ Bᴰ'.∫ .StateAlg.wt-rd true (f xt , xtᴰ) (f xf , xfᴰ)
      ∙ sym (wtᴰ-filler true xtᴰ)
  reindexStateAlgᴰ .StateAlgᴰ.rd-wtᴰ x xᴰ = Bᴰ'.rectifyOut $
    Bᴰ'.∫ .StateAlg.rd-wt (f x , xᴰ)
    ∙ cong₂ (Bᴰ'.∫ .StateAlg.rd)
        (sym (wtᴰ-filler true xᴰ)) (sym (wtᴰ-filler false xᴰ))
    ∙ sym (rdᴰ-filler (wtᴰ true xᴰ) (wtᴰ false xᴰ))
  reindexStateAlgᴰ .StateAlgᴰ.wt-wtᴰ b b' x xᴰ = Bᴰ'.rectifyOut $
    wtᴰ-filler b (wtᴰ b' xᴰ)
    ∙ cong (Bᴰ'.∫ .StateAlg.wt b) (wtᴰ-filler b' xᴰ)
    ∙ Bᴰ'.∫ .StateAlg.wt-wt b b' (f x , xᴰ)
    ∙ sym (wtᴰ-filler b' xᴰ)

  reindexStateAlgᴰ-rd-filler : ∀ {xt xf}
    (xtᴰ : Xᴰ' (f xt)) (xfᴰ : Xᴰ' (f xf))
    → Path (Σ X' Xᴰ')
        (f (B.rd xt xf) , StateAlgᴰ.rdᴰ reindexStateAlgᴰ xtᴰ xfᴰ)
        (B'.rd (f xt) (f xf) , Bᴰ'.rdᴰ xtᴰ xfᴰ)
  reindexStateAlgᴰ-rd-filler = rdᴰ-filler

  reindexStateAlgᴰ-wt-filler : ∀ {x} b (xᴰ : Xᴰ' (f x))
    → Path (Σ X' Xᴰ')
        (f (B.wt b x) , StateAlgᴰ.wtᴰ reindexStateAlgᴰ b xᴰ)
        (B'.wt b (f x) , Bᴰ'.wtᴰ b xᴰ)
  reindexStateAlgᴰ-wt-filler = wtᴰ-filler

record Homoᴰ {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  (fᴰ : mapOver f Xᴰ Xᴰ')
  (ϕ : Homo f B B')
  (Bᴰ : StateAlgᴰ B Xᴰ) (Bᴰ' : StateAlgᴰ B' Xᴰ')
  : Type (ℓᴰ' ⊔ℓ ℓᴰ ⊔ℓ ℓ) where
  private
    module B = StateAlg B
    module B' = StateAlg B'
    module Bᴰ = StateAlgᴰ Bᴰ
    module Bᴰ' = StateAlgᴰ Bᴰ'
  field
    rd-homᴰ : ∀ xt xf xtᴰ xfᴰ
      → fᴰ _ (Bᴰ.rdᴰ xtᴰ xfᴰ) Bᴰ'.P≡[ ϕ .Homo.rd-hom xt xf ] Bᴰ'.rdᴰ (fᴰ xt xtᴰ) (fᴰ xf xfᴰ)
    wt-homᴰ : ∀ b x xᴰ
      → fᴰ _ (Bᴰ.wtᴰ b xᴰ) Bᴰ'.P≡[ ϕ .Homo.wt-hom b x ] Bᴰ'.wtᴰ b (fᴰ x xᴰ)

  ∫ : Homo (λ (b , bᴰ) → f b , fᴰ b bᴰ) Bᴰ.∫ Bᴰ'.∫
  ∫ .Homo.rd-hom xt xf = ΣPathP (_ , (rd-homᴰ (xt .fst) (xf .fst) (xt .snd) (xf .snd)))
  ∫ .Homo.wt-hom b x = ΣPathP (_ , wt-homᴰ b (x .fst) (x .snd))

isPropHomoᴰ : {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  {ϕ : Homo f B B'}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  {fᴰ : mapOver f Xᴰ Xᴰ'} {Bᴰ : StateAlgᴰ B Xᴰ} {Bᴰ' : StateAlgᴰ B' Xᴰ'}
  (isSetXᴰ' : ∀ x → isSet (Xᴰ' x))
  → isProp (Homoᴰ fᴰ ϕ Bᴰ Bᴰ')
isPropHomoᴰ isSetXᴰ' ϕᴰ ψᴰ i .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ =
  isOfHLevelPathP' 1 (isSetXᴰ' _) _ _
    (ϕᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ)
    (ψᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ) i
isPropHomoᴰ isSetXᴰ' ϕᴰ ψᴰ i .Homoᴰ.wt-homᴰ b x xᴰ =
  isOfHLevelPathP' 1 (isSetXᴰ' _) _ _
    (ϕᴰ .Homoᴰ.wt-homᴰ b x xᴰ)
    (ψᴰ .Homoᴰ.wt-homᴰ b x xᴰ) i

module _ {X : Type ℓ} {B : StateAlg X}
  {Xᴰ : X → Type ℓᴰ} {Bᴰ : StateAlgᴰ B Xᴰ} where
  idHomoᴰ : Homoᴰ (λ _ xᴰ → xᴰ) idHomo Bᴰ Bᴰ
  idHomoᴰ .Homoᴰ.rd-homᴰ _ _ _ _ = refl
  idHomoᴰ .Homoᴰ.wt-homᴰ _ _ _ = refl

module _ {X : Type ℓ} {X' : Type ℓ'} {X'' : Type ℓ''}
  {B : StateAlg X} {B' : StateAlg X'} {B'' : StateAlg X''}
  {f : X → X'} {g : X' → X''}
  {ϕ : Homo f B B'} {ψ : Homo g B' B''}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  {Xᴰ'' : X'' → Type ℓᴰ''}
  {Bᴰ : StateAlgᴰ B Xᴰ} {Bᴰ' : StateAlgᴰ B' Xᴰ'}
  {Bᴰ'' : StateAlgᴰ B'' Xᴰ''}
  {fᴰ : mapOver f Xᴰ Xᴰ'} {gᴰ : mapOver g Xᴰ' Xᴰ''}
  (ϕᴰ : Homoᴰ fᴰ ϕ Bᴰ Bᴰ') (ψᴰ : Homoᴰ gᴰ ψ Bᴰ' Bᴰ'')
  (isSetX'' : isSet X'') where
  private
    module Bᴰ'' where
      open StateAlgᴰ Bᴰ'' public
      open hSetReasoning (_ , isSetX'') Xᴰ'' using (rectifyOut) public

  _⋆Homoᴰ_ : Homoᴰ (λ x xᴰ → gᴰ (f x) (fᴰ x xᴰ)) (ϕ ⋆Homo ψ) Bᴰ Bᴰ''
  _⋆Homoᴰ_ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ = Bᴰ''.rectifyOut $
    (Homoᴰ.∫ ϕᴰ ⋆Homo Homoᴰ.∫ ψᴰ) .Homo.rd-hom
      (xt , xtᴰ) (xf , xfᴰ)
  _⋆Homoᴰ_ .Homoᴰ.wt-homᴰ b x xᴰ = Bᴰ''.rectifyOut $
    (Homoᴰ.∫ ϕᴰ ⋆Homo Homoᴰ.∫ ψᴰ) .Homo.wt-hom b (x , xᴰ)

Homoⱽ : {X : Type ℓ} {B : StateAlg X}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X → Type ℓᴰ'}
  (fᴰ : ∀ x → Xᴰ x → Xᴰ' x)
  (Bᴰ : StateAlgᴰ B Xᴰ) (Bᴰ' : StateAlgᴰ B Xᴰ') → Type _
Homoⱽ fᴰ Bᴰ Bᴰ' = Homoᴰ fᴰ idHomo Bᴰ Bᴰ'
