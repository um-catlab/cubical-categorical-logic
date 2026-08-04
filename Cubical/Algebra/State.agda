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
open import Cubical.Data.Unit

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
    rd-hom : ∀ xt xf rdxtxf → (p : rdxtxf ≡ B.rd xt xf) → f rdxtxf ≡ B'.rd (f xt) (f xf)
    wt-hom : ∀ b x wtbx → (p : wtbx ≡ B.wt b x) → f wtbx ≡ B'.wt b (f x)

  rd-hom' : ∀ xt xf → f (B.rd xt xf) ≡ B'.rd (f xt) (f xf)
  rd-hom' xt xf = rd-hom _ _ _ refl

  wt-hom' : ∀ b x → f (B.wt b x) ≡ B'.wt b (f x)
  wt-hom' b x = wt-hom _ _ _ refl

isPropHomo : {X : Type ℓ} {Y : Type ℓ'}
  {f : X → Y} {B : StateAlg X} {B' : StateAlg Y}
  → isSet Y → isProp (Homo f B B')
isPropHomo isSetY ϕ ψ i .Homo.rd-hom xt xf rdxtxf p =
  isSetY _ _ (ϕ .Homo.rd-hom xt xf rdxtxf p)
    (ψ .Homo.rd-hom xt xf rdxtxf p) i
isPropHomo isSetY ϕ ψ i .Homo.wt-hom b x wtbx p =
  isSetY _ _ (ϕ .Homo.wt-hom b x wtbx p)
    (ψ .Homo.wt-hom b x wtbx p) i

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
  idHomo .Homo.rd-hom xt xf rdxtxf p = p
  idHomo .Homo.wt-hom b x wtbx p = p

module _ {X : Type ℓ} {X' : Type ℓ'} {X'' : Type ℓ''}
  {B : StateAlg X} {B' : StateAlg X'} {B'' : StateAlg X''}
  {f : X → X'} {g : X' → X''}
  (ϕ : Homo f B B')
  (ψ : Homo g B' B'')
  where
  private
    module ϕ = Homo ϕ
    module ψ = Homo ψ
  _⋆Homo_ : Homo (g ∘ f) B B''
  _⋆Homo_ .Homo.rd-hom xt xf rdxtf p = ψ.rd-hom (f xt) (f xf) (f rdxtf) (ϕ.rd-hom xt xf rdxtf p)
  _⋆Homo_ .Homo.wt-hom b x wtbx p = ψ.wt-hom b (f x) (f wtbx) (ϕ.wt-hom b x wtbx p)

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
    rdᴰ {xt} {xf} xtᴰ xfᴰ = Bᴰ'.reind (sym (ϕ.rd-hom' xt xf)) (Bᴰ'.rdᴰ xtᴰ xfᴰ)

    wtᴰ : ∀ {x} b → Xᴰ' (f x) → Xᴰ' (f (B.wt b x))
    wtᴰ {x} b xᴰ = Bᴰ'.reind (sym (ϕ.wt-hom' b x)) (Bᴰ'.wtᴰ b xᴰ)

    rdᴰ-filler : ∀ {xt xf} (xtᴰ : Xᴰ' (f xt)) (xfᴰ : Xᴰ' (f xf))
      → Path (Σ X' Xᴰ')
          (f (B.rd xt xf) , rdᴰ xtᴰ xfᴰ)
          (B'.rd (f xt) (f xf) , Bᴰ'.rdᴰ xtᴰ xfᴰ)
    rdᴰ-filler {xt} {xf} xtᴰ xfᴰ =
      sym (Bᴰ'.reind-filler (sym (ϕ.rd-hom' xt xf)))

    wtᴰ-filler : ∀ {x} b (xᴰ : Xᴰ' (f x))
      → Path (Σ X' Xᴰ')
          (f (B.wt b x) , wtᴰ b xᴰ)
          (B'.wt b (f x) , Bᴰ'.wtᴰ b xᴰ)
    wtᴰ-filler {x} b xᴰ =
      sym (Bᴰ'.reind-filler (sym (ϕ.wt-hom' b x)))

  reindexStateAlgᴰ : StateAlgᴰ B (Xᴰ' ∘ f)
  reindexStateAlgᴰ .StateAlgᴰ.rdᴰ = rdᴰ
  reindexStateAlgᴰ .StateAlgᴰ.wtᴰ = wtᴰ
  reindexStateAlgᴰ .StateAlgᴰ.wt-rdᴰ false xt xf xtᴰ xfᴰ = Bᴰ'.rectifyOut $
    wtᴰ-filler false (rdᴰ xtᴰ xfᴰ)
    ∙ cong (Bᴰ'.∫ .StateAlg.wt false) (rdᴰ-filler xtᴰ xfᴰ)
    ∙ Bᴰ'.∫ .StateAlg.wt-rd false (f xt , xtᴰ) (f xf , xfᴰ)
    ∙ sym (wtᴰ-filler false xfᴰ)
  reindexStateAlgᴰ .StateAlgᴰ.wt-rdᴰ true xt xf xtᴰ xfᴰ = Bᴰ'.rectifyOut $
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
    module ϕ = Homo ϕ
  field
    rd-homᴰ : ∀ xt xf xtᴰ xfᴰ
      rdtf rdtfᴰ
      → (p : rdtf ≡ B.rd xt xf)
      → (pᴰ : rdtfᴰ Bᴰ.P≡[ p ] Bᴰ.rdᴰ xtᴰ xfᴰ)
      → fᴰ rdtf rdtfᴰ Bᴰ'.P≡[ ϕ.rd-hom xt xf rdtf p ] Bᴰ'.rdᴰ (fᴰ xt xtᴰ) (fᴰ xf xfᴰ)
    wt-homᴰ : ∀ b x xᴰ wtbx wtbxᴰ
      → (p : wtbx ≡ B.wt b x)
      → (pᴰ : wtbxᴰ Bᴰ.P≡[ p ] Bᴰ.wtᴰ b xᴰ)
      → fᴰ wtbx wtbxᴰ Bᴰ'.P≡[ ϕ.wt-hom b x wtbx p ] Bᴰ'.wtᴰ b (fᴰ x xᴰ)

  rd-homᴰ' : ∀ xt xf xtᴰ xfᴰ
    → fᴰ _ (Bᴰ.rdᴰ xtᴰ xfᴰ)
      Bᴰ'.P≡[ ϕ.rd-hom' xt xf ]
      Bᴰ'.rdᴰ (fᴰ xt xtᴰ) (fᴰ xf xfᴰ)
  rd-homᴰ' xt xf xtᴰ xfᴰ =
    rd-homᴰ xt xf xtᴰ xfᴰ _ _ refl refl

  wt-homᴰ' : ∀ b x xᴰ
    → fᴰ _ (Bᴰ.wtᴰ b xᴰ)
      Bᴰ'.P≡[ ϕ.wt-hom' b x ] Bᴰ'.wtᴰ b (fᴰ x xᴰ)
  wt-homᴰ' b x xᴰ = wt-homᴰ b x xᴰ _ _ refl refl

  ∫ : Homo (λ (b , bᴰ) → f b , fᴰ b bᴰ) Bᴰ.∫ Bᴰ'.∫
  ∫ .Homo.rd-hom xt xf rdxtxf p =
    ΣPathP ( (ϕ.rd-hom (xt .fst) (xf .fst) (rdxtxf .fst) (PathPΣ p .fst))
           , rd-homᴰ (xt .fst) (xf .fst) (xt .snd) (xf .snd) (rdxtxf .fst) (rdxtxf .snd) (PathPΣ p .fst) ((PathPΣ p .snd)))
  ∫ .Homo.wt-hom b x wtbx p = ΣPathP ( _ , wt-homᴰ b (x .fst) (x .snd) (fst wtbx) (wtbx .snd) (PathPΣ p .fst) (PathPΣ p .snd) )

isPropHomoᴰ : {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  {ϕ : Homo f B B'}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  {fᴰ : mapOver f Xᴰ Xᴰ'} {Bᴰ : StateAlgᴰ B Xᴰ} {Bᴰ' : StateAlgᴰ B' Xᴰ'}
  (isSetXᴰ' : ∀ x → isSet (Xᴰ' x))
  → isProp (Homoᴰ fᴰ ϕ Bᴰ Bᴰ')
isPropHomoᴰ isSetXᴰ' ϕᴰ ψᴰ i .Homoᴰ.rd-homᴰ
  xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
  isOfHLevelPathP' 1 (isSetXᴰ' _) _ _
    (ϕᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ)
    (ψᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ) i
isPropHomoᴰ isSetXᴰ' ϕᴰ ψᴰ i .Homoᴰ.wt-homᴰ
  b x xᴰ wtbx wtbxᴰ p pᴰ =
  isOfHLevelPathP' 1 (isSetXᴰ' _) _ _
    (ϕᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ)
    (ψᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ) i

HomoᴰΣ≡ : {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  {ϕ : Homo f B B'}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  {Bᴰ : StateAlgᴰ B Xᴰ} {Bᴰ' : StateAlgᴰ B' Xᴰ'}
  (isSetXᴰ' : ∀ x → isSet (Xᴰ' x))
  (p q : Σ[ fᴰ ∈ mapOver f Xᴰ Xᴰ' ] Homoᴰ fᴰ ϕ Bᴰ Bᴰ')
  → p .fst ≡ q .fst → p ≡ q
HomoᴰΣ≡ isSetXᴰ' p q = Σ≡Prop (λ fᴰ → isPropHomoᴰ isSetXᴰ')

module _ {X : Type ℓ} {B : StateAlg X}
  {Xᴰ : X → Type ℓᴰ} {Bᴰ : StateAlgᴰ B Xᴰ} where
  idHomoᴰ : Homoᴰ (λ _ xᴰ → xᴰ) idHomo Bᴰ Bᴰ
  idHomoᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ = pᴰ
  idHomoᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ = pᴰ

module _ {X : Type ℓ} {X' : Type ℓ'} {X'' : Type ℓ''}
  {B : StateAlg X} {B' : StateAlg X'} {B'' : StateAlg X''}
  {f : X → X'} {g : X' → X''}
  {ϕ : Homo f B B'} {ψ : Homo g B' B''}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X' → Type ℓᴰ'}
  {Xᴰ'' : X'' → Type ℓᴰ''}
  {Bᴰ : StateAlgᴰ B Xᴰ} {Bᴰ' : StateAlgᴰ B' Xᴰ'}
  {Bᴰ'' : StateAlgᴰ B'' Xᴰ''}
  {fᴰ : mapOver f Xᴰ Xᴰ'} {gᴰ : mapOver g Xᴰ' Xᴰ''}
  (ϕᴰ : Homoᴰ fᴰ ϕ Bᴰ Bᴰ') (ψᴰ : Homoᴰ gᴰ ψ Bᴰ' Bᴰ'') where

  _⋆Homoᴰ_ : Homoᴰ (λ x xᴰ → gᴰ (f x) (fᴰ x xᴰ)) (ϕ ⋆Homo ψ) Bᴰ Bᴰ''
  _⋆Homoᴰ_ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
    ψᴰ .Homoᴰ.rd-homᴰ (f xt) (f xf) (fᴰ xt xtᴰ) (fᴰ xf xfᴰ) (f rdtf)
      (fᴰ rdtf rdtfᴰ) (Homo.rd-hom ϕ xt xf rdtf p)
      (ϕᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ)
  _⋆Homoᴰ_ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ =
    ψᴰ .Homoᴰ.wt-homᴰ b (f x) (fᴰ x xᴰ) (f wtbx) (fᴰ wtbx wtbxᴰ)
      (Homo.wt-hom ϕ b x wtbx p)
      (ϕᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ)

Homoⱽ : {X : Type ℓ} {B : StateAlg X}
  {Xᴰ : X → Type ℓᴰ} {Xᴰ' : X → Type ℓᴰ'}
  (fᴰ : ∀ x → Xᴰ x → Xᴰ' x)
  (Bᴰ : StateAlgᴰ B Xᴰ) (Bᴰ' : StateAlgᴰ B Xᴰ') → Type _
Homoⱽ fᴰ Bᴰ Bᴰ' = Homoᴰ fᴰ idHomo Bᴰ Bᴰ'

module _ {X : Type ℓ} (B : StateAlg X) (ℓᴰ : Level) where
  Unitⱽ : StateAlgᴰ B (λ _ → Unit* {ℓᴰ})
  Unitⱽ .StateAlgᴰ.rdᴰ _ _ = tt*
  Unitⱽ .StateAlgᴰ.wtᴰ _ _ = tt*
  Unitⱽ .StateAlgᴰ.wt-rdᴰ _ _ _ _ _ = refl
  Unitⱽ .StateAlgᴰ.rd-wtᴰ _ _ = refl
  Unitⱽ .StateAlgᴰ.wt-wtᴰ _ _ _ _ = refl

module _ {X : Type ℓ} {X' : Type ℓ'}
  {B : StateAlg X} {B' : StateAlg X'} {f : X → X'}
  (ϕ : Homo f B B')
  {Xᴰ : X → Type ℓᴰ} (Bᴰ : StateAlgᴰ B Xᴰ)
  where
  !ⱽ : Homoᴰ (λ _ _ → tt*) ϕ Bᴰ (Unitⱽ B' ℓᴰ)
  !ⱽ .Homoᴰ.rd-homᴰ _ _ _ _ _ _ _ _ = refl
  !ⱽ .Homoᴰ.wt-homᴰ _ _ _ _ _ _ _ = refl

open StateAlgᴰ
open Homoᴰ
module _ {X : Type ℓ}{B : StateAlg X}
  {Xᴰ : X → Type ℓᴰ}
  {Xᴰ' : X → Type ℓᴰ'}
  (Bᴰ : StateAlgᴰ B Xᴰ)
  (Bᴰ' : StateAlgᴰ B Xᴰ')
  where
  private
    module Bᴰ = StateAlgᴰ Bᴰ
    module Bᴰ' = StateAlgᴰ Bᴰ'
  Prodⱽ : StateAlgᴰ B λ x → Xᴰ x × Xᴰ' x
  Prodⱽ .rdᴰ (xtᴰ , xtᴰ') (xfᴰ , xfᴰ') =
    Bᴰ.rdᴰ xtᴰ xfᴰ , Bᴰ'.rdᴰ xtᴰ' xfᴰ'
  Prodⱽ .wtᴰ b x = Bᴰ.wtᴰ b (x .fst) , Bᴰ'.wtᴰ b (x .snd)
  Prodⱽ .wt-rdᴰ false xt xf xtᴰ xfᴰ = ΣPathP
    (Bᴰ.wt-rdᴰ false xt xf (xtᴰ .fst) (xfᴰ .fst) ,
     Bᴰ'.wt-rdᴰ false xt xf (xtᴰ .snd) (xfᴰ .snd))
  Prodⱽ .wt-rdᴰ true xt xf xtᴰ xfᴰ = ΣPathP
    (Bᴰ.wt-rdᴰ true xt xf (xtᴰ .fst) (xfᴰ .fst) ,
     Bᴰ'.wt-rdᴰ true xt xf (xtᴰ .snd) (xfᴰ .snd))
  Prodⱽ .rd-wtᴰ x xᴰ = ΣPathP
    (Bᴰ.rd-wtᴰ x (fst xᴰ) , Bᴰ'.rd-wtᴰ x (snd xᴰ))
  Prodⱽ .wt-wtᴰ b b' x xᴰ = ΣPathP
    (Bᴰ.wt-wtᴰ b b' x (xᴰ .fst) , Bᴰ'.wt-wtᴰ b b' x (xᴰ .snd))

  π₁ⱽ : Homoⱽ (λ _ → fst) Prodⱽ Bᴰ
  π₁ⱽ .Homoᴰ.rd-homᴰ _ _ _ _ _ _ _ pᴰ i = pᴰ i .fst
  π₁ⱽ .Homoᴰ.wt-homᴰ _ _ _ _ _ _ pᴰ i = pᴰ i .fst

  π₂ⱽ : Homoⱽ (λ _ → snd) Prodⱽ Bᴰ'
  π₂ⱽ .Homoᴰ.rd-homᴰ _ _ _ _ _ _ _ pᴰ i = pᴰ i .snd
  π₂ⱽ .Homoᴰ.wt-homᴰ _ _ _ _ _ _ pᴰ i = pᴰ i .snd

  module _ {Γ : Type ℓ''} {Γᴰ : Γ → Type ℓᴰ''} {f : Γ → X}
    {C : StateAlg Γ} {Cᴰ : StateAlgᴰ C Γᴰ}
    {fᴰ : ∀ γ → Γᴰ γ → Xᴰ (f γ) × Xᴰ' (f γ)}
    (ϕ : Homo f C B)
    (ϕᴰ : Homoᴰ fᴰ ϕ Cᴰ Prodⱽ)
    where
    ×ⱽproj₁ : Homoᴰ (λ γ γᴰ → fᴰ γ γᴰ .fst) ϕ Cᴰ Bᴰ
    ×ⱽproj₁ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ i =
      ϕᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ i .fst
    ×ⱽproj₁ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ i =
      ϕᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ i .fst

    ×ⱽproj₂ : Homoᴰ (λ γ γᴰ → fᴰ γ γᴰ .snd) ϕ Cᴰ Bᴰ'
    ×ⱽproj₂ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ i =
      ϕᴰ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ i .snd
    ×ⱽproj₂ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ i =
      ϕᴰ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ i .snd

  module _ {Γ : Type ℓ''}{Γᴰ : Γ → Type ℓᴰ''}{f : Γ → X}
    {C : StateAlg Γ}{Cᴰ : StateAlgᴰ C Γᴰ}
    {f₁ᴰ : ∀ γ → Γᴰ γ → Xᴰ (f γ)}
    {f₂ᴰ : ∀ γ → Γᴰ γ → Xᴰ' (f γ)}
    (ϕ : Homo f C B)
    (ϕ₁ᴰ : Homoᴰ {f = f} f₁ᴰ ϕ Cᴰ Bᴰ)
    (ϕ₂ᴰ : Homoᴰ {f = f} f₂ᴰ ϕ Cᴰ Bᴰ')
    where
    private
      module ϕ = Homo ϕ
      module ϕ₁ᴰ = Homoᴰ ϕ₁ᴰ
      module ϕ₂ᴰ = Homoᴰ ϕ₂ᴰ
    ×ⱽintroⱽ : Homoᴰ {f = f} (λ _ γᴰ → f₁ᴰ _ γᴰ , f₂ᴰ _ γᴰ) ϕ Cᴰ Prodⱽ
    ×ⱽintroⱽ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ = ΣPathP
      (ϕ₁ᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ ,
       ϕ₂ᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ)
    ×ⱽintroⱽ .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ = ΣPathP
      (ϕ₁ᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ ,
       ϕ₂ᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ)

module _ {X : Type ℓ}{B : StateAlg X}
  {X' : Type ℓ'}{B' : StateAlg X'}
  {f : X → X'}
  {Xᴰ' : X' → Type ℓᴰ'}
  (ϕ : Homo f B B')
  (Bᴰ' : StateAlgᴰ B' Xᴰ')
  (isSetX' : isSet X')
  where
  private
    module ϕ = Homo ϕ
    module Bᴰ' where
      open StateAlgᴰ Bᴰ' public
      open hSetReasoning (_ , isSetX') Xᴰ'
        using (rectifyOut) public
  pull : StateAlgᴰ B λ x → Xᴰ' (f x)
  pull = reindexStateAlgᴰ ϕ Bᴰ' isSetX'

  π-pull : Homoᴰ (λ _ xᴰ → xᴰ) ϕ pull Bᴰ'
  π-pull .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
    Bᴰ'.rectifyOut $
      (λ i → f (p i) , pᴰ i)
      ∙ reindexStateAlgᴰ-rd-filler ϕ Bᴰ' isSetX' xtᴰ xfᴰ
  π-pull .Homoᴰ.wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ =
    Bᴰ'.rectifyOut $
      (λ i → f (p i) , pᴰ i)
      ∙ reindexStateAlgᴰ-wt-filler ϕ Bᴰ' isSetX' b xᴰ

  module _ {Γ : Type ℓ''}{Γᴰ : Γ → Type ℓᴰ''}{g : Γ → X}
    {C : StateAlg Γ}{Cᴰ : StateAlgᴰ C Γᴰ}
    {fᴰ : ∀ γ → Γᴰ γ → Xᴰ' (f (g γ))}
    (ψ : Homo g C B)
    (ψϕᴰ : Homoᴰ fᴰ (ψ ⋆Homo ϕ) Cᴰ Bᴰ')
    where
    private
      module ψ = Homo ψ
      module ψϕᴰ = Homoᴰ ψϕᴰ
    pull-intro : Homoᴰ fᴰ ψ Cᴰ pull
    pull-intro .rd-homᴰ xt xf xtᴰ xfᴰ rdtf rdtfᴰ p pᴰ =
      Bᴰ'.rectifyOut $
        ψϕᴰ.∫ .Homo.rd-hom (xt , xtᴰ) (xf , xfᴰ)
          (rdtf , rdtfᴰ) (ΣPathP (p , pᴰ))
        ∙ sym (Homo.rd-hom' (Homoᴰ.∫ π-pull)
          (g xt , fᴰ xt xtᴰ) (g xf , fᴰ xf xfᴰ))
    pull-intro .wt-homᴰ b x xᴰ wtbx wtbxᴰ p pᴰ =
      Bᴰ'.rectifyOut $
        ψϕᴰ.∫ .Homo.wt-hom b (x , xᴰ)
          (wtbx , wtbxᴰ) (ΣPathP (p , pᴰ))
        ∙ sym (Homo.wt-hom' (Homoᴰ.∫ π-pull) b (g x , fᴰ x xᴰ))
