{-# OPTIONS --lossy-unification #-}
-- Guarded recursion over the walking parallel pair V ⇉ E
module Cubical.Categories.Direct.Examples.ParallelPair where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (true ; false)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Int using (ℤ ; _-_ ; isSetℤ)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Presheaf.Base using (Presheaf)
open import Cubical.Categories.Presheaf.Constructions.Unit using (UnitPsh)
open import Cubical.Categories.Presheaf.StrictHom.Base
  using (PshHomStrict ; pshhom ; PshHomStrictN-homTy ; makePshHomStrictPath)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.ParallelPair
import Cubical.Categories.Direct.StrictDownset as SD

open Functor
open Iso
open PshHomStrict

private
  dir = ParallelPairDirect

module _ {ℓP} (P : Presheaf ParallelPair ℓP) where
  -- ▷ P at V is trivial
  ▷V-contr : isContr ⟨ SD.▷Psh dir P .F-ob V ⟩
  ▷V-contr .fst =
    pshhom (λ y (f , q) → ⊥.rec q) (λ c c' g (f' , q') p e → ⊥.rec q')
  ▷V-contr .snd β =
    makePshHomStrictPath (funExt λ y → funExt λ (f , q) → ⊥.rec q)

  private
    ends : ⟨ P .F-ob V ⟩ × ⟨ P .F-ob V ⟩
         → ∀ y → ⟨ SD.↡Psh dir E .F-ob y ⟩ → ⟨ P .F-ob y ⟩
    ends (x , y) V (false , _) = x
    ends (x , y) V (true  , _) = y
    ends (x , y) E (_     , q) = ⊥.rec q

    ends-hom : ∀ xy → PshHomStrictN-homTy (SD.↡Psh dir E) P (ends xy)
    ends-hom xy V V g (f' , q') p e = funExt⁻ (P .F-id) _ ∙ cong (ends xy V) e
    ends-hom xy E V g p'        p e = ⊥.rec g
    ends-hom xy V E g (f' , q') p e = ⊥.rec q'
    ends-hom xy E E g (f' , q') p e = ⊥.rec q'

  -- ▷ P at E is a pair of vertices
  ▷E-Iso : Iso ⟨ SD.▷Psh dir P .F-ob E ⟩ (⟨ P .F-ob V ⟩ × ⟨ P .F-ob V ⟩)
  ▷E-Iso .fun β = β .N-ob V (s , tt) , β .N-ob V (t , tt)
  ▷E-Iso .inv xy = pshhom (ends xy) (ends-hom xy)
  ▷E-Iso .sec xy = refl
  ▷E-Iso .ret β = makePshHomStrictPath (funExt λ where
    V → funExt λ { (false , _) → refl ; (true , _) → refl }
    E → funExt λ { (_ , q) → ⊥.rec q })

  -- next is the boundary of an edge
  next-boundary : ∀ (e : ⟨ P .F-ob E ⟩)
    → ▷E-Iso .fun (SD.next dir P .N-ob E e) ≡ (P .F-hom s e , P .F-hom t e)
  next-boundary e = refl

module Coboundary
  (Vt Et : hSet ℓ-zero)
  (src tgt : ⟨ Et ⟩ → ⟨ Vt ⟩)
  (pot : ⟨ Vt ⟩ → ℤ)
  where

  A : Ob → hSet ℓ-zero
  A V = (⟨ Vt ⟩ → ℤ) , isSet→ isSetℤ
  A E = (⟨ Et ⟩ → ℤ) , isSet→ isSetℤ

  view : ⟨ SD.▷Fam dir {ℓF = ℓ-zero} A E ⟩
       → ParallelPair [ V , E ] → ⟨ Vt ⟩ → ℤ
  view β g = SD.▷FamApp dir {ℓF = ℓ-zero} A β g tt

  step : ∀ x → ⟨ SD.▷Fam dir {ℓF = ℓ-zero} A x ⟩ → ⟨ A x ⟩
  step V β = pot
  step E β e = view β t (tgt e) - view β s (src e)

  potential : ⟨ Vt ⟩ → ℤ
  potential = SD.löbFam dir {ℓF = ℓ-zero} A step V

  δ : ⟨ Et ⟩ → ℤ
  δ = SD.löbFam dir {ℓF = ℓ-zero} A step E

  potential≡pot : potential ≡ pot
  potential≡pot = SD.löbFam-unfold dir {ℓF = ℓ-zero} A step V

  δ-eq : ∀ e → δ e ≡ pot (tgt e) - pot (src e)
  δ-eq e =
    funExt⁻ (SD.löbFam-unfold dir {ℓF = ℓ-zero} A step E) e
    ∙ (λ i → potential≡pot i (tgt e) - potential≡pot i (src e))

  δ-uniq : (f : ⟨ Vt ⟩ → ℤ) (g : ⟨ Et ⟩ → ℤ)
         → f ≡ pot
         → (∀ e → g e ≡ f (tgt e) - f (src e))
         → g ≡ δ
  δ-uniq f g hf hg =
    funExt⁻ (SD.löbFam-uniq-unfold dir {ℓF = ℓ-zero} A step fam fix) E
    where
      fam : ∀ x → ⟨ A x ⟩
      fam V = f
      fam E = g
      fix : ∀ x → fam x ≡ step x (SD.nextFam dir {ℓF = ℓ-zero} A fam x)
      fix V = hf
      fix E = funExt hg

module Example where
  open import Cubical.Data.Bool
    using (Bool ; true ; false ; not ; _and_ ; _⊕_ ; if_then_else_
          ; isSetBool ; Bool→Type ; isProp-Bool→Type)

  Vtx : Type
  Vtx = Bool × Bool

  v₀ v₁ v₂ v₃ : Vtx
  v₀ = false , false
  v₁ = false , true
  v₂ = true  , false
  v₃ = true  , true

  eqV : Vtx → Vtx → Bool
  eqV (a , b) (c , d) = not (a ⊕ c) and not (b ⊕ d)

  hasEdge : Vtx → Vtx → Bool
  hasEdge i j = not (eqV i j and fst i)

  Edg : Type
  Edg = Σ[ p ∈ Vtx × Vtx ] Bool→Type (hasEdge (p .fst) (p .snd))

  src tgt : Edg → Vtx
  src e = e .fst .fst
  tgt e = e .fst .snd

  loop₀ loop₁ : Edg
  loop₀ = (v₀ , v₀) , tt
  loop₁ = (v₁ , v₁) , tt

  isSetVtx : isSet Vtx
  isSetVtx = isSet× isSetBool isSetBool

  -- Complete graph on 4 vertices + 2 self loops
  G : Presheaf ParallelPair ℓ-zero
  G .F-ob V = Vtx , isSetVtx
  G .F-ob E = Edg , isSetΣ (isSet× isSetVtx isSetVtx)
    (λ p → isProp→isSet (isProp-Bool→Type (hasEdge (p .fst) (p .snd))))
  G .F-hom {V} {V} _ i = i
  G .F-hom {E} {E} _ e = e
  G .F-hom {E} {V} f ((i , j) , _) = if f then j else i
  G .F-hom {V} {E} f = ⊥.rec f
  G .F-id {V} = refl
  G .F-id {E} = refl
  G .F-seq {V} {V} {V} f g = refl
  G .F-seq {E} {E} {E} f g = refl
  G .F-seq {E} {E} {V} f g = refl
  G .F-seq {E} {V} {V} f g = refl
  G .F-seq {V} {E}     f g = ⊥.rec f
  G .F-seq {V} {V} {E} f g = ⊥.rec g
  G .F-seq {E} {V} {E} f g = ⊥.rec g

  loopStep : (e : Edg) → tgt e ≡ src e → PshHomStrict (SD.▷Psh dir G) G
  loopStep e q .N-ob V _ = src e
  loopStep e q .N-ob E _ = e
  loopStep e q .N-hom V V f     p' p _ = refl
  loopStep e q .N-hom V E false p' p _ = refl
  loopStep e q .N-hom V E true  p' p _ = q
  loopStep e q .N-hom E E f     p' p _ = refl
  loopStep e q .N-hom E V f     p' p _ = ⊥.rec f

  -- Global elements of a directed graph choose of self loop,
  -- which isn't terribly interesting
  sect₀ sect₁ : PshHomStrict UnitPsh G
  sect₀ = SD.löb dir G (loopStep loop₀ refl)
  sect₁ = SD.löb dir G (loopStep loop₁ refl)

  _ : sect₀ .N-ob V tt ≡ v₀
  _ = refl

  _ : sect₀ .N-ob E tt ≡ loop₀
  _ = refl

  _ : sect₁ .N-ob V tt ≡ v₁
  _ = refl

  _ : sect₁ .N-ob E tt ≡ loop₁
  _ = refl

  private
    c₀ : ⟨ SD.▷Psh dir G .F-ob V ⟩
    c₀ = ▷V-contr G .fst
    β₀ : ⟨ SD.▷Psh dir G .F-ob E ⟩
    β₀ = ▷E-Iso G .inv (v₀ , v₀)

  step-self-loop : (φ : PshHomStrict (SD.▷Psh dir G) G)
    → (src (φ .N-ob E β₀) ≡ φ .N-ob V c₀)
    × (tgt (φ .N-ob E β₀) ≡ φ .N-ob V c₀)
  step-self-loop φ =
      φ .N-hom V E s β₀ _ refl
        ∙ cong (φ .N-ob V) (sym (▷V-contr G .snd _))
    , φ .N-hom V E t β₀ _ refl
        ∙ cong (φ .N-ob V) (sym (▷V-contr G .snd _))
