-- Adjunction between Sets and (Boolean) state algebras
-- and their lifting to Families and displayed algebras
-- as CBPV and CBPVᴰ models.

{-# OPTIONS --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

-- Firstly what is a state algebra?
record StateAlg (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    X : Type ℓ
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

record Homo (B : StateAlg ℓ) (B' : StateAlg ℓ') : Type (ℓ-max ℓ' ℓ) where
  private
    module B = StateAlg B
    module B' = StateAlg B'
  field
    f : B.X → B'.X
    rd-hom : ∀ xt xf → f (B.rd xt xf) ≡ B'.rd (f xt) (f xf)
    wt-hom : ∀ b x → f (B.wt b x) ≡ B'.wt b (f x)

module _ {B : StateAlg ℓ} where
  open StateAlg B
  idHomo : Homo B B
  idHomo .Homo.f x = x
  idHomo .Homo.rd-hom _ _ = refl
  idHomo .Homo.wt-hom _ _ = refl

module _ {B : StateAlg ℓ}{B' : StateAlg ℓ'}{B'' : StateAlg ℓ''}
  (ϕ : Homo B B')
  (ψ : Homo B' B'')
  where
  _⋆Homo_ : Homo B B''
  _⋆Homo_ .Homo.f = ψ .Homo.f ∘ ϕ .Homo.f
  _⋆Homo_ .Homo.rd-hom xt xf = cong (ψ .Homo.f) (ϕ .Homo.rd-hom _ _) ∙ ψ .Homo.rd-hom _ _
  _⋆Homo_ .Homo.wt-hom b x = cong (ψ .Homo.f) (ϕ .Homo.wt-hom _ _) ∙ ψ .Homo.wt-hom _ _

record StateAlgᴰ (B : StateAlg ℓ)(ℓᴰ : Level) : Type (ℓ-max ℓ (ℓ-suc ℓᴰ)) where
  open StateAlg B
  field
    Xᴰ : X → Type ℓᴰ

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

  ∫ : StateAlg (ℓ-max ℓ ℓᴰ)
  ∫ .StateAlg.X = Σ X Xᴰ
  ∫ .StateAlg.rd (_ , xtᴰ) (_ , xfᴰ) = _ , rdᴰ xtᴰ xfᴰ
  ∫ .StateAlg.wt b (_ , xᴰ) = _ , wtᴰ b xᴰ
  ∫ .StateAlg.wt-rd false xt xf = ΣPathP (_ , wt-rdᴰ _ _ _ _ _)
  ∫ .StateAlg.wt-rd true xt xf = ΣPathP (_ , wt-rdᴰ _ _ _ _ _)
  ∫ .StateAlg.rd-wt (x , xᴰ) = ΣPathP (_ , rd-wtᴰ _ _)
  ∫ .StateAlg.wt-wt b1 b2 (x , xᴰ) = ΣPathP (_ , wt-wtᴰ _ _ _ _)

record Homoᴰ {B : StateAlg ℓ}{B' : StateAlg ℓ'}
  (ϕ : Homo B B') (Bᴰ : StateAlgᴰ B ℓᴰ)(Bᴰ' : StateAlgᴰ B' ℓᴰ')
  : Type (ℓᴰ' ⊔ℓ ℓᴰ ⊔ℓ ℓ) where
  private
    module B = StateAlg B
    module B' = StateAlg B'
    module Bᴰ = StateAlgᴰ Bᴰ
    module Bᴰ' = StateAlgᴰ Bᴰ'
  open Homo ϕ
  field
    fᴰ : mapOver f Bᴰ.Xᴰ Bᴰ'.Xᴰ
    rd-homᴰ : ∀ xt xf xtᴰ xfᴰ
      → fᴰ _ (Bᴰ.rdᴰ xtᴰ xfᴰ) Bᴰ'.P≡[ rd-hom xt xf ] Bᴰ'.rdᴰ (fᴰ xt xtᴰ) (fᴰ xf xfᴰ)
    wt-homᴰ : ∀ b x xᴰ
      → fᴰ _ (Bᴰ.wtᴰ b xᴰ) Bᴰ'.P≡[ wt-hom b x ] Bᴰ'.wtᴰ b (fᴰ x xᴰ)

  ∫ : Homo Bᴰ.∫ Bᴰ'.∫
  ∫ .Homo.f (b , bᴰ) = (f b) , (fᴰ b bᴰ)
  ∫ .Homo.rd-hom xt xf = ΣPathP (_ , (rd-homᴰ (xt .fst) (xf .fst) (xt .snd) (xf .snd)))
  ∫ .Homo.wt-hom b x = ΣPathP (_ , wt-homᴰ b (x .fst) (x .snd))

Homoⱽ : {B : StateAlg ℓ} (Bᴰ : StateAlgᴰ B ℓᴰ)(Bᴰ' : StateAlgᴰ B ℓᴰ') → Type _
Homoⱽ Bᴰ Bᴰ' = Homoᴰ idHomo Bᴰ Bᴰ'

module _ (X : Type ℓ) where
  FreeStateAlg : StateAlg ℓ
  FreeStateAlg .StateAlg.X = Bool → Bool × X
  FreeStateAlg .StateAlg.rd ft ff = if_then ft true else ff false
  FreeStateAlg .StateAlg.wt b f _ = f b
  FreeStateAlg .StateAlg.wt-rd false _ _ = refl
  FreeStateAlg .StateAlg.wt-rd true _ _ = refl
  FreeStateAlg .StateAlg.rd-wt f = funExt λ { false → refl ; true → refl }
  FreeStateAlg .StateAlg.wt-wt _ _ _ = refl

  module FreeStateAlg = StateAlg FreeStateAlg

  η : X → Bool → Bool × X
  η x b = b , x

  module _ (B : StateAlg ℓ') where
    private module B = StateAlg B
    module _ (i : X → B.X) where
      recFSA : Homo FreeStateAlg B
      recFSA .Homo.f f = B.rd (B.wt (f true  .fst) (i (f true  .snd)))
                                (B.wt (f false .fst) (i (f false .snd)))
      recFSA .Homo.rd-hom ft ff = sym (B.rd-rd _ _ _ _)
      recFSA .Homo.wt-hom false f =
        B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)
      recFSA .Homo.wt-hom true f =
        B.rd-idempotent _ ∙ (sym $ B.wt-rd _ _ _ ∙ B.wt-wt _ _ _)

      private module recFSA = Homo recFSA
      recFSA-β : ∀ x → recFSA.f (η x) ≡ i x
      recFSA-β x = sym $ B.rd-wt (i x)

    module _ (ϕ : Homo FreeStateAlg B) where
      private
        module ϕ = Homo ϕ
        module recϕ = Homo (recFSA (ϕ.f ∘ η))
      recFSA-η : ∀ f → recϕ.f f ≡ ϕ.f f
      recFSA-η f =
        cong₂ B.rd (sym $ ϕ.wt-hom _ _) (sym $ ϕ.wt-hom _ _)
        ∙ (sym $ ϕ.rd-hom _ _)
        ∙ cong ϕ.f (sym $ FreeStateAlg.rd-wt f)

  module _ (Xᴰ : X → Type ℓ') where
    FreeStateAlgᴰ : StateAlgᴰ FreeStateAlg ℓ'
    FreeStateAlgᴰ .StateAlgᴰ.Xᴰ f = ∀ b → Xᴰ (f b .snd)
    FreeStateAlgᴰ .StateAlgᴰ.rdᴰ {xf} {xt} xfᴰ xtᴰ false = xtᴰ false
    FreeStateAlgᴰ .StateAlgᴰ.rdᴰ {xf} {xt} xfᴰ xtᴰ true  = xfᴰ true
    FreeStateAlgᴰ .StateAlgᴰ.wtᴰ b fᴰ _ = fᴰ b
    FreeStateAlgᴰ .StateAlgᴰ.wt-rdᴰ false _ _ _ _ = refl
    FreeStateAlgᴰ .StateAlgᴰ.wt-rdᴰ true  _ _ _ _ = refl
    FreeStateAlgᴰ .StateAlgᴰ.rd-wtᴰ f fᴰ =
      funExt (λ { false → refl ; true → refl })
    FreeStateAlgᴰ .StateAlgᴰ.wt-wtᴰ b b' f fᴰ = refl

    ηᴰ : mapOver η Xᴰ (FreeStateAlgᴰ .StateAlgᴰ.Xᴰ)
    ηᴰ x xᴰ b = xᴰ

module _ {X : Type ℓ}{Xᴰ : X → Type ℓ'} where
  open StateAlgᴰ using (∫)

  -- ∫ (FSAᴰ Xᴰ) ≅ FSA (∫ Xᴰ)
  open Homo
  -- this is equivalent to pack⁻ but pack⁻ has better definitional
  -- behavior.
  unpack : Homo (FreeStateAlg (Σ X Xᴰ)) (∫ (FreeStateAlgᴰ X Xᴰ))
  unpack = recFSA (Σ X Xᴰ) (∫ (FreeStateAlgᴰ X Xᴰ)) (λ (x , xᴰ) → ((λ b → b , x) , λ b → xᴰ))

  pack : Homo (∫ (FreeStateAlgᴰ X Xᴰ)) (FreeStateAlg (Σ X Xᴰ))
  pack .f (f , fᴰ) b = f b .fst , f b .snd , fᴰ b
  pack .rd-hom (ft , ftᴰ) (ff , ffᴰ) = funExt λ
    { false → refl
    ; true → refl }
  pack .wt-hom b (ft , ftᴰ) = refl

  pack⁻ : isIso (pack .f)
  pack⁻ .fst ∫f .fst b .fst = ∫f b .fst
  pack⁻ .fst ∫f .fst b .snd = ∫f b .snd .fst
  pack⁻ .fst ∫f .snd b = ∫f b .snd .snd
  pack⁻ .snd .fst _ = refl
  pack⁻ .snd .snd _ = refl

  module _ {B : StateAlg ℓ'} (Bᴰ : StateAlgᴰ B ℓᴰ') where
    private
      module B = StateAlg B
      module Bᴰ = StateAlgᴰ Bᴰ

    module _ (i : X → B.X) (iᴰ : ∀ x → Xᴰ x → Bᴰ.Xᴰ (i x)) (isSetB : isSet B.X) where
      -- ∫ FSAᴰ → FSA (∫ X Xᴰ) → ∫ Bᴰ
      ∫recFSAᴰ : Homo (∫ (FreeStateAlgᴰ X Xᴰ)) Bᴰ.∫
      ∫recFSAᴰ = pack ⋆Homo recFSA (Σ X Xᴰ) Bᴰ.∫ (λ z → i (z .fst) , iᴰ (z .fst) (z .snd))

      recFSAᴰ : Homoᴰ (recFSA X B i) (FreeStateAlgᴰ X Xᴰ) Bᴰ
      recFSAᴰ .Homoᴰ.fᴰ s sᴰ = ∫recFSAᴰ .f (s , sᴰ) .snd
      recFSAᴰ .Homoᴰ.rd-homᴰ st sf stᴰ sfᴰ = hSetReasoning.rectifyOut (_ , isSetB) Bᴰ.Xᴰ $
        ∫recFSAᴰ .rd-hom (st , stᴰ) (sf , sfᴰ)
      recFSAᴰ .Homoᴰ.wt-homᴰ b s sᴰ = hSetReasoning.rectifyOut (_ , isSetB) Bᴰ.Xᴰ $
        ∫recFSAᴰ .wt-hom b (s , sᴰ)

module _ {B : StateAlg ℓ}{B' : StateAlg ℓ'}
  (ϕ : Homo B B')
  (Bᴰ : StateAlgᴰ B ℓᴰ)
  where
  private
    module B = StateAlg B
    module B' = StateAlg B'
    module ϕ = Homo ϕ
    module Bᴰ = StateAlgᴰ Bᴰ

  module _ (isSetB' : isSet B'.X) where
    -- Not sure if this isSetB' is actually necessary but makes it
    -- easy
    push : StateAlgᴰ B' _
    push .StateAlgᴰ.Xᴰ b' = Σ[ b ∈ fiber ϕ.f b' ] Bᴰ.Xᴰ (b .fst)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .fst .fst =
      B.rd (b'ᴰ .fst .fst) (b'ᴰ' .fst .fst)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .fst .snd =
      ϕ.rd-hom _ _ ∙ cong₂ B'.rd (b'ᴰ .fst .snd) (b'ᴰ' .fst .snd)
    push .StateAlgᴰ.rdᴰ b'ᴰ b'ᴰ' .snd =
      Bᴰ.rdᴰ (b'ᴰ .snd) (b'ᴰ' .snd)
    push .StateAlgᴰ.wtᴰ b x .fst .fst = B.wt b (x .fst .fst)
    push .StateAlgᴰ.wtᴰ b x .fst .snd =
      ϕ.wt-hom _ _ ∙ cong (B'.wt b) (x .fst .snd)
    push .StateAlgᴰ.wtᴰ b x .snd = Bᴰ.wtᴰ b (x .snd)
    push .StateAlgᴰ.wt-rdᴰ false xt xf xtᴰ xfᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-rd _ _ _)
      , Bᴰ.wt-rdᴰ _ _ _ _ _)
    push .StateAlgᴰ.wt-rdᴰ true xt xf xtᴰ xfᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-rd _ _ _)
      , Bᴰ.wt-rdᴰ _ _ _ _ _)
    push .StateAlgᴰ.rd-wtᴰ x xᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.rd-wt _)
      , Bᴰ.rd-wtᴰ _ _)
    push .StateAlgᴰ.wt-wtᴰ b b' x xᴰ = ΣPathP
      ( ΣPathPProp (λ _ → isSetB' _ _)
        (B.wt-wt _ _ _)
      , Bᴰ.wt-wtᴰ _ _ _ _)

    σ : Homoᴰ ϕ Bᴰ push
    σ .Homoᴰ.fᴰ x xᴰ = (x , refl) , xᴰ
    σ .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ = ΣPathP ((ΣPathPProp (λ _ → isSetB' _ _) refl) , refl)
    σ .Homoᴰ.wt-homᴰ b x xᴰ = ΣPathP ((ΣPathPProp (λ _ → isSetB' _ _) refl) , refl)

    --
    module _ {B'' : StateAlg ℓ''}(isSetB'' : isSet (B'' .StateAlg.X))(ψ : Homo B' B'')(Bᴰ'' : StateAlgᴰ B'' ℓᴰ'') where
      private
        module ψ = Homo ψ
        module Bᴰ'' where
          open StateAlgᴰ Bᴰ'' public
          open hSetReasoning (_ , isSetB'') Xᴰ using (rectifyOut) public
      module _ (ϕψᴰ : Homoᴰ (ϕ ⋆Homo ψ) Bᴰ Bᴰ'') where
        private module ϕψᴰ = Homoᴰ ϕψᴰ
        -- Maybe can avoid this using EqFiber but not sure that it's
        -- ultimately helpful to do so?
        recPush : Homoᴰ ψ push Bᴰ''
        recPush .Homoᴰ.fᴰ b' x =
          Bᴰ''.reind (cong ψ.f (x .fst .snd)) (ϕψᴰ.fᴰ (x .fst .fst) (x .snd))
        recPush .Homoᴰ.rd-homᴰ xt xf xtᴰ xfᴰ = Bᴰ''.rectifyOut $
          Bᴰ''.reind-filler⁻ _
          ∙ ϕψᴰ.∫ .Homo.rd-hom _ _
          ∙ cong₂ (Bᴰ''.∫ .StateAlg.rd)
            (Bᴰ''.reind-filler _)
            (Bᴰ''.reind-filler _)
        recPush .Homoᴰ.wt-homᴰ b x xᴰ = Bᴰ''.rectifyOut $
          Bᴰ''.reind-filler⁻ (λ i → ψ.f (StateAlgᴰ.wtᴰ push b xᴰ .fst .snd i))
          ∙ ϕψᴰ.∫ .Homo.wt-hom _ _
          ∙ cong (Bᴰ''.∫ .StateAlg.wt _) (Bᴰ''.reind-filler _)


module _ {X : Type ℓ}(Xᴰ : X → Type ℓᴰ) (B : StateAlg ℓ')
  (i : X → B .StateAlg.X) (isSetB : isSet (B .StateAlg.X))
  where
  private
    module B = StateAlg B

  -- Can we get the universal property for this as a combination of
  -- the universal properties for the others?
  FreeStateAlgⱽ : StateAlgᴰ B (ℓ-max (ℓ-max ℓ ℓᴰ) ℓ')
  FreeStateAlgⱽ = push (recFSA X B i) (FreeStateAlgᴰ X Xᴰ) isSetB

-- summarizing,
-- - we have an opcartesian lift ηᴰ : C [ η ][ Aᴰ , FSAᴰ Aᴰ ] of Aᴰ
-- - we have a opcartesian lifts σ : C [ ϕ ][ Bᴰ , push ϕ ] for any ϕ : B → B'
--
-- Given any M : C [ A , B ] we can construct a heterogeneous
-- opcartesian lift by composition:
-- - ηᴰ ⋆ᴰ σ[ rec M ] : C [ η ⋆ rec M ][ Aᴰ , Bᴰ ]
-- which we can then reind to be C [ M ][ Aᴰ , Bᴰ ]
--
-- - Second we have FSA Aᴰ ↦ F A


-- given M : C [ A , B ] and Aᴰ over A, we can construct push M Aᴰ as a composition:
-- - first, we get a homomorphism rec M : C [ F A , B ]
-- Given Xᴰ over X, we have η : C [ X , FSA X ]
