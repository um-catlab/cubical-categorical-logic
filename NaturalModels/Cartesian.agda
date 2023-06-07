module NaturalModels.Cartesian where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.FinSet

open import UMP
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism

open Category
open CartesianCategory
open UnivElt
open isUniversal

record SimplyTypedCategory (ℓb ℓb' ℓt ℓt' : Level) : Type (ℓ-suc (ℓ-max ℓb (ℓ-max ℓb' (ℓ-max ℓt ℓt')))) where
  field
    -- A cartesian category B of contexts and substitutions
    B    : CartesianCategory ℓb ℓb'
    -- a type of objects and for each object a presheaf of terms for that object
    Ty   : Type ℓt
    Tm   : ∀ (A : Ty) → Presheaf (B .cat) ℓt'
    -- Tm A is always representable, this defines a context containing a single variable
    Tm-repr : ∀ (A : Ty) → UnivElt (B .cat) (Tm A)

  sole : ∀ (A : Ty) → B .cat .ob
  sole A = Tm-repr A .vertex

  the-var : ∀ {A} → (Tm A ⟅ sole A ⟆) .fst
  the-var = Tm-repr _ .element

  _/the-var : ∀ {Γ A} → (Tm A ⟅ Γ ⟆) .fst → B .cat [ Γ , sole A ]
  _/the-var M = Tm-repr _ .universal .coinduction M

  _⟨_⟩S : ∀ {Δ Γ A} → (Tm A ⟅ Γ ⟆) .fst → B .cat [ Δ , Γ ] → (Tm A ⟅ Δ ⟆) .fst
  M ⟨ γ ⟩S = B .cat [ M ∘ᴾ⟨ Tm _ ⟩ γ ]

  ⟨/the-var⟩ : ∀ {Γ A} (M : (Tm A ⟅ Γ ⟆) .fst)
             → the-var ⟨ M /the-var ⟩S ≡ M
  ⟨/the-var⟩ = Tm-repr _ .universal .commutes

  /the-var⟨⟩S : ∀ {Δ Γ A} (M : (Tm A ⟅ Γ ⟆) .fst) (γ : B .cat [ Δ , Γ ])
              → (M /the-var) ∘⟨ B .cat ⟩ γ ≡ (M ⟨ γ ⟩S) /the-var
  /the-var⟨⟩S M γ = Tm-repr _ .universal .is-uniq (M ⟨ γ ⟩S) ((M /the-var) ∘⟨ B .cat ⟩ γ)
    (the-var ⟨ M /the-var ∘⟨ B .cat ⟩ γ ⟩S
      ≡⟨ ∘ᴾAssoc (B .cat) (Tm _) _ _ _ ⟩
    the-var ⟨ M /the-var ⟩S ⟨ γ ⟩S
      ≡[ i ]⟨ ⟨/the-var⟩ M i ⟨ γ ⟩S ⟩
    M ⟨ γ ⟩S ∎)

open SimplyTypedCategory
open Functor
open NatTrans

record STC-Functor {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       (C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct')
       (D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt') :
       Type (ℓ-max ℓcb (ℓ-max ℓcb' (ℓ-max ℓct (ℓ-max ℓct' (ℓ-max ℓdb (ℓ-max ℓdb' (ℓ-max ℓdt (ℓ-max ℓdt' (ℓ-suc ℓ-zero))))))))) where
  open CartesianFunctor
  field
    F-B : CartesianFunctor (C .B) (D .B)
    F-Ty : C .Ty → D .Ty
    F-Tm : ∀ A → PshHom (F-B .func) (C .Tm A) (D .Tm (F-Ty A))
    F-Tm-repr : ∀ A → preserves-representation (F-B .func) (C .Tm A) (D .Tm (F-Ty A)) (F-Tm A) (C .Tm-repr A)

-- | Universal Properties
private
  variable
    ℓb ℓb' ℓt ℓt' ℓp : Level

-- A presheaf P on the base category is representable as a type when
-- there is an object of the STC whose presheaf of terms is equivelent
-- to P
TypeRepresentation : ∀ (C : SimplyTypedCategory ℓb ℓb' ℓt ℓt') → (P : Presheaf (C .B .cat) ℓp) → Type _
TypeRepresentation C P = Σ[ A ∈ C .Ty ] PshIso (C .B .cat) (C .Tm A) P

-- TerminalType : ∀ (C : SimplyTypedCategory ℓb ℓb' ℓt ℓt') → TypeRepresentation C (presheaf-Prod (C .B .cat) (⊥, ?) (λ ()))

-- AllProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- AllProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ty)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

-- FinProductTypes : ∀ {ℓo ℓt} → SimplyTypedCategory ℓo ℓt → Type (ℓ-max ℓo (ℓ-suc ℓt))
-- FinProductTypes {ℓo}{ℓt} C =
--   ∀ (J : Type ℓt) (D : J → C .Ty)
--   → TypeRepresentation C (presheaf-Prod (C .B .cat) J (λ j → C .Tm (D j)))

-- | TODO: Exponentials as representing the exponential of presheaves
-- | or the more syntactic-looking Tm (a => b) G =~ Tm b (G x sole A)

-- | TODO: coproducts are "just" coproducts in the category of terms
-- | with a free variable.

-- module _ {ℓcb ℓcb' ℓct ℓct'} (C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct') where
--   module C = SimplyTypedCategory C

--   _×sole_ : C.B .cat .ob → C .Ty → C.B .cat .ob
--   Γ ×sole B = bin-prod-ob C.B Γ (sole C B)
--   Unary : C .B .cat .ob → Category ℓct ℓct'
--   Unary Γ .ob = C.Ty
--   Unary Γ .Hom[_,_] B A = (C.Tm A ⟅ Γ ×sole B ⟆) .fst
--   Unary Γ .id = C.B .cat [ the-var C ∘ᴾ⟨ C.Tm _ ⟩ π₂ C.B _ _ ]
--   Unary Γ ._⋆_ N M = C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ prod₂-I C.B _ _ (π₁ C.B _ _) (_/the-var C N) ]
--   Unary Γ .⋆IdL M =
--     C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ prod₂-I C.B _ _ (π₁ C.B _ _) (_/the-var C (Unary Γ .id)) ]
--       ≡[ i ]⟨ C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ prod₂-I C.B _ _ (π₁ C.B _ _) (η-expansion (C .Tm-repr _ .universal) (π₂ C.B _ _) (~ i)) ] ⟩
--     C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ prod₂-I C.B _ _ (π₁ C.B _ _) (π₂ C.B _ _) ]
--       ≡[ i ]⟨ C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ η-expansion (finite-products C.B _ _ .universal) {!!} {!i!} ] ⟩
--     C.B .cat [ M ∘ᴾ⟨ C.Tm _ ⟩ C.B .cat .id ]
--       ≡⟨ {!!} ⟩
--     M ∎
--     -- tms : (j : Bool) → cat C.B [ Γ ×sole _ , if j then Γ else C.sole _ ]
--     -- tms true =
--   Unary Γ .⋆IdR = {!!}
--   Unary Γ .⋆Assoc = {!!}
--   Unary Γ .isSetHom = {!!}
--   -- Unary Γ
-- -- Unary C Γ .ob = C .Ty
-- -- Unary C Γ .Hom[_,_] a b = (C .Tm b ⟅ prod-ob (C .B) (Bool , isFinSetBool) ctx ⟆) .fst
-- --   where
-- --     ctx : Bool → C .B .cat .ob
-- --     ctx false = Γ
-- --     ctx true = sole C a
-- -- Unary C Γ .id = C .B .cat [ the-var C ∘ᴾ⟨ C .Tm _ ⟩ {!!}  ]
-- -- Unary C Γ ._⋆_ = {!!}
-- -- Unary C Γ .⋆IdL = {!!}
-- -- Unary C Γ .⋆IdR = {!!}
-- -- Unary C Γ .⋆Assoc = {!!}
-- -- Unary C Γ .isSetHom = {!!}


open STC-Functor
open CartesianFunctor
STC-NatTrans : ∀ {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       {C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct'}
       {D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt'}
       (F G : STC-Functor C D) → Type (ℓ-max (ℓ-max ℓcb ℓcb') ℓdb')
STC-NatTrans F G = NatTrans (F .F-B .func) (G .F-B .func)

STC-NatIso : ∀ {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
       {C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct'}
       {D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt'}
       (F G : STC-Functor C D) → Type (ℓ-max (ℓ-max (ℓ-max ℓcb ℓcb') ℓdb) ℓdb')
STC-NatIso F G = NatIso (F .F-B .func) (G .F-B .func)

-- This should be determined by
-- N-Tm : ∀ (A : C .Ty) → (D .Tm (G .F-Ty A) ⟅ sole D (F .F-Ty A) ⟆) .fst

-- record STC-Transformation' {ℓcb ℓcb' ℓct ℓct' ℓdb ℓdb' ℓdt ℓdt'}
--        {C : SimplyTypedCategory ℓcb ℓcb' ℓct ℓct'}
--        {D : SimplyTypedCategory ℓdb ℓdb' ℓdt ℓdt'}
--        (F G : STC-Functor C D) : Type {!!} where
--   field
--     N-Tm : ∀ (A : C .Ty) → (D .Tm (G .F-Ty A) ⟅ sole D (F .F-Ty A) ⟆) .fst
--     N-Tm-nat : ∀ {Γ : C .B .cat .ob}{A : C .Ty}
--              → (M : (C .Tm A ⟅ Γ ⟆) .fst)
--              → D .B .cat [ G .F-Tm A .N-ob _ (lift M) .lower ∘ᴾ⟨ D .Tm (G .F-Ty A) ⟩ {!!} ]
--                ≡ {!!}

