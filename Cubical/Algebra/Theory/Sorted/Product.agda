-- Binary products of models of a many-sorted theory.
--
-- The carrier is the pointwise `Σ` and the operations are pointwise, so
-- the two β laws hold ON THE NOSE (`×β₁`, `×β₂` are `refl`): `MOD`'s
-- composition is composition of the underlying families, and
-- `cong fst (ΣPathP (p , q))` is `p` by eta.  Only the *equations* of
-- the product cost an argument, and only because `TmRec` into a product
-- is the pair of the two `TmRec`s propositionally rather than
-- judgementally (`TmRec×`).
module Cubical.Algebra.Theory.Sorted.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; Tm; var; node; Ops; TmRec;
         MOD; ModHom)

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX : Level

open SortedSig
open SortedEqns

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  {ℓX : Level} (M N : Category.ob (MOD σeq ℓX)) where

  private
    X : S → Type ℓX
    X s = ⟨ M .fst s ⟩

    Y : S → Type ℓX
    Y s = ⟨ N .fst s ⟩

    α = M .snd .fst
    β = N .snd .fst

    XY : S → hSet ℓX
    XY s = (X s × Y s) , isSet× (M .fst s .snd) (N .fst s .snd)

    αβ : Ops {σ = σ} (λ s → X s × Y s)
    αβ o x = α o (λ a → x a .fst) , β o (λ a → x a .snd)

    -- The only real content: a recursor into a product is the pair of
    -- the recursors.  Not `refl`, since `ts a` is neutral.
    TmRec× : {V : Type ℓv} {vs : V → S}
      (ρ : (v : V) → X (vs v) × Y (vs v))
      {s : S} (t : Tm σ V vs s)
      → TmRec (λ s' → X s' × Y s') αβ ρ t
        ≡ ( TmRec X α (λ v → ρ v .fst) t
          , TmRec Y β (λ v → ρ v .snd) t )
    TmRec× ρ (var v) = refl
    TmRec× ρ (node o ts) =
      ΣPathP ( cong (α o) (funExt (λ a → cong fst (TmRec× ρ (ts a))))
             , cong (β o) (funExt (λ a → cong snd (TmRec× ρ (ts a)))) )

    sat× : (e : σeq .eqns)
      (ρ : (v : σeq .vars e) → X (σeq .varSort e v) × Y (σeq .varSort e v))
      → TmRec (λ s → X s × Y s) αβ ρ (σeq .lhs e)
        ≡ TmRec (λ s → X s × Y s) αβ ρ (σeq .rhs e)
    sat× e ρ =
      TmRec× ρ (σeq .lhs e)
      ∙ ΣPathP ( M .snd .snd e (λ v → ρ v .fst)
               , N .snd .snd e (λ v → ρ v .snd) )
      ∙ sym (TmRec× ρ (σeq .rhs e))

  prodMod : Category.ob (MOD σeq ℓX)
  prodMod = XY , αβ , sat×

  π₁Mod : ModHom σeq ℓX prodMod M
  π₁Mod = (λ _ → fst) , (λ o x y eq → cong fst eq) , tt*

  π₂Mod : ModHom σeq ℓX prodMod N
  π₂Mod = (λ _ → snd) , (λ o x y eq → cong snd eq) , tt*

  module _ (L : Category.ob (MOD σeq ℓX))
    (h : ModHom σeq ℓX L M) (k : ModHom σeq ℓX L N) where

    pairMod : ModHom σeq ℓX L prodMod
    pairMod =
      (λ s l → h .fst s l , k .fst s l)
      , (λ o x y eq →
          ΣPathP (h .snd .fst o x y eq , k .snd .fst o x y eq))
      , tt*

    -- Both β laws are `refl`.
    ×β₁ : Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod} {z = M}
            pairMod π₁Mod
          ≡ h
    ×β₁ = refl

    ×β₂ : Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod} {z = N}
            pairMod π₂Mod
          ≡ k
    ×β₂ = refl

    -- η: the underlying family of any competitor is a pair by eta, so
    -- all that is owed is the two components, and the homomorphism
    -- condition is a path in a set.
    pairUniq : (g : ModHom σeq ℓX L prodMod)
      → Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod} {z = M} g π₁Mod
        ≡ h
      → Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod} {z = N} g π₂Mod
        ≡ k
      → pairMod ≡ g
    pairUniq g p q =
      Σ≡Prop
        (λ _ → isPropΣ
          (isPropΠ4 (λ o x y eq → XY (σ .resultSort o) .snd _ _))
          (λ _ → isPropUnit*))
        (funExt (λ s → funExt (λ l →
          ΣPathP ( sym (funExt⁻ (funExt⁻ (cong fst p) s) l)
                 , sym (funExt⁻ (funExt⁻ (cong fst q) s) l) ))))

  private
    isPropβs : (L : Category.ob (MOD σeq ℓX))
      (h : ModHom σeq ℓX L M) (k : ModHom σeq ℓX L N)
      (f : ModHom σeq ℓX L prodMod)
      → isProp ( (Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod}
                    {z = M} f π₁Mod ≡ h)
               × (Category._⋆_ (MOD σeq ℓX) {x = L} {y = prodMod}
                    {z = N} f π₂Mod ≡ k) )
    isPropβs L h k f =
      isProp× (Category.isSetHom (MOD σeq ℓX) {x = L} {y = M} _ _)
              (Category.isSetHom (MOD σeq ℓX) {x = L} {y = N} _ _)

  isBinProdMod : isBinProduct (MOD σeq ℓX) {x = M} {y = N}
                   {x×y = prodMod} π₁Mod π₂Mod
  isBinProdMod {z = L} h k =
    (pairMod L h k , ×β₁ L h k , ×β₂ L h k)
    , λ g → Σ≡Prop (isPropβs L h k)
        (pairUniq L h k (g .fst) (g .snd .fst) (g .snd .snd))

  BinProdMod : BinProduct (MOD σeq ℓX) M N
  -- `{z}` must be passed explicitly: `MOD`'s hom type is a `Σ` that
  -- does not mention its source, so the object is not recoverable.
  BinProdMod .BinProduct.binProdOb = prodMod
  BinProdMod .BinProduct.binProdPr₁ = π₁Mod
  BinProdMod .BinProduct.binProdPr₂ = π₂Mod
  BinProdMod .BinProduct.univProp {z} = isBinProdMod {z = z}

-- `MOD` has all binary products.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (ℓX : Level) where

  BinProductsMOD : BinProducts (MOD σeq ℓX)
  BinProductsMOD M N = BinProdMod σeq M N

  -- infix notation, once the theory and the level are fixed
  _×Mod_ : (M N : Category.ob (MOD σeq ℓX)) → Category.ob (MOD σeq ℓX)
  M ×Mod N = prodMod σeq M N
