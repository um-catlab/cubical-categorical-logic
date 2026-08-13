-- The product of two direct categories is direct.
module Cubical.Categories.Direct.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_ ; isProp¬)
import Cubical.Data.Equality as Eq

open import Cubical.Induction.WellFounded

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Direct.Base

private
  variable
    ℓc ℓc' ℓe ℓe' ℓD ℓD' ℓ< ℓ<' : Level

  ≤-antisym : (W : WFOrder ℓD ℓ<) {a b : WFOrder.D W}
            → WFOrder._≤_ W a b → WFOrder._≤_ W b a → a Eq.≡ b
  ≤-antisym W (inr a≡b) _         = a≡b
  ≤-antisym W (inl a<b) (inr b≡a) = Eq.sym b≡a
  ≤-antisym W (inl a<b) (inl b<a) =
    ⊥.rec (WFOrder.¬<refl W (WFOrder.trans< W a<b b<a))

-- The lexicographic and product well-founded orders
module _ (Wo : WFOrder ℓD ℓ<) (Wo' : WFOrder ℓD' ℓ<') where
  private
    module W  = WFOrder Wo
    module W' = WFOrder Wo'

    isPropEq : ∀ {a a' : W.D} → isProp (a Eq.≡ a')
    isPropEq {a} {a'} = isOfHLevelRetract 1
      Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (W.isSetD a a')

  -- Lexicographic order
  _<Lex_ : (W.D × W'.D) → (W.D × W'.D) → Type (ℓ-max ℓ< (ℓ-max ℓD ℓ<'))
  (a , b) <Lex (a' , b') = (a W.< a') ⊎ ((a Eq.≡ a') × (b W'.< b'))

  private
    isProp<Lex : ∀ p q → isProp (p <Lex q)
    isProp<Lex (a , b) (a' , b') =
      isProp⊎ (W.isProp< a a') (isProp× isPropEq (W'.isProp< b b')) disjoint
      where
        disjoint : (a W.< a') → ((a Eq.≡ a') × (b W'.< b')) → ⊥
        disjoint a<a' (a≡a' , _) = W.¬<refl (Eq.transport (a W.<_) (Eq.sym a≡a') a<a')

    trans<Lex : ∀ {p q r} → p <Lex q → q <Lex r → p <Lex r
    trans<Lex (inl a<a')          (inl a'<a'')          = inl (W.trans< a<a' a'<a'')
    trans<Lex {p = a , _} (inl a<a') (inr (a'≡a'' , _)) =
      inl (Eq.transport (a W.<_) a'≡a'' a<a')
    trans<Lex {r = a'' , _} (inr (a≡a' , _)) (inl a'<a'') =
      inl (Eq.transport (W._< a'') (Eq.sym a≡a') a'<a'')
    trans<Lex (inr (a≡a' , b<b')) (inr (a'≡a'' , b'<b'')) =
      inr (a≡a' Eq.∙ a'≡a'' , W'.trans< b<b' b'<b'')

    wf<Lex : WellFounded _<Lex_
    wf<Lex (a , b) = go a (W.wf< a) b (W'.wf< b)
      where
        go : ∀ a → Acc W._<_ a → ∀ b → Acc W'._<_ b → Acc _<Lex_ (a , b)
        go a aA@(acc rsA) b (acc rsB) = acc λ where
          (a' , b') (inl a'<a)             → go a' (rsA a' a'<a) b' (W'.wf< b')
          (a' , b') (inr (Eq.refl , b'<b)) → go a  aA            b' (rsB b' b'<b)

  LexWFOrder : WFOrder (ℓ-max ℓD ℓD') (ℓ-max ℓ< (ℓ-max ℓD ℓ<'))
  LexWFOrder = record
    { D       = W.D × W'.D
    ; isSetD  = isSet× W.isSetD W'.isSetD
    ; _<_     = _<Lex_
    ; isProp< = isProp<Lex
    ; trans<  = trans<Lex
    ; wf<     = wf<Lex
    }

  -- Product order
  _<Prod_ : (W.D × W'.D) → (W.D × W'.D)
       → Type (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓ< ℓ<'))
  (a , b) <Prod (a' , b') =
    (a W.≤ a') × (b W'.≤ b') × (¬ ((a Eq.≡ a') × (b Eq.≡ b')))

  private
    isProp<Prod : ∀ p q → isProp (p <Prod q)
    isProp<Prod (a , b) (a' , b') =
      isProp× W.isProp≤ (isProp× W'.isProp≤ (isProp¬ _))

    trans<Prod : ∀ {p q r} → p <Prod q → q <Prod r → p <Prod r
    trans<Prod {a , b} {a' , b'} {a'' , b''}
            (a≤a' , b≤b' , ne) (a'≤a'' , b'≤b'' , _) =
      W.≤-trans a≤a' a'≤a'' , W'.≤-trans b≤b' b'≤b'' , ne''
      where
        -- If `(a,b) = (a'',b'')` then, sandwiched by the ≤'s, also
        -- `(a,b) = (a',b')`, contradicting the first strictness witness.
        ne'' : ¬ ((a Eq.≡ a'') × (b Eq.≡ b''))
        ne'' (a≡a'' , b≡b'') = ne
          ( ≤-antisym Wo  a≤a' (Eq.transport (a' W.≤_)  (Eq.sym a≡a'') a'≤a'')
          , ≤-antisym Wo' b≤b' (Eq.transport (b' W'.≤_) (Eq.sym b≡b'') b'≤b'') )

    -- `_<Prod_ ⊆ _<Lex_`, so accessibility for lex transfers to product order.
    <Prod→<Lex : ∀ {p q} → p <Prod q → p <Lex q
    <Prod→<Lex (inl a<a' , _        , _)  = inl a<a'
    <Prod→<Lex (inr a≡a' , inl b<b' , _)  = inr (a≡a' , b<b')
    <Prod→<Lex (inr a≡a' , inr b≡b' , ne) = ⊥.rec (ne (a≡a' , b≡b'))

    wf<Prod : WellFounded _<Prod_
    wf<Prod p = go p (wf<Lex p)
      where
        go : ∀ p → Acc _<Lex_ p → Acc _<Prod_ p
        go p (acc r) = acc λ q q<p → go q (r q (<Prod→<Lex q<p))

  ProdWFOrder : WFOrder (ℓ-max ℓD ℓD') (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓ< ℓ<'))
  ProdWFOrder = record
    { D       = W.D × W'.D
    ; isSetD  = isSet× W.isSetD W'.isSetD
    ; _<_     = _<Prod_
    ; isProp< = isProp<Prod
    ; trans<  = trans<Prod
    ; wf<     = wf<Prod
    }

-- The product of two direct categories, over either order.
module _ {C : Category ℓc ℓc'} {D : Category ℓe ℓe'}
         {Wo : WFOrder ℓD ℓ<} {Wo' : WFOrder ℓD' ℓ<'} where
  private
    module W  = WFOrder Wo
    module W' = WFOrder Wo'

  -- Directness over the lexicographic order
  LexDirect : DirectStr C Wo → DirectStr D Wo'
              → DirectStr (C ×C D) (LexWFOrder Wo Wo')
  LexDirect dirC dirD =
    mkDirectStr (C ×C D) (LexWFOrder Wo Wo') deg× non-dec×
    where
      open DirectNotation dirC using () renaming (deg to degC ; non-dec to non-decC)
      open DirectNotation dirD using () renaming (deg to degD ; non-dec to non-decD)

      deg× : Category.ob (C ×C D) → W.D × W'.D
      deg× (c , d) = degC c , degD d

      -- component-wise `≤` (from the two non-decreasing degrees) is a lex `≤`.
      lex≤ : ∀ {a a' b b'} → a W.≤ a' → b W'.≤ b'
           → WFOrder._≤_ (LexWFOrder Wo Wo') (a , b) (a' , b')
      lex≤ (inl a<a')     _              = inl (inl a<a')
      lex≤ (inr Eq.refl) (inl b<b')      = inl (inr (Eq.refl , b<b'))
      lex≤ (inr Eq.refl) (inr Eq.refl)   = inr Eq.refl

      non-dec× : ∀ {x y} → (C ×C D) [ x , y ]
               → WFOrder._≤_ (LexWFOrder Wo Wo') (deg× x) (deg× y)
      non-dec× (f , g) = lex≤ (non-decC f) (non-decD g)

  -- Directness over the product order.
  ProdDirect : DirectStr C Wo → DirectStr D Wo'
               → DirectStr (C ×C D) (ProdWFOrder Wo Wo')
  ProdDirect dirC dirD =
    mkDirectStr (C ×C D) (ProdWFOrder Wo Wo') deg× non-dec×
    where
      open DirectNotation dirC using () renaming (deg to degC ; non-dec to non-decC)
      open DirectNotation dirD using () renaming (deg to degD ; non-dec to non-decD)

      deg× : Category.ob (C ×C D) → W.D × W'.D
      deg× (c , d) = degC c , degD d

      -- component-wise `≤` IS the product `≤` (equal pairs go to `inr`).
      prod≤ : ∀ {a a' b b'} → a W.≤ a' → b W'.≤ b'
            → WFOrder._≤_ (ProdWFOrder Wo Wo') (a , b) (a' , b')
      prod≤ {a} (inl a<a') b≤b' =
        inl (inl a<a' , b≤b'
            , λ (a≡a' , _) → W.¬<refl (Eq.transport (a W.<_) (Eq.sym a≡a') a<a'))
      prod≤ {b = b} (inr a≡a') (inl b<b') =
        inl (inr a≡a' , inl b<b'
            , λ (_ , b≡b') → W'.¬<refl (Eq.transport (b W'.<_) (Eq.sym b≡b') b<b'))
      prod≤ (inr Eq.refl) (inr Eq.refl) = inr Eq.refl

      non-dec× : ∀ {x y} → (C ×C D) [ x , y ]
               → WFOrder._≤_ (ProdWFOrder Wo Wo') (deg× x) (deg× y)
      non-dec× (f , g) = prod≤ (non-decC f) (non-decD g)
