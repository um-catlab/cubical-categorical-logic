{-# OPTIONS --lossy-unification #-}
-- Intrinsically verified shortest paths as a guarded fixpoint
--
-- It is generic over a selective ordered semiring for the graph weights.
-- "Selective" means x ⊕ y always returns either x or y
module Cubical.Categories.Direct.Examples.ShortestPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_≤_)
import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.FinData
  using (Fin ; zero ; suc ; discreteFin ; toℕ ; isSetFin)
open import Cubical.Data.Vec.Base using (Vec)
open import Cubical.Data.Vec.Properties
  using (FinVec→Vec ; Vec→FinVec ; FinVec→Vec→FinVec ; FinVec≃Vec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Relation.Nullary using (Dec ; yes ; no)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct using (_×C_)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Instances.DirectedGraph
  using (GraphPsh ; module Graph ; isFiniteGraph ; Disc ; finDisc)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Product using (LexWFOrder ; LexDirect)
open import Cubical.Categories.Direct.StrictDownset
  using (▷Fam ; ▷FamApp ; löbFam)
open import Cubical.Categories.Direct.Instances.Nat
  using (ℕWFOrder ; ℕCat ; ℕDirect)
import Cubical.Categories.Direct.Instances.ParallelPair as PP
open import Cubical.Algebra.OrderedSemiring.Selective
open import Cubical.Algebra.OrderedSemiring.MinPlus using (MinPlusSel)
open import Cubical.Algebra.OrderedSemiring.Bool using (BooleanSel)
open import Cubical.Data.Maybe using (just ; nothing)
open import Cubical.Data.Nat.More using (Cost)

open PshHomStrict

Listing : GraphPsh ℓ-zero → Type
Listing Q = Σ[ n ∈ ℕ ] Σ[ vtx ∈ (Fin n → Graph.Vertex Q) ]
              (∀ v → Σ[ i ∈ Fin n ] vtx i ≡ v)

module _ (SR : SelectiveSemiring ℓ-zero) where
  open SelectiveSemiring SR

  ⨁Fin : ∀ {n} → (Fin n → R) → R
  ⨁Fin {zero}  f = 𝟘
  ⨁Fin {suc n} f = f zero ⊕ ⨁Fin (λ i → f (suc i))

  ⨁Fin-lb : ∀ {n} (f : Fin n → R) (i : Fin n) → ⨁Fin f ⊑ f i
  ⨁Fin-lb f zero    = ⊕-lb₁ (f zero) _
  ⨁Fin-lb f (suc i) = ⊕-skip (f zero) (⨁Fin-lb (λ j → f (suc j)) i)

  ≤suc : ∀ {j n} → j ≤ n → j ≤ suc n
  ≤suc {j} {n} jn =
    Ord.≤-trans {j} {n} {suc n} jn
      (Ord.<-weaken {n} {suc n} (Ord.≤-refl (suc n)))

  ShapeCat : Category ℓ-zero ℓ-zero
  ShapeCat = ℕCat ×C PP.ParallelPair

  ShapeWF : WFOrder ℓ-zero ℓ-zero
  ShapeWF = LexWFOrder ℕWFOrder ℕWFOrder

  ShapeDir : DirectStr {C = ShapeCat} ShapeWF
  ShapeDir = LexDirect ℕDirect PP.ParallelPairDirect

  open DirectNotation ShapeDir using (_≺_)

  ℕid : ∀ {n} → ℕCat [ n , n ]
  ℕid = inr Eq.refl
  ℕup : ∀ {n} → ℕCat [ n , suc n ]
  ℕup {n} = inl (Ord.≤-refl (suc n))
  ↓time : ∀ {n} → (n , PP.E) ≺ (suc n , PP.E)
  ↓time {n} = inl (Ord.≤-refl (suc n))
  ↓layer : ∀ {n} → (n , PP.V) ≺ (n , PP.E)
  ↓layer = inr (Eq.refl , _)

  module Search (Q : GraphPsh ℓ-zero) (fin : Listing Q)
                (weight : Graph.Vertex Q → Graph.Vertex Q → R)
                (source : Graph.Vertex Q) where
    open Graph Q
    N : ℕ
    N = fin .fst
    vtx : Fin N → Vertex
    vtx = fin .snd .fst
    coverV : ∀ v → Σ[ i ∈ Fin N ] vtx i ≡ v
    coverV = fin .snd .snd
    w : Fin N → Fin N → R
    w i j = weight (vtx i) (vtx j)
    src₀ : Fin N
    src₀ = coverV source .fst

    data Walk : ℕ → Fin N → Type where
      nil  : Walk 0 src₀
      snoc : ∀ {k u} → Walk k u → (v : Fin N) → Walk (suc k) v

    pcost : ∀ {k v} → Walk k v → R
    pcost nil                = 𝟙
    pcost (snoc {u = u} p v) = pcost p ⊗ w u v

    WalkRep : ℕ → Fin N → Type
    WalkRep zero    v = src₀ Eq.≡ v
    WalkRep (suc k) v = Σ[ u ∈ Fin N ] WalkRep k u
    isSetWalkRep : ∀ k v → isSet (WalkRep k v)
    isSetWalkRep zero    v = isProp→isSet (isOfHLevelRetract 1
      Eq.eqToPath Eq.pathToEq Eq.pathToEq-eqToPath (isSetFin src₀ v))
    isSetWalkRep (suc k) v = isSetΣ isSetFin (λ u → isSetWalkRep k u)
    toRep : ∀ {k v} → Walk k v → WalkRep k v
    toRep nil                = Eq.refl
    toRep (snoc {u = u} p v) = u , toRep p
    fromRep : ∀ {k v} → WalkRep k v → Walk k v
    fromRep {k = zero}      Eq.refl = nil
    fromRep {k = suc k} {v} (u , r) = snoc (fromRep r) v
    fromRep-toRep : ∀ {k v} (p : Walk k v) → fromRep (toRep p) ≡ p
    fromRep-toRep nil        = refl
    fromRep-toRep (snoc p v) = cong (λ q → snoc q v) (fromRep-toRep p)
    isSetWalk : ∀ {k v} → isSet (Walk k v)
    isSetWalk {k} {v} =
      isOfHLevelRetract 2 toRep fromRep fromRep-toRep (isSetWalkRep k v)

    relaxF : (Fin N → Fin N → R) → (Fin N → R) → Fin N → R
    relaxF ec d v = d v ⊕ ⨁Fin (λ i → d i ⊗ ec i v)
    relax : (Fin N → Fin N → R) → Vec R N → Vec R N
    relax ec dv = FinVec→Vec (relaxF ec (Vec→FinVec dv))

    relax-β : ∀ ec dv → Vec→FinVec (relax ec dv) ≡ relaxF ec (Vec→FinVec dv)
    relax-β ec dv = FinVec→Vec→FinVec (relaxF ec (Vec→FinVec dv))

    relax-keeps : ∀ ec d v → relaxF ec d v ⊑ d v
    relax-keeps ec d v = ⊕-lb₁ (d v) _
    relax-lb : ∀ ec d u v → relaxF ec d v ⊑ (d u ⊗ ec u v)
    relax-lb ec d u v = ⊕-skip (d v) (⨁Fin-lb (λ i → d i ⊗ ec i v) u)

    LowerBound : ℕ → (Fin N → R) → Type
    LowerBound m d = ∀ {j v} (p : Walk j v) → j ≤ m → d v ⊑ pcost p
    isPropLowerBound : ∀ m d → isProp (LowerBound m d)
    isPropLowerBound m d = isPropImplicitΠ λ _ → isPropImplicitΠ λ _ →
      isPropΠ λ _ → isPropΠ λ _ → isProp⊑

    AchAt : ℕ → R → Fin N → Type
    AchAt m c v =
      (c ≡ 𝟘) ⊎ (Σ[ j ∈ ℕ ] Σ[ p ∈ Walk j v ] (j ≤ m) × (pcost p ≡ c))
    isSetAchAt : ∀ m c v → isSet (AchAt m c v)
    isSetAchAt m c v = isSet⊎ (isProp→isSet (isSetR c 𝟘))
      (isSetΣ isSetℕ λ j → isSetΣ isSetWalk λ p →
        isSet× (isProp→isSet (Ord.isProp≤ {j} {m})) (isProp→isSet (isSetR _ _)))
    Attained : ℕ → (Fin N → R) → Type
    Attained m d = ∀ v → AchAt m (d v) v
    isSetAttained : ∀ m d → isSet (Attained m d)
    isSetAttained m d = isSetΠ λ v → isSetAchAt m (d v) v

    weakenA : ∀ {m c v} → AchAt m c v → AchAt (suc m) c v
    weakenA (inl e)                 = inl e
    weakenA (inr (j , p , le , eq)) = inr (j , p , ≤suc {j} le , eq)
    extendA : ∀ {m c u} v → AchAt m c u → AchAt (suc m) (c ⊗ w u v) v
    extendA {u = u} v (inl e) =
      inl (cong (_⊗ w u v) e ∙ ⊗-annihilˡ (w u v))
    extendA {u = u} v (inr (j , p , le , eq)) =
      inr (suc j , snoc p v , le , cong (_⊗ w u v) eq)
    combineA : ∀ {m c₁ c₂ v} → AchAt m c₁ v → AchAt m c₂ v → AchAt m (c₁ ⊕ c₂) v
    combineA {m} {c₁} {c₂} {v} a₁ a₂ with ⊕-select c₁ c₂
    ... | inl e = subst (λ c → AchAt m c v) (sym e) a₁
    ... | inr e = subst (λ c → AchAt m c v) (sym e) a₂

    base? : ∀ (v : Fin N) → Dec (src₀ ≡ v) → R
    base? _ (yes _) = 𝟙
    base? _ (no  _) = 𝟘
    base : Fin N → R
    base v = base? v (discreteFin src₀ v)
    walk0 : ∀ {v} → src₀ ≡ v → Walk 0 v
    walk0 e = subst (Walk 0) e nil
    pcost-walk0 : ∀ {v} (e : src₀ ≡ v) → pcost (walk0 e) ≡ 𝟙
    pcost-walk0 = J (λ _ e → pcost (walk0 e) ≡ 𝟙)
      (cong pcost (substRefl {B = Walk 0} nil))
    base?-lb : (dec : Dec (src₀ ≡ src₀)) → base? src₀ dec ⊑ 𝟙
    base?-lb (yes _) = ⊑-refl
    base?-lb (no ¬e) = ⊥.rec (¬e refl)
    base?-att : ∀ v (dec : Dec (src₀ ≡ v)) → AchAt 0 (base? v dec) v
    base?-att v (yes e) = inr (0 , walk0 e , tt , pcost-walk0 e)
    base?-att v (no  _) = inl refl

    isSetVecR : isSet (Vec R N)
    isSetVecR = isOfHLevelRespectEquiv 2 (FinVec≃Vec N) (isSetΠ λ _ → isSetR)

    Carrier : Category.ob ShapeCat → hSet ℓ-zero
    Carrier (n , PP.V) =
        (Σ[ ec ∈ (Fin N → Fin N → R) ] (∀ i j → ec i j ≡ w i j))
      , isSetΣ (isSetΠ λ _ → isSetΠ λ _ → isSetR)
               (λ _ → isProp→isSet (isPropΠ λ _ → isPropΠ λ _ → isSetR _ _))
    Carrier (n , PP.E) =
        ( Σ[ dv ∈ Vec R N ]
          (LowerBound n (Vec→FinVec dv) × Attained n (Vec→FinVec dv)) )
      , isSetΣ isSetVecR
               (λ dv →
                 isSet× (isProp→isSet (isPropLowerBound n (Vec→FinVec dv)))
                              (isSetAttained n (Vec→FinVec dv)))

    step : ∀ x → ⟨ ▷Fam ShapeDir {ℓF = ℓ-zero} Carrier x ⟩ → ⟨ Carrier x ⟩
    step (n     , PP.V) β = w , λ _ _ → refl
    step (zero  , PP.E) β = FinVec→Vec base , lb0 , att0
      where
        memo0 : Vec→FinVec (FinVec→Vec base) ≡ base
        memo0 = FinVec→Vec→FinVec base
        lb0 : LowerBound 0 (Vec→FinVec (FinVec→Vec base))
        lb0 = subst (LowerBound 0) (sym memo0) lb0'
          where lb0' : LowerBound 0 base
                lb0' nil        _  = base?-lb (discreteFin src₀ src₀)
                lb0' (snoc _ _) le = ⊥.rec le
        att0 : Attained 0 (Vec→FinVec (FinVec→Vec base))
        att0 = subst (Attained 0) (sym memo0) att0'
          where att0' : Attained 0 base
                att0' v = base?-att v (discreteFin src₀ v)
    step (suc n , PP.E) β = relax edgeCost prevDv , lbS , attS
      where
        rec : ∀ y → ShapeCat [ y , (suc n , PP.E) ]
            → y ≺ (suc n , PP.E) → ⟨ Carrier y ⟩
        rec y g q = ▷FamApp ShapeDir {ℓF = ℓ-zero} Carrier β g q
        prev    = rec (n , PP.E) (ℕup , PP.idH PP.E) ↓time
        prevDv  = prev .fst
        prevD   = Vec→FinVec prevDv
        prevLB  = prev .snd .fst
        prevAtt = prev .snd .snd
        wRead   = rec (suc n , PP.V) (ℕid , true) ↓layer
        edgeCost : Fin N → Fin N → R
        edgeCost = wRead .fst
        conn : Vec→FinVec (relax edgeCost prevDv) ≡ relaxF w prevD
        conn = relax-β edgeCost prevDv
             ∙ cong (λ ec → relaxF ec prevD)
                 (funExt λ i → funExt λ j → wRead .snd i j)
        lbS' : LowerBound (suc n) (relaxF w prevD)
        lbS' nil                _  =
          ⊑-trans (relax-keeps w prevD src₀) (prevLB nil _)
        lbS' (snoc {u = u} p v) le =
          ⊑-trans (relax-lb w prevD u v) (⊗-monoˡ (w u v) (prevLB p le))
        attS' : Attained (suc n) (relaxF w prevD)
        attS' v = combineA (weakenA (prevAtt v)) (go (λ i → i))
          where
            go : ∀ {k} (g : Fin k → Fin N)
               → AchAt (suc n) (⨁Fin (λ i → prevD (g i) ⊗ w (g i) v)) v
            go {zero}  g = inl refl
            go {suc k} g =
              combineA (extendA v (prevAtt (g zero))) (go (λ i → g (suc i)))
        lbS : LowerBound (suc n) (Vec→FinVec (relax edgeCost prevDv))
        lbS = subst (LowerBound (suc n)) (sym conn) lbS'
        attS : Attained (suc n) (Vec→FinVec (relax edgeCost prevDv))
        attS = subst (Attained (suc n)) (sym conn) attS'

    dist : ℕ → Fin N → R
    dist n =
      Vec→FinVec (löbFam ShapeDir {ℓF = ℓ-zero} Carrier step (n , PP.E) .fst)

    optimal : ∀ n {j v} (p : Walk j v) → j ≤ n → dist n v ⊑ pcost p
    optimal n = löbFam ShapeDir {ℓF = ℓ-zero} Carrier step (n , PP.E) .snd .fst

    attained : ∀ n v → AchAt n (dist n v) v
    attained n = löbFam ShapeDir {ℓF = ℓ-zero} Carrier step (n , PP.E) .snd .snd

    shortest : Fin N → R
    shortest = dist N

    shortest-optimal : ∀ {j v} (p : Walk j v) → j ≤ N → shortest v ⊑ pcost p
    shortest-optimal = optimal N

    shortest-attained : ∀ v → AchAt N (shortest v) v
    shortest-attained = attained N

module Example where
  --       7
  --   ┌─────────────────────┐
  --   │                     ▼
  --   │        ┌───┐  1   ┌────┐       7
  --   │        │ 7 │ ───▶ │ 5  │ ◀─────────────────┐
  --   │        └───┘      └────┘                   │
  --   │              5                             │
  --   │          ┌──────────────────────┐          │
  --   │          │                      ▼          │
  -- ┌───┐  5   ┌───┐  4   ┌────┐  2   ┌───┐  3   ┌───┐
  -- │ 3 │ ◀─── │ 0 │ ───▶ │    │ ───▶ │ 4 │ ───▶ │ 6 │
  -- └───┘      └───┘      │ 2  │      └───┘      └───┘
  --              ▲   1    │    │  3     │
  --              └─────── │    │ ◀──────┘
  --                       └────┘
  --                         │
  --                         │ 2
  --                         ▼
  --                       ┌────┐
  --                       │ 1  │
  --                       └────┘
  G : GraphPsh ℓ-zero
  G = Disc 8
  _ : isFiniteGraph G
  _ = finDisc 8
  finG : Listing G
  finG = 8 , (λ i → i) , (λ v → v , refl)

  wN : ℕ → ℕ → Cost
  wN 0 2 = just 4
  wN 0 3 = just 5
  wN 0 4 = just 5
  wN 2 0 = just 1
  wN 2 1 = just 2
  wN 2 4 = just 2
  wN 3 5 = just 7
  wN 4 2 = just 3
  wN 4 6 = just 3
  wN 6 5 = just 7
  wN 7 5 = just 1
  wN _ _ = nothing
  wMP : Fin 8 → Fin 8 → Cost
  wMP i j = wN (toℕ i) (toℕ j)

  bN : ℕ → ℕ → Bool
  bN 0 2 = true
  bN 0 3 = true
  bN 0 4 = true
  bN 2 0 = true
  bN 2 1 = true
  bN 2 4 = true
  bN 3 5 = true
  bN 4 2 = true
  bN 4 6 = true
  bN 6 5 = true
  bN 7 5 = true
  bN _ _ = false
  wB : Fin 8 → Fin 8 → Bool
  wB i j = bN (toℕ i) (toℕ j)

  v1 v2 v3 v5 v7 : Fin 8
  v1 = suc zero
  v2 = suc (suc zero)
  v3 = suc (suc (suc zero))
  v5 = suc (suc (suc (suc (suc zero))))
  v7 = suc (suc (suc (suc (suc (suc (suc zero))))))

  _ : Search.shortest MinPlusSel G finG wMP v2 v3 ≡ just 6    -- 2→0→3
  _ = refl
  -- 2→4→6→5 (cheaper than 2→0→3→5 = 13)
  _ : Search.shortest MinPlusSel G finG wMP v2 v5 ≡ just 12
  _ = refl
  -- 7 has no in-edge: unreachable (∞)
  _ : Search.shortest MinPlusSel G finG wMP v2 v7 ≡ nothing
  _ = refl
  -- this could replace Cubical.Data.Quiver.Reachability upstream
  _ : Search.shortest BooleanSel G finG wB v2 v1 ≡ true       -- 2→1, reachable
  _ = refl
  _ : Search.shortest BooleanSel G finG wB v2 v7 ≡ false      -- unreachable
  _ = refl
