{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.DirectedGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin ; isSetFin)
open import Cubical.Data.FinSet.Base using (isFinOrd)
open import Cubical.Data.SumFin using (FinData≃SumFin)
open import Cubical.Foundations.Equiv using (idEquiv)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Direct.Instances.ParallelPair
  using (ParallelPair ; V ; E ; Ob)
open import Cubical.Data.Quiver.Base using (Quiver ; QuiverOver)

open Functor
open Category
open QuiverOver

private
  variable ℓ : Level

GraphPsh : (ℓ : Level) → Type _
GraphPsh ℓ = Presheaf ParallelPair ℓ

mkGraphPsh : (Vt Ed : hSet ℓ) (s t : ⟨ Ed ⟩ → ⟨ Vt ⟩) → GraphPsh ℓ
mkGraphPsh Vt Ed s t .F-ob V = Vt
mkGraphPsh Vt Ed s t .F-ob E = Ed
mkGraphPsh Vt Ed s t .F-hom {V} {V} _     = λ x → x
mkGraphPsh Vt Ed s t .F-hom {V} {E} h     = ⊥.rec h
mkGraphPsh Vt Ed s t .F-hom {E} {V} false = s
mkGraphPsh Vt Ed s t .F-hom {E} {V} true  = t
mkGraphPsh Vt Ed s t .F-hom {E} {E} _     = λ x → x
mkGraphPsh Vt Ed s t .F-id  {V} = refl
mkGraphPsh Vt Ed s t .F-id  {E} = refl
mkGraphPsh Vt Ed s t .F-seq {V} {V} {V} tt    tt    = refl
mkGraphPsh Vt Ed s t .F-seq {E} {V} {V} false tt    = refl
mkGraphPsh Vt Ed s t .F-seq {E} {V} {V} true  tt    = refl
mkGraphPsh Vt Ed s t .F-seq {E} {E} {V} tt    false = refl
mkGraphPsh Vt Ed s t .F-seq {E} {E} {V} tt    true  = refl
mkGraphPsh Vt Ed s t .F-seq {E} {E} {E} tt    tt    = refl
mkGraphPsh Vt Ed s t .F-seq {V} {E} {_} f g = ⊥.rec f
mkGraphPsh Vt Ed s t .F-seq {_} {V} {E} f g = ⊥.rec g

module Graph (Q : GraphPsh ℓ) where
  Vertex : Type ℓ
  Vertex = ⟨ Q .F-ob V ⟩
  Edge : Type ℓ
  Edge = ⟨ Q .F-ob E ⟩
  src tgt : Edge → Vertex
  src = Q .F-hom {E} {V} false
  tgt = Q .F-hom {E} {V} true

Graph→Quiver : GraphPsh ℓ → Quiver ℓ ℓ
Graph→Quiver Q .fst         = Graph.Vertex Q
Graph→Quiver Q .snd .mor    = Graph.Edge Q
Graph→Quiver Q .snd .dom    = Graph.src Q
Graph→Quiver Q .snd .cod    = Graph.tgt Q

Quiver→Graph : (Q : Quiver ℓ ℓ) → isSet (Q .fst) → isSet (Q .snd .mor)
             → GraphPsh ℓ
Quiver→Graph Q sOb sMor =
  mkGraphPsh (Q .fst , sOb) (Q .snd .mor , sMor) (Q .snd .dom) (Q .snd .cod)

Quiver→Graph→Quiver :
  (Q : Quiver ℓ ℓ) (sOb : isSet (Q .fst)) (sMor : isSet (Q .snd .mor))
  → Graph→Quiver (Quiver→Graph Q sOb sMor) ≡ Q
Quiver→Graph→Quiver Q sOb sMor = refl

Graph→Quiver→Graph :
  (G : GraphPsh ℓ)
  → Quiver→Graph (Graph→Quiver G) (G .F-ob V .snd) (G .F-ob E .snd) ≡ G
Graph→Quiver→Graph {ℓ} G = Functor≡ hOb hHom
  where
    mkG : GraphPsh ℓ
    mkG = Quiver→Graph (Graph→Quiver G) (G .F-ob V .snd) (G .F-ob E .snd)

    hOb : ∀ (c : Ob) → mkG .F-ob c ≡ G .F-ob c
    hOb V = refl
    hOb E = refl

    hHom : ∀ {c c'} (f : (ParallelPair ^op) [ c , c' ])
         → PathP (λ i → (SET ℓ) [ hOb c i , hOb c' i ])
                 (mkG .F-hom f) (G .F-hom f)
    hHom {V} {V} f = sym (cong (G .F-hom {V} {V}) (isPropUnit f tt) ∙ G .F-id)
    hHom {V} {E} f = ⊥.rec f
    hHom {E} {V} false = refl
    hHom {E} {V} true  = refl
    hHom {E} {E} f = sym (cong (G .F-hom {E} {E}) (isPropUnit f tt) ∙ G .F-id)

isFiniteGraph : GraphPsh ℓ → Type ℓ
isFiniteGraph Q = isFinOrd (Graph.Vertex Q) × isFinOrd (Graph.Edge Q)

Disc : ℕ → GraphPsh ℓ-zero
Disc n = mkGraphPsh (Fin n , isSetFin) (⊥ , isProp→isSet isProp⊥) ⊥.rec ⊥.rec

finDisc : (n : ℕ) → isFiniteGraph (Disc n)
finDisc n = (n , FinData≃SumFin) , (0 , idEquiv ⊥)
