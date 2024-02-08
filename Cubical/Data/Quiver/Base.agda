-- A Quiver is an endo-span of types.
--   ob <- mor -> ob
-- This is often used in set theory as the data over which a category
-- is defined to be algebraic structure.

-- A Quiver is equivalent to a Graph (modulo universe issues), but
-- they are not definitionally isomorphic: turning a quiver into a
-- graph introduces a Path between objects/nodes in the definition of
-- an Edge.

-- Since avoiding Paths generally leads to cleaner code, Graphs or
-- Quivers may be preferable depending on the variance of a
-- construction.

-- 1. *Using* a Graph generally requires fewer paths between
--    objects. For instance, Graphs are preferable to be used in the
--    definition of a category because composition can be defined by
--    sharing a common middle variable Hom[ A , B ] × Hom[ B , C ] →
--    Hom[ A , C ], which in a Quiver would need a path (e e' : mor) →
--    (cod e ≡ dom e') → mor.
--
-- 2. *Producing* a Quiver generally requires fewer paths between
--    objects. For instance, Quivers are preferable to be used in the
--    definition of generating data for free and presented categories.
--    As an example, the "Funny tensor product" C ⊗ D of categories is
--    defined by generators and relations. The generators are easy to
--    define as a Quiver, but if defined as a graph, then the
--    generators require a path between objects.

-- So as a principle, to get the most general definitions,
-- 1. *Produce* Graphs
-- 2. *Use* Quivers
-- when you can get away with it.

{-# OPTIONS --safe #-}
module Cubical.Data.Quiver.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Graph
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓc ℓc' ℓcᴰ ℓcᴰ' ℓd ℓd' ℓg ℓg' ℓgᴰ ℓgᴰ' ℓh ℓh' ℓj ℓ : Level

-- Useful in certain applications to separate this into components
record QuiverOver (ob : Type ℓg) ℓg' : Type (ℓ-suc (ℓ-max ℓg ℓg')) where
  field
    mor : Type ℓg'
    dom : mor → ob
    cod : mor → ob

open QuiverOver
Quiver : ∀ ℓg ℓg' → Type _
Quiver ℓg ℓg' = Σ[ ob ∈ Type ℓg ] QuiverOver ob ℓg'

-- A "heteromorphism" from a Quiver to a Graph
record HetQG (Q : Quiver ℓc ℓc') (G : Graph ℓg ℓg')
       : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓg ℓg')) where
  field
    _$g_ : Q .fst → G .Node
    _<$g>_ : (e : Q .snd .mor)
           → G .Edge (_$g_ (Q .snd .dom e)) (_$g_ (Q .snd .cod e))
open HetQG public

Graph→Quiver : Graph ℓc ℓc' → Quiver ℓc (ℓ-max ℓc ℓc')
Graph→Quiver g .fst = g .Node
Graph→Quiver g .snd .mor = Σ[ A ∈ g .Node ] Σ[ B ∈ g .Node ] g .Edge A B
Graph→Quiver g .snd .dom x = x .fst
Graph→Quiver g .snd .cod x = x .snd .fst

-- | The use of ≡ in this definition is the raison d'etre for the
-- | Quiver-Graph distinction
Quiver→Graph : Quiver ℓc ℓc' → Graph ℓc (ℓ-max ℓc ℓc')
Quiver→Graph Q .Node = Q .fst
Quiver→Graph Q .Edge A B =
  Σ[ e ∈ Q .snd .mor ]
    (Q .snd .dom e ≡ A)
  × (Q .snd .cod e ≡ B)

Cat→Quiver : Category ℓc ℓc' → Quiver ℓc (ℓ-max ℓc ℓc')
Cat→Quiver 𝓒 = Graph→Quiver (Cat→Graph 𝓒)

module _ (Q : Quiver ℓg ℓg') where
  -- Of the four possible combinations: Q over Q, G over Q, Q over G,
  -- Q over Q, this strikes the right balance. Having the displayed
  -- thing be a Graph means we can define sections without using ≡.
  record Graphᴰ ℓgᴰ ℓgᴰ' : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-suc (ℓ-max ℓgᴰ ℓgᴰ')))
         where
    no-eta-equality
    open QuiverOver (Q .snd)
    field
      ob[_] : Q .fst → Type ℓgᴰ
      Hom[_][_,_]
        : (e : Q .snd .mor)
        → ob[ Q .snd .dom e ]
        → ob[ Q .snd .cod e ]
        → Type ℓgᴰ'

Categoryᴰ→Graphᴰ : {𝓒 : Category ℓc ℓc'}(𝓒ᴰ : Categoryᴰ 𝓒 ℓcᴰ ℓcᴰ')
                 → Graphᴰ (Cat→Quiver 𝓒) ℓcᴰ ℓcᴰ'
Categoryᴰ→Graphᴰ 𝓒ᴰ .Graphᴰ.ob[_] x = 𝓒ᴰ .Categoryᴰ.ob[_] x
Categoryᴰ→Graphᴰ 𝓒ᴰ .Graphᴰ.Hom[_][_,_] (A , B , e) Aᴰ Bᴰ =
  𝓒ᴰ .Categoryᴰ.Hom[_][_,_] e Aᴰ Bᴰ

module _ {Q : Quiver ℓc ℓc'} {G : Graph ℓg ℓg'}
       (ϕ : HetQG Q G) (Gᴰ : Graphᴰ (Graph→Quiver G) ℓgᴰ ℓgᴰ') where
  open HetQG
  open Graphᴰ Gᴰ
  reindex : Graphᴰ Q ℓgᴰ ℓgᴰ'
  reindex .Graphᴰ.ob[_] q = ob[ ϕ $g q ]
  reindex .Graphᴰ.Hom[_][_,_] e A B = Hom[ _ , _ , (ϕ <$g> e) ][ A , B ]

record Section {Q : Quiver ℓg ℓg'} (G : Graphᴰ Q ℓgᴰ ℓgᴰ')
       : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-max ℓgᴰ ℓgᴰ')) where
  open QuiverOver (Q .snd)
  open Graphᴰ G
  field
    F-ob  : ∀ q → ob[ q ]
    F-hom : ∀ e → Hom[ e ][ F-ob (Q .snd .dom e) , F-ob (Q .snd .cod e) ]
