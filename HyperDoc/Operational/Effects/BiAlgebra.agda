{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Effects.BiAlgebra where 
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.FinData
open import Cubical.Data.Sigma 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base 
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Instances.Sets

open import HyperDoc.Algebra.Algebra hiding (FORGET ; FREE )
open import HyperDoc.Operational.Graph hiding (FORGET ; FREE ; FORGETᴰ)

open Alg
open AlgHom
open Category
open Signature

record BiAlg (Sig : Signature): Type where 
  field 
    car : hSet _ 
    isAlg : IsAlg Sig car
    -- a reflexive graph on the carrier of alg
    -- view this as a coalgebra for the covariant powerset functor
    -- edges in hProp
    isRGraph : ReflBinRel car

  alg : Alg Sig 
  alg = record { Carrier = car ; interp = isAlg }

  -- TODO observe the bisimulation principle given by Relator R -> PR
  coalg : ⟨ car ⟩ → ℙ ⟨ car ⟩ 
  coalg x x' = isRGraph .fst x x'

  graph : Graph _ _ 
  graph = car , λ n n' → isRGraph .fst n n' .fst , isProp→isSet (isRGraph .fst n n' .snd)

  rgraph : RGraph _ _ 
  rgraph = graph , isRGraph .snd

  Node : Type 
  Node = ⟨ car ⟩ 

  Edge[_,_] : Node → Node → Type 
  Edge[_,_] n n' = ⟨ graph .snd n n' ⟩

  isPropEdge : {n n' : Node} → isProp Edge[ n , n' ] 
  isPropEdge {n}{n'} = isRGraph .fst n n' .snd

  field 
    congruence : 
      (op : Sig .Op)(args args' : Fin (Sig .arity op) → Node) → 
      ((i : Fin (Sig .arity op)) → Edge[ args i , args' i ]) → 
      -------------------------------------
      Edge[ interp alg op args , interp alg op args' ]
open BiAlg

record BiAlgHom {Sig : Signature}(B B' : BiAlg Sig) : Type where 
  private 
    module B = BiAlg B 
    module B' = BiAlg B'
  field 
    map : ⟨ B.car ⟩ → ⟨ B'.car ⟩
    isAlgHom : IsAlgHom {Sig} {alg B}{alg B'} map
    isRelator : IsRelator {rgraph B}{rgraph B'} map

  algHom : AlgHom (alg B) (alg B') 
  algHom = record { carmap = map ; pres = isAlgHom }

  relator : Relator (rgraph B) (rgraph B') 
  relator = map , isRelator


open BiAlgHom
open AlgHom

isProp→isPropPath :
  {X : Type} →
  isProp X →
  (x y : X) →
  isProp (x ≡ y)
isProp→isPropPath propX x y = isContr→isProp (isProp→isContrPath propX x y)

BiAlgRelator≡ : {Sig : Signature}{B B' : BiAlg Sig}{f g : BiAlgHom B B'} → 
  (p : f .map ≡ g .map) → 
  PathP (λ i → IsRelator {rgraph B}{rgraph B'} (p i)) (isRelator f) (isRelator g) 
BiAlgRelator≡ {Sig}{B}{B'}{f}{g} prf  = 
  isProp→PathP 
    (λ i → isPropΣ 
      (isPropImplicitΠ2 (λ n n' → isProp→ (isPropEdge B'))) 
      λ x → isPropImplicitΠ λ y → isProp→isPropPath (isPropEdge B') _ _)
    (isRelator f) 
    (isRelator g)

BiAlgHom≡ : {Sig : Signature}{B B' : BiAlg Sig}{f g : BiAlgHom B B'} → 
  (p : f .map ≡ g .map) → f ≡ g
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .map = prf i
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .isAlgHom = 
  AlgHom≡ {Sig} {alg B}{alg B'} {algHom f}{algHom g} prf i .pres
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .isRelator = 
  BiAlgRelator≡ {Sig}{B}{B'}{f}{g} prf i

unquoteDecl BiAlgHomIsoΣ = declareRecordIsoΣ BiAlgHomIsoΣ (quote BiAlgHom)

idBHom : {Sig : Signature}{B : BiAlg Sig} → BiAlgHom B B 
idBHom {Sig} {B} .map x = x
idBHom {Sig} {B} .isAlgHom op args = refl
idBHom {Sig} {B} .isRelator .fst e = e
idBHom {Sig} {B} .isRelator .snd = refl

seqBHom : {Sig : Signature}{B B' B'' : BiAlg Sig} → 
  BiAlgHom B B' → BiAlgHom B' B'' → BiAlgHom B B'' 
seqBHom f g .map x = g .map (f .map x)
seqBHom f g .isAlgHom = ( algHom f ⋆AlgHom algHom g ) .pres
seqBHom {Sig}{B}{B'}{B''} f g .isRelator = 
  seqRelator {G = rgraph B}{rgraph B'}{rgraph B''} (relator f) (relator g) .snd 

BIALG : Signature → Category _ _ 
BIALG Sig .ob = BiAlg Sig
BIALG Sig .Hom[_,_] = BiAlgHom
BIALG Sig .id = idBHom
BIALG Sig ._⋆_ = seqBHom
BIALG Sig .⋆IdL _ = BiAlgHom≡ refl
BIALG Sig .⋆IdR _ = BiAlgHom≡ refl
BIALG Sig .⋆Assoc _ _ _ = BiAlgHom≡ refl
BIALG Sig .isSetHom = {!   !}

FORGET : {Sig : Signature} → Functor (BIALG Sig) (SET _) 
FORGET .Functor.F-ob B = car B
FORGET .Functor.F-hom = λ z → z .map
FORGET .Functor.F-id = refl
FORGET .Functor.F-seq _ _ = refl 

open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation renaming (map to hmap)

FreeBiAlg : {Sig : Signature} → hSet _ → BiAlg Sig 
FreeBiAlg {Sig} X .car = FreeOn Sig ⟨ X ⟩ , {!   !}
FreeBiAlg X .isAlg = ops
FreeBiAlg X .isRGraph .fst = _≡ₚ_
FreeBiAlg X .isRGraph .snd n = ∣ refl ∣₁
FreeBiAlg X .congruence op args args' args≡ = recFin squash₁ (λ eqs → ∣ (cong₂ ops refl (funExt eqs)) ∣₁) args≡

FreeBiAlgHom : {Sig : Signature}{X Y : hSet _} → (⟨ X ⟩ → ⟨ Y ⟩ ) →  BIALG Sig [ FreeBiAlg X , FreeBiAlg Y ] 
FreeBiAlgHom {Sig}{X}{Y} f .map = FreeAlgMorphism {Sig}{⟨ X ⟩}{FreeAlg Sig ⟨ Y ⟩ } (λ z → inc (f z)) .carmap
FreeBiAlgHom {Sig}{X}{Y} f .isAlgHom = FreeAlgMorphism {Sig}{⟨ X ⟩}{FreeAlg Sig ⟨ Y ⟩ } (λ z → inc (f z)) .pres
FreeBiAlgHom f .isRelator .fst = hmap (cong₂ FreeAlgMorphism' refl)
FreeBiAlgHom f .isRelator .snd = refl

FREE : {Sig : Signature} → Functor (SET _) (BIALG Sig) 
FREE {Sig} .Functor.F-ob = FreeBiAlg
FREE {Sig} .Functor.F-hom {X}{Y} = FreeBiAlgHom {Sig}{X}{Y}
FREE {Sig} .Functor.F-id = {!   !} -- FreeAlgMorphism! 
FREE {Sig} .Functor.F-seq = {!   !}


open Categoryᴰ
open Algᴰ

record BiAlgᴰ {Sig : Signature}(B : BiAlg Sig): Type where 
  module B = BiAlg B
  field 
    carᴰ : ⟨ B.car ⟩ → hSet _
    isAlgᴰ : IsAlgᴰ {Sig} {alg B} carᴰ
    isRGraphᴰ : ReflBinRelᴰ {B.car} carᴰ B.isRGraph

  algᴰ : Algᴰ B.alg 
  algᴰ = record { Carrierᴰ = carᴰ ; interpᴰ = isAlgᴰ }

  graphᴰ : Graphᴰ _ _ B.graph
  graphᴰ = carᴰ , λ {n}{n'} e nᴰ n'ᴰ → 
    (isRGraphᴰ .fst {n}{n'} e nᴰ n'ᴰ .fst) , 
    isProp→isSet (isRGraphᴰ .fst {n}{n'} e nᴰ n'ᴰ .snd)
    
  rgraphᴰ : RGraphᴰ B.rgraph
  rgraphᴰ = graphᴰ , isRGraphᴰ .snd

  Nodeᴰ : B.Node → Type 
  Nodeᴰ n = ⟨ carᴰ n ⟩

  Edgeᴰ[_][_,_] : {n n' : B.Node}(e : B.Edge[ n , n' ]) → Nodeᴰ n → Nodeᴰ n' → Type 
  Edgeᴰ[_][_,_] {n}{n'} e nᴰ n'ᴰ = ⟨ graphᴰ .snd {n}{n'} e nᴰ n'ᴰ ⟩

  isPropEdgeᴰ : {n n' : B.Node}{e : B.Edge[ n , n' ]}{nᴰ : Nodeᴰ n}{n'ᴰ : Nodeᴰ n'} → 
     isProp Edgeᴰ[ e ][ nᴰ , n'ᴰ ] 
  isPropEdgeᴰ {n}{n'}{e}{nᴰ}{n'ᴰ} = isRGraphᴰ .fst {n}{n'} e nᴰ n'ᴰ .snd

  field 
    congruenceᴰ : 
      (op : Sig .Op)
      (args args' : Fin (Sig .arity op) → B.Node) 
      (edges : (i : Fin (Sig .arity op)) → B.Edge[ args i , args' i ] )
      (dargs : ((i : Fin (Sig .arity op)) → Nodeᴰ (args i))) 
      (dargs' : ((i : Fin (Sig .arity op)) → Nodeᴰ (args' i)))
      (edgesᴰ : (i : Fin (Sig .arity op)) → Edgeᴰ[ edges i ][ dargs i , dargs' i ] ) → 
      Edgeᴰ[ B.congruence op args args' edges ][ interpᴰ algᴰ  op args dargs , interpᴰ algᴰ  op args' dargs' ]


record BiAlgHomᴰ 
  {Sig : Signature}
  {B B' : BiAlg Sig}
  (f : BiAlgHom B B')
  (Bᴰ : BiAlgᴰ B)
  (B'ᴰ : BiAlgᴰ B') : Type where 
  private 
    module B = BiAlg B 
    module B' = BiAlg B'
    module Bᴰ = BiAlgᴰ Bᴰ
    module B'ᴰ = BiAlgᴰ B'ᴰ
  field 
    mapᴰ : (b : B.Node) → Bᴰ.Nodeᴰ b → B'ᴰ.Nodeᴰ (map f b)
    isAlgHomᴰ : IsAlgHomᴰ {Sig}{B.alg}{B'.alg}{algHom f}{Bᴰ.algᴰ}{B'ᴰ.algᴰ} mapᴰ
    isRelatorᴰ : IsRelatorᴰ {B.rgraph}{B'.rgraph}{Bᴰ.rgraphᴰ}{B'ᴰ.rgraphᴰ} (map f) (f .isRelator) mapᴰ

  algHomᴰ : AlgHomᴰ (algHom f) Bᴰ.algᴰ B'ᴰ.algᴰ 
  algHomᴰ = record { carmapᴰ = mapᴰ ; presᴰ = isAlgHomᴰ }

  relatorᴰ : Relatorᴰ {G = B.rgraph}{B'.rgraph}(relator f) Bᴰ.rgraphᴰ B'ᴰ.rgraphᴰ 
  relatorᴰ = mapᴰ , isRelatorᴰ

open BiAlgHomᴰ 
idBHomᴰ : {Sig : Signature}{B : BiAlg Sig}{Bᴰ : BiAlgᴰ B} → 
  BiAlgHomᴰ (BIALG Sig .id) Bᴰ Bᴰ
idBHomᴰ .BiAlgHomᴰ.mapᴰ b bᴰ = bᴰ
idBHomᴰ .BiAlgHomᴰ.isAlgHomᴰ op args dargs = refl
idBHomᴰ .BiAlgHomᴰ.isRelatorᴰ .fst = λ nᴰ n'ᴰ z → z
idBHomᴰ .BiAlgHomᴰ.isRelatorᴰ .snd = refl

seqBHomᴰ : {Sig : Signature}{B B' B'' : BiAlg Sig}
      {f : BiAlgHom B B'}
      {g : BiAlgHom B' B''}
      {Bᴰ : BiAlgᴰ B}
      {B'ᴰ : BiAlgᴰ  B'}
      {B''ᴰ : BiAlgᴰ B''} → 
      BiAlgHomᴰ f Bᴰ B'ᴰ →
      BiAlgHomᴰ g B'ᴰ B''ᴰ →
      BiAlgHomᴰ ((BIALG Sig ⋆ f) g) Bᴰ B''ᴰ
seqBHomᴰ {Sig} {B} {B'} {B''} {f} {g} {Bᴰ} {B'ᴰ} {B''ᴰ} fᴰ gᴰ .BiAlgHomᴰ.mapᴰ b bᴰ = 
  gᴰ .mapᴰ (f .map b) (fᴰ .mapᴰ b bᴰ)
seqBHomᴰ {Sig} {B} {B'} {B''} {f} {g} {Bᴰ} {B'ᴰ} {B''ᴰ} fᴰ gᴰ .BiAlgHomᴰ.isAlgHomᴰ = {!   !}
seqBHomᴰ {Sig} {B} {B'} {B''} {f} {g} {Bᴰ} {B'ᴰ} {B''ᴰ} fᴰ gᴰ .BiAlgHomᴰ.isRelatorᴰ = {!   !}

BIALGᴰ : {Sig : Signature} → Categoryᴰ (BIALG Sig) _ _ 
ob[ BIALGᴰ {Sig} ] = BiAlgᴰ
BIALGᴰ {Sig} .Hom[_][_,_] = BiAlgHomᴰ
BIALGᴰ {Sig} .idᴰ {B}{Bᴰ} = idBHomᴰ {Sig}{B}{Bᴰ}
BIALGᴰ {Sig} ._⋆ᴰ_ {B}{B'}{B''}{f}{g}{Bᴰ}{B'ᴰ}{B''ᴰ}= 
  seqBHomᴰ{Sig}{B}{B'}{B''}{f}{g}{Bᴰ}{B'ᴰ}{B''ᴰ}
BIALGᴰ {Sig} .⋆IdLᴰ = {!   !}
BIALGᴰ {Sig} .⋆IdRᴰ = {!   !}
BIALGᴰ {Sig} .⋆Assocᴰ = {!   !}
BIALGᴰ {Sig} .isSetHomᴰ = {!   !}

FORGETᴰ : {Sig : Signature}→  Functorᴰ FORGET (BIALGᴰ {Sig}) (SETᴰ ℓ-zero ℓ-zero)
FORGETᴰ .Functorᴰ.F-obᴰ = λ z → BiAlgᴰ.carᴰ z
FORGETᴰ .Functorᴰ.F-homᴰ = λ z → z .BiAlgHomᴰ.mapᴰ
FORGETᴰ .Functorᴰ.F-idᴰ = refl
FORGETᴰ .Functorᴰ.F-seqᴰ _ _ = refl
{-
BiAlgRelator≡ : {Sig : Signature}{B B' : BiAlg Sig}{f g : BiAlgHom B B'} → 
  (p : f .map ≡ g .map) → 
  PathP (λ i → IsRelator {rgraph B}{rgraph B'} (p i)) (isRelator f) (isRelator g) 
BiAlgRelator≡ {Sig}{B}{B'}{f}{g} prf  = 
  isProp→PathP 
    (λ i → isPropΣ 
      (isPropImplicitΠ2 (λ n n' → isProp→ (isPropEdge B'))) 
      λ x → isPropImplicitΠ λ y → isProp→isPropPath (isPropEdge B') _ _)
    (isRelator f) 
    (isRelator g)

BiAlgHom≡ : {Sig : Signature}{B B' : BiAlg Sig}{f g : BiAlgHom B B'} → 
  (p : f .map ≡ g .map) → f ≡ g
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .map = prf i
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .isAlgHom = 
  AlgHom≡ {Sig} {alg B}{alg B'} {algHom f}{algHom g} prf i .pres
BiAlgHom≡ {Sig} {B} {B'} {f} {g} prf i .isRelator = 
  BiAlgRelator≡ {Sig}{B}{B'}{f}{g} prf i
-}