{-# OPTIONS --prop --lossy-unification #-}
module Gluing.Bench.CBPV.Model.Reader where

-- Canonicity for CBPV over the reader theory: the program asks for its
-- configuration and tests divisibility by the configured modulus.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Bool
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod using (_mod_)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (Vertex to Kind; l to 𝒱; r to 𝒞)
open import Cubical.Algebra.Theory.Instances.Reader using (ask; ReaderTheory)
open import Gluing.CBPV.Model.Concrete
open import Cubical.Data.List using (List; []; _∷_)
open import Gluing.Bench.Reference using (Test; test; test!)
open import Gluing.Bench.CBPV.Model.Base

Config = Fin 3

open Syntax (ReaderTheory Config)
open ReaderBoolModelSyntax Config using (ReaderCanonicity)

-- run a closed computation in a configuration
run : Tm _ UnitTy FBoolTy → Config → Bool
run M e = lower (ReaderCanonicity .Iso.inv M e)

-- ask for the configuration as a tag
askTag : ∀ {A : Ob 𝒱} → Tm _ A ([F] (Tag 3 A))
askTag = [op] ask λ e → return (tagFin e)

-- configuration e tests divisibility by modulus e + 1
modulus : Config → ℕ
modulus zero = 2
modulus (suc zero) = 4
modulus (suc (suc zero)) = 6

divisibleByConfigured : ∀ n → Word Bool n → Tm _ UnitTy FBoolTy
divisibleByConfigured n bs = askTag >>= caseFin λ e →
  DFA.runAutomaton (modulus e) (λ _ M → M) n bs

-- reference for divisibleByConfigured
divisible : Config → ∀ n → Word Bool n → Bool
divisible e n bs = valMSB n 0 bs mod suc (modulus e) ≡ᵇ 0

tests : List Test
tests =
  -- one test per configuration, on 48 pseudo-random bits
    test! (run (divisibleByConfigured 48 (patWord 48 0)) zero
           ≡ divisible zero 48 (patWord 48 0))
  ∷ test! (run (divisibleByConfigured 48 (patWord 48 0)) (suc zero)
           ≡ divisible (suc zero) 48 (patWord 48 0))
  ∷ test! (run (divisibleByConfigured 48 (patWord 48 0)) (suc (suc zero))
           ≡ divisible (suc (suc zero)) 48 (patWord 48 0))
  ∷ []
