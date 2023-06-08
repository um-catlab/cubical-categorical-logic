{-# OPTIONS --safe #-}

module Cubical.Categories.Equivalence.More where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Equivalence.Base



private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level


module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {F : Functor C D} {G : Functor D E}
  where

  open Category
  open Functor
  open NatTrans
  open isEquivalence
  open NatIso
  open isIso

  isEquivalenceComp : isEquivalence F → isEquivalence G → isEquivalence (G ∘F F)
  isEquivalenceComp Feq Geq = record { invFunc = F'∘G' ;
                                       η = η-iso ;
                                       ε = ε-iso } where
    F'∘G' : Functor E C
    F'∘G' = Feq .invFunc ∘F  Geq .invFunc
    η-iso : NatIso 𝟙⟨ C ⟩ (F'∘G' ∘F (G ∘F F))
    η-iso = seqNatIso
      -- proof that 1 and (F' F) are iso
      (Feq .η)
      -- proof that (F' F) and (F' G') (G F) are iso
      (seqNatIso
        -- precompose nested iso with F'
        ((Feq .invFunc) ∘ʳi seqNatIso
          -- proof that F and (G' G) F are isomorphic
          (seqNatIso
            -- proof that F and 1 F are iso
            (symNatIso (CAT⋆IdR {F = F}))
            -- proof that 1 F and (G' G) F are iso (whisker with F)
            (F ∘ˡi (Geq .η)))
          -- associate the parentheses (G' G) F and G' (G F)
          (symNatIso (CAT⋆Assoc F G (Geq .invFunc)))
        )
        -- fix final assoc F' (G' (G F)) iso to (F' G') (G F)
        (CAT⋆Assoc (G ∘F F) (Geq .invFunc) (Feq .invFunc))
      )

    ε-iso : NatIso ((G ∘F F) ∘F F'∘G') 𝟙⟨ E ⟩
    ε-iso = seqNatIso
      -- proof that (G F) (F' G') and G G' are iso
      (seqNatIso
        -- proof that (G F) (F' G') and G (F (F' G')) are iso
        (symNatIso (CAT⋆Assoc (F'∘G') F G))
        -- post compose nested proof with G
        (G ∘ʳi seqNatIso
          -- proof that F (F' G') and 1 G' are iso
          (seqNatIso
            -- proof that F (F' G') and (F F') G' are iso
            (CAT⋆Assoc (Geq .invFunc) (Feq .invFunc) F)
            -- proof that (F F') G' and 1 G' are iso (whisker with G')
            ((Geq .invFunc) ∘ˡi (Feq .ε))
          )
          -- proof that (1 G') and G are iso
          (CAT⋆IdR {F = Geq .invFunc})
        )
      )
      -- proof that G G' and 1 are iso
      (Geq .ε)
