{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.shanuel where
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Displayed.Constructions.FullSubcategory

    -- hacking things out.. 
    module _ ℓ where

        -- The Shanuel topos is equivalet to the full subcategory of [Inj, Set] given by pullback preserving functors.
        -- pg 105 Nominal Sets - Pitts

        -- define Inj
        -- find definition of functor category
        -- define full subcategory of functor category
        --   the predictate used will have to be pullback preserving functors
        --   so figure out what those are and how to formalize that


        -- Define Inj
        -- Can/should I define this from a displayed category?
        -- Just do it manually for now
        open Category
        open import Cubical.Foundations.HLevels
        open import Cubical.Functions.Embedding
        open import Cubical.Foundations.Equiv
        open import Cubical.Foundations.Equiv.Properties
        open import Cubical.Data.Sigma

        
        Inj : Category (ℓ-suc ℓ) ℓ 
        ob Inj = FinSet ℓ
        Hom[_,_] Inj (A , _) (B , _) = A ↪ B
        id Inj {x} = id↪ (fst x)
        _⋆_ Inj f g = compEmbedding g f
        ⋆IdL Inj (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆IdR Inj (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆Assoc Inj f g h = Σ≡Prop (λ x → isPropIsEmbedding) refl
        -- FinSet is defined using Type with structure and not an hset... 
        -- how do we know the fst components (x : Type) in FinSet are actually "Set"..?
        isSetHom Inj {x} {y} = isSetΣ 
                                (isSetΠ λ _ → {! fst x  !}) 
                                (λ t → isProp→isOfHLevelSuc 1 isPropIsEmbedding)

        open import Cubical.Categories.Instances.Functors
        open import Cubical.Categories.Functor

        [Inj,SET] : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
        [Inj,SET] = FUNCTOR Inj (SET ℓ)

        open import Cubical.Categories.Limits
        open import Cubical.Categories.Displayed.Base

        -- preserves limits is overkill
        -- just needs to preserve pullbacks
        -- which I may need to define myself..
        Sch : Categoryᴰ [Inj,SET] (ℓ-suc ℓ) ℓ-zero
        Sch = FullSubcategoryᴰ [Inj,SET] (preservesLimits {ℓ} {ℓ})

        open import Cubical.Categories.Limits.Pullback
        -- preservesPullbacks : ?
       --preservesPullbacks 

        {-
        preservesTerminals : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                   → Functor C D
                   → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preservesTerminals C D F = ∀ (term : Terminal C) → isTerminal D (F ⟅ term .fst ⟆) 
        -}
    

        -- FinSet 
        -- objects finite sets
        -- morphisms functions
        -- https://ncatlab.org/nlab/show/FinSet
        -- it is a Full Subcategory of SET
        -- Full Subcatetory
        --      some objects
        --      all morphisms (for those objects)
        -- use embedding instead of injection? 
        -- https://github.com/agda/cubical/blob/598dfa5c85492f503d04164e79dc4bb0e1e54a24/Cubical/Functions/Embedding.agda#L37
        Fin : Category {! SET !} {! isFinSet  !} 
        Fin = {! FullSubcategoryᴰ   !} --isFinSet