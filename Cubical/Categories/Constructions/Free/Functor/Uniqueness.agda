-- Free functor between categories generated from two graphs
-- -- and a homomorphism between them
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Constructions.Free.Functor.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base hiding (_⟦_⟧)
open import Cubical.Data.Graph.Base

open import Cubical.Data.Graph.Properties
open import Cubical.Data.Empty
open import Cubical.Categories.Constructions.Free.General as
  Free hiding (module Semantics)
open import Cubical.Categories.Constructions.Free.Functor.Base
open import Cubical.Categories.Constructions.Free.UnderlyingGraph

open import Cubical.Tactics.CategorySolver.Reflection

open Category
open Functor
open NatTrans
open NatIso
open isIso

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' : Level

module _ (G : Graph ℓg ℓg') (H : Graph ℓh ℓh') (ϕ : GraphHom G H) where
  -- show that the free functor generated from G , H and ϕ is initial
  -- this is a proof of the universal property of the free functor
  module _ {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'}(𝓕 : Functor 𝓒 𝓓)
           (ıG : GraphHom G (Ugr 𝓒)) (ıH : GraphHom H (Ugr 𝓓))
           (ıϕ : InterpIso G 𝓓 (ıG ⋆Interp 𝓕) (ϕ ⋆GrHom ıH))
           where
    open Semantics G H ϕ 𝓕 ıG ıH ıϕ

    -- Let's say we had an alternative commuting square from Freeϕ to
    -- F that when composed with the universal interpretation agrees
    -- with some fixed interpretation ıϕ. Then in fact that square is
    -- isomorphic to the one generated from ıϕ
    module _ (sem𝓒' : Functor (FreeCat G) 𝓒)
             (sem𝓓' : Functor (FreeH+ϕ G H ϕ) 𝓓)
             (semϕ' : NatIso (𝓕 ∘F sem𝓒') (sem𝓓' ∘F (Freeϕ G H ϕ)))
             (sem𝓒'-agree : InterpIso G 𝓒 (sem𝓒' ∘Interp (η G)) ıG)
             (sem𝓓'-agree : InterpIso H 𝓓 (sem𝓓' ∘Interp (ηH G H ϕ)) ıH)
             (semϕ'-agree : (𝓕 ⊙ʳInterp symInterpIso sem𝓒'-agree )
                            ⋆InterpIso ((semϕ' ⊙ˡInterp (η G))
                            ⋆InterpIso ((sem𝓓' ⊙ʳInterp ηϕ G H ϕ)
                            ⋆InterpIso (sem𝓓'-agree ∘ˡInterp ϕ)))
                            ≡ ıϕ)
             where

      -- first, sem𝓒 and sem𝓒' are isomorphic
      sem𝓒-iso : NatIso sem𝓒' sem𝓒
      sem𝓒-iso = Free.Semantics.semIIso G 𝓒 ıG sem𝓒' sem𝓒'-agree

      -- then, sem𝓓 and sem𝓓' are isomorphic
      private
        -- essentially, we have an iso that is natural on generators
        -- and we need to prove its natural on all terms
        α-mor = sem𝓓'-agree .fst .fst
        α-nat-generators = sem𝓓'-agree .fst .snd

        α-nat-id : ∀ {v} → sem𝓓' ⟪ idf ⟫ ⋆⟨ 𝓓 ⟩
                   α-mor v ≡ α-mor v ⋆⟨ 𝓓 ⟩ 𝓓 .id
        α-nat-id = (λ i → sem𝓓' .F-id i ⋆⟨ 𝓓 ⟩ α-mor _) ∙
                   sym (idTrans (Id {C = 𝓓}) .N-hom _)

        α-nat-seq : ∀ {u v w} → (e : FreeH+ϕ G H ϕ [ u , v ])
                    (e' : FreeH+ϕ G H ϕ [ v , w ])
                  → sem𝓓' ⟪ e ⟫ ⋆⟨ 𝓓 ⟩ α-mor _ ≡ α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ e ⟫
                  → sem𝓓' ⟪ e' ⟫ ⋆⟨ 𝓓 ⟩ α-mor _ ≡ α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ e' ⟫
                  → sem𝓓' ⟪ e ⋆f e' ⟫ ⋆⟨ 𝓓 ⟩ α-mor w ≡ α-mor _ ⋆⟨ 𝓓 ⟩
                          (sem𝓓 ⟪ e ⟫ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ e' ⟫)
        α-nat-seq e e' e-ih e'-ih =
          (λ i → sem𝓓' .F-seq e e' i ⋆⟨ 𝓓 ⟩ α-mor _)
          ∙ 𝓓 .⋆Assoc _ _ _
          ∙ cong (seq' 𝓓 (sem𝓓' ⟪ e ⟫)) e'-ih
          ∙ sym (𝓓 .⋆Assoc _ _ _)
          ∙ cong (comp' 𝓓 (sem𝓓 ⟪ e' ⟫)) e-ih
          ∙ 𝓓 .⋆Assoc _ _ _

        F⟪⟫-Functor : Functor (FreeCat G) (FreeH+ϕ G H ϕ)
        F⟪⟫-Functor .F-ob = ϕ ._$g_
        F⟪⟫-Functor .F-hom = F⟪_⟫
        F⟪⟫-Functor .F-id = F-idₑ
        F⟪⟫-Functor .F-seq = F-seqₑ

        F⟪⟫-Freeϕ-agree : NatIso F⟪⟫-Functor (Freeϕ G H ϕ)
        F⟪⟫-Freeϕ-agree =
          Free.Semantics.semIIso G ((FreeH+ϕ G H ϕ))
          (Freeϕ-homo G H ϕ) F⟪⟫-Functor (idInterpIso _ _)

        natural-on-Freeϕ : NatIso (sem𝓓' ∘F Freeϕ G H ϕ) (sem𝓓 ∘F Freeϕ G H ϕ)
        natural-on-Freeϕ =
          uniqueness-principle G (sem𝓓' ∘F Freeϕ G H ϕ) (sem𝓓 ∘F Freeϕ G H ϕ)
          ((sem𝓓' ⊙ʳInterp ηϕ G H ϕ)
          ⋆InterpIso ((sem𝓓'-agree ∘ˡInterp ϕ) ⋆InterpIso
            symInterpIso (sem𝓓 ⊙ʳInterp ηϕ G H ϕ)))

        α-mor≡NatTransFreeϕ : ∀ {v} →
          (natural-on-Freeϕ ⊙ˡInterp (η G)) .fst .fst v ≡ α-mor (ϕ $g v)
        α-mor≡NatTransFreeϕ =
           (natural-on-Freeϕ ⊙ˡInterp (η G)) .fst .fst _
             ≡[ i ]⟨ uniqueness-principle-restricts G ((sem𝓓' ∘F Freeϕ G H ϕ))
                     ((sem𝓓 ∘F Freeϕ G H ϕ))
                     (((sem𝓓' ⊙ʳInterp ηϕ G H ϕ) ⋆InterpIso
                       ((sem𝓓'-agree ∘ˡInterp ϕ) ⋆InterpIso symInterpIso
                         (sem𝓓 ⊙ʳInterp ηϕ G H ϕ)))) i .fst .fst _ ⟩
           (sem𝓓' ⟪ FreeH+ϕ G H ϕ .id ⟫ ⋆⟨ 𝓓 ⟩
             (α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ FreeH+ϕ G H ϕ .id ⟫))
             ≡[ i ]⟨ sem𝓓' .F-id i ⋆⟨ 𝓓 ⟩ (α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 .F-id i) ⟩
           (𝓓 .id ⋆⟨ 𝓓 ⟩ (α-mor _ ⋆⟨ 𝓓 ⟩ 𝓓 .id))
             ≡⟨ solveCat! 𝓓 ⟩
           α-mor _ ∎

        α-nat-F' : ∀ {u v} → (e : FreeCat G [ u , v ])
                 → sem𝓓' ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩ α-mor _ ≡
                   α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫
        α-nat-F' e =
          transport
            (λ i → sem𝓓' ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩
              α-mor≡NatTransFreeϕ i ≡ α-mor≡NatTransFreeϕ i ⋆⟨ 𝓓 ⟩
                sem𝓓 ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫) (natural-on-Freeϕ .trans .N-hom e)

        -- Argument: α should be natural on everything
        -- of the form F ⟪ e ⟫ because ?
        α-nat-F : ∀ {u v} → (e : FreeCat G [ u , v ])
                → sem𝓓' ⟪ F⟪ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩ α-mor _ ≡
                  α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ F⟪ e ⟫ ⟫
        α-nat-F e =
          sem𝓓' ⟪ F⟪ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩ α-mor _
            ≡[ i ]⟨ sem𝓓' ⟪ F⟪⟫-Freeϕ-agree⟪⟫ i ⟫ ⋆⟨ 𝓓 ⟩ α-mor _ ⟩
          sem𝓓' ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫ ⋆⟨ 𝓓 ⟩ α-mor _
            ≡⟨ α-nat-F' e ⟩
          α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ Freeϕ G H ϕ ⟪ e ⟫ ⟫
            ≡[ i ]⟨ α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ F⟪⟫-Freeϕ-agree⟪⟫ (~ i) ⟫ ⟩
          α-mor _ ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ F⟪ e ⟫ ⟫ ∎
          where
            F⟪⟫-Freeϕ-agree⟪⟫ : F⟪ e ⟫ ≡ Freeϕ G H ϕ ⟪ e ⟫
            F⟪⟫-Freeϕ-agree⟪⟫ =
              sym (FreeH+ϕ G H ϕ .⋆IdR F⟪ e ⟫) ∙
                F⟪⟫-Freeϕ-agree .trans .N-hom _ ∙ FreeH+ϕ G H ϕ .⋆IdL _

        α-nat : ∀ {A B} (e : FreeH+ϕ G H ϕ [ A , B ])
                           → sem𝓓' ⟪ e ⟫ ⋆⟨ 𝓓 ⟩ α-mor B
                             ≡ α-mor A ⋆⟨ 𝓓 ⟩ sem𝓓 ⟪ e ⟫
        -- the actual cases
        α-nat (↑f x) = α-nat-generators x
        α-nat idf = α-nat-id
        α-nat (e ⋆f e') = α-nat-seq e e' (α-nat e) (α-nat e')
        α-nat F⟪ x ⟫ = α-nat-F x -- α-nat-F x
        -- 1-paths
        α-nat (⋆fIdL e i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom)
          (α-nat-seq idf e α-nat-id (α-nat e))
          (α-nat e) (λ i → seq' 𝓓 (sem𝓓' ⟪ ⋆fIdL e i ⟫) (α-mor _))
          (λ i → seq' 𝓓 (α-mor _) (sem𝓓 ⟪ ⋆fIdL e i ⟫)) i j

        α-nat (⋆fIdR e i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom)
            (α-nat-seq e idf (α-nat e) α-nat-id) (α-nat e)
            (λ i → seq' 𝓓 (sem𝓓' ⟪ ⋆fIdR e i ⟫) (α-mor _))
            (λ i → seq' 𝓓 (α-mor _) (sem𝓓 ⟪ ⋆fIdR e i ⟫)) i j

        α-nat (⋆fAssoc e e' e'' i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom)
            (α-nat-seq (e ⋆f e') e'' (α-nat-seq e e' (α-nat e)
              (α-nat e')) (α-nat e''))
            (α-nat-seq e (e' ⋆f e'') (α-nat e)
              (α-nat-seq e' e'' (α-nat e') (α-nat e'')))
            (λ i → seq' 𝓓 (sem𝓓' ⟪ ⋆fAssoc e e' e'' i ⟫) (α-mor _))
            (λ i → seq' 𝓓 (α-mor _) (sem𝓓 ⟪ ⋆fAssoc e e' e'' i ⟫)) i j
        α-nat (F-idₑ i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom) (α-nat-F idₑ) (α-nat-id)
            (λ i → seq' 𝓓 (sem𝓓' ⟪ F-idₑ i ⟫) (α-mor (ϕ $g _)))
            (λ i → seq' 𝓓 (α-mor (ϕ $g _)) (sem𝓓 ⟪ F-idₑ i ⟫)) i j
        α-nat (F-seqₑ e e' i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom) (α-nat-F (e ⋆ₑ e'))
            (α-nat-seq F⟪ e ⟫ F⟪ e' ⟫ (α-nat-F e) (α-nat-F e'))
            (λ i → seq' 𝓓 (sem𝓓' ⟪ F-seqₑ e e' i ⟫) (α-mor (ϕ $g _)))
            (λ i → seq' 𝓓 (α-mor (ϕ $g _)) (sem𝓓 ⟪ F-seqₑ e e' i ⟫)) i j

        α-nat (F⟪⟫-ϕ-agree e i) j =
          isSet→SquareP (λ _ _ → 𝓓 .isSetHom) (α-nat-F (↑ e))
            (α-nat-generators (ϕ <$g> e))
            (λ i → seq' 𝓓 (sem𝓓' ⟪ F⟪⟫-ϕ-agree e i ⟫) (α-mor (ϕ $g _)))
            (λ i → seq' 𝓓 (α-mor (ϕ $g _)) (sem𝓓 ⟪ F⟪⟫-ϕ-agree e i ⟫)) i j
        -- the 2-path
        α-nat (isSetFExp e e' p q i j) =
          isSet→SquareP (λ i j → isSet→isGroupoid (𝓓 .isSetHom)
            (seq' 𝓓 (sem𝓓' ⟪ isSetFExp e e' p q i j ⟫) (α-mor _))
            (seq' 𝓓 (α-mor _) (sem𝓓 ⟪ isSetFExp e e' p q i j ⟫)))
            (λ j → α-nat (p j)) (λ j → α-nat (q j)) (λ _ → α-nat e)
              (λ _ → α-nat e') i j

        sem𝓓-trans : NatTrans sem𝓓' sem𝓓
        sem𝓓-trans .N-ob = α-mor
        sem𝓓-trans .N-hom f = α-nat f
      sem𝓓-iso : NatIso sem𝓓' sem𝓓
      sem𝓓-iso .trans = sem𝓓-trans
      sem𝓓-iso .nIso x = sem𝓓'-agree .snd x
