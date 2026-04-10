{-# OPTIONS --lossy-unification #-}
-- Double category of categories, functors, and profunctors
--
-- In this file, we opt for a strict notion of functor,
-- see Cubical.Categories.Functors.Strict.Base for an
-- alternative definition of functors that is definitionally
-- unital and associative, to give better definitional equalities
--
-- Correspondingly, we also use variants of presheaves, bifunctors,
-- and PshHom that are related to this notion of StrictFunctor
--
-- I'm not sure how much is genuinely necessary. Certainly the
-- usage of StrictFunctor is crucial in allowing usage of
-- makeSPshHomPath in several places, as in the non-strict variant we would
-- be forced to use a genuine PathP
module Cubical.Categories.Double.Instances.Prof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Functors.Strict.Presheaf
open import Cubical.Categories.Functors.Strict.Bifunctor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.BinProduct as BP
open import Cubical.Categories.Presheaf.Constructions.Tensor as ⊗
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom as Strict
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.StrictHom as Strict
open import Cubical.Categories.Profunctor.StrictHom.Constructions.Extension

open import Cubical.Categories.Double.Base

open DoubleCategory
open PshHomStrict
open PshIsoStrict
open StrictFunctor
open Bifunctor
open BifunctorSepAx

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

-- Whisker a RelatorHomStrict by a pair of StrictFunctors.
module _ {ℓP ℓQ}
  {C : Category ℓc ℓc'}
  {D : Category ℓd ℓd'}
  {P : StrictPresheaf D ℓP}{Q : StrictPresheaf D ℓQ}
  where
  -- This probably belongs elsewhere
  _∘ˡS_ : SPshHom P Q
        → (F : StrictFunctor C D)
        → SPshHom (P S∘ (F ^opS)) (Q S∘ (F ^opS))
  (α ∘ˡS F) .SPshHom.N-ob = λ c → α .SPshHom.N-ob ((F ^opS) .F-ob c)
  (α ∘ˡS F) .SPshHom.N-hom = λ c c' f →
                                α .SPshHom.N-hom ((F ^opS) .F-ob c) ((F ^opS) .F-ob c')
                                ((F ^opS) .F-hom f)

module _ {ℓ}
  {C₁ C₂ C₃ C₄ : Category ℓ ℓ}
  (f : StrictRelatoro* C₁ ℓ C₂)
  (g : StrictRelatoro* C₂ ℓ C₃)
  (h : StrictRelatoro* C₃ ℓ C₄)
  where
  private
    fg = scompLRS ⊗-BifS (StrictCurryBifunctor f)
                         (StrictCurryBifunctor (StrictSym g))
    gh = scompLRS ⊗-BifS (StrictCurryBifunctor g)
                         (StrictCurryBifunctor (StrictSym h))
  module _ (c : Category.ob C₁) (d : Category.ob C₄) where
    αᴴ-Nob :
      (appL (StrictBif→Bif fg) c) ⊗ (appL (StrictBif→Bif (StrictSym h)) d) →
      (appL (StrictBif→Bif f) c) ⊗ (appL (StrictBif→Bif (StrictSym gh)) d)
    αᴴ-Nob = rec _ _ isSet⊗ (rec _ _ (isSet→ isSet⊗)
        (λ {x = x₂} p q q₁ → p Tensor.,⊗ (q Tensor.,⊗ q₁))
        (λ p f q → funExt λ _ → Tensor.swap p f (q Tensor.,⊗ _)))
        (ind _ _ (λ _ → isPropΠ2 λ _ _ → isSet⊗ _ _)
        (λ p q g q' → congS (p Tensor.,⊗_) (Tensor.swap _ _ _)))

    αᴴ⁻-Nob :
      (appL (StrictBif→Bif f) c) ⊗ (appL (StrictBif→Bif (StrictSym gh)) d) →
      (appL (StrictBif→Bif fg) c) ⊗ (appL (StrictBif→Bif (StrictSym h)) d)
    αᴴ⁻-Nob = rec _ _ isSet⊗
        (λ p → rec _ _ isSet⊗
          (λ q r → (p Tensor.,⊗ q) Tensor.,⊗ r)
          (λ q n r → Tensor.swap (p Tensor.,⊗ q) n r))
        (λ p n → ind _ _ (λ _ → isSet⊗ _ _)
          (λ q r → congS (Tensor._,⊗ r) (Tensor.swap p n q)))

module _ (ℓ ℓ' : Level) where
  PROF : DoubleCategory _ _ _ _
  PROF .ob = Category ℓ ℓ
  PROF .Homⱽ[_,_] = StrictFunctor
  PROF .idⱽ = SId
  PROF ._⋆ⱽ_ F G = G S∘ F
  PROF .⋆ⱽIdL F = refl
  PROF .⋆ⱽIdR F = refl
  PROF .⋆ⱽAssoc F G H = refl
  PROF .Homᴴ[_,_] C D = StrictRelatoro* C ℓ D
  PROF .idᴴ {x = C} = StrictHomBif C
  PROF ._⋆ᴴ_ S R =
    scompLRS ⊗-BifS (StrictCurryBifunctor S)
                    (StrictCurryBifunctor (StrictSym R))
  PROF .Sq S R F G =
    SPshHom (StrictRelator→Psh S)
            (StrictRelator→Psh (scompLRS R (F ^opS) G))
  PROF .isSetSq {fᴴ = f}{gᴴ = g}{fⱽ = v}{gⱽ = u} =
    isSetSPshHom (StrictRelator→Psh f)
                 (StrictRelator→Psh (scompLRS g (v ^opS) u))
  PROF .idⱽSq = spshhom (λ c z → z) (λ c c' f p' p z → z)
  PROF .idᴴSq {v = F} .SPshHom.N-ob (c , c') f = F .F-hom f
  PROF .idᴴSq {y = D}{v = F} .SPshHom.N-hom (c , c') (c1 , c1') (f₁ , f₃) p' p eq =
    cong (D._⋆ F .F-hom f₃) (sym (F .F-seq f₁ p' _ refl))
    ∙ sym (F .F-seq _ f₃ p eq)
    where module D = Category D
  PROF ._⋆ⱽSq_ {←f = v}{→f = u} α β =
    spshhom
     (λ c z →
        β .SPshHom.N-ob (v .F-ob (c .fst) , u .F-ob (c .snd))
        (α .SPshHom.N-ob c z))
     (λ c c' f p' p z →
        β .SPshHom.N-hom (v .F-ob (c .fst) , u .F-ob (c .snd))
        (v .F-ob (c' .fst) , u .F-ob (c' .snd))
        (v .F-hom (f .fst) , u .F-hom (f .snd)) (α .SPshHom.N-ob c' p')
        (α .SPshHom.N-ob c p) (α .SPshHom.N-hom c c' f p' p z))
  PROF .⋆ⱽIdLSq _ = refl -- nice
  PROF .⋆ⱽIdRSq _ = refl
  PROF .⋆ⱽAssocSq _ _ _ = refl
  PROF ._⋆ᴴSq_ {↑f = ↑f} {←f = ←f} {↓f = ↓f} {→f = →f}
                {↑f' = ↑f'} {↓f' = ↓f'} {→f' = →f'} α β .SPshHom.N-ob (c , c3) =
     rec _ _ isSet⊗
     (λ {d} s r → α .SPshHom.N-ob (c , d) s Tensor.,⊗ β .SPshHom.N-ob (d , c3) r)
      (λ {d}{d'} s g r →
        cong₂ Tensor._,⊗_ refl (natLS ↑f' (scompLRS ↓f' (→f ^opS) →f') β g r)
        ∙ Tensor.swap _ (→f .F-hom g) _
        ∙ cong₂ Tensor._,⊗_ (sym (natRS ↑f (scompLRS ↓f (←f ^opS) →f) α g s)) refl)
  PROF ._⋆ᴴSq_ {↑f = ↑f} {←f = ←f} {↓f = ↓f} {→f = →f}
                {↑f' = ↑f'} {↓f' = ↓f'} {→f' = →f'} α β .SPshHom.N-hom
                (c1 , c3) (c1' , c3') (f₁ , f₃) =
    ind _ _
      (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSet⊗ _ _)
      (λ {d} s r → ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
        (λ {d'} u v e →
          cong₂ Tensor._,⊗_
            (sym (natLS ↑f (scompLRS ↓f (←f ^opS) →f) α f₁ s))
            (sym (natRS ↑f' (scompLRS ↓f' (→f ^opS) →f') β f₃ r))
          ∙ cong ϕ e))
      where
      module LHS = ⊗.Tensor (appL (StrictBif→Bif ↑f) c1)
                             (appL (StrictBif→Bif (StrictSym ↑f')) c3)
      module RHS = ⊗.Tensor (appL (StrictBif→Bif ↓f) (←f .F-ob c1))
                            (appL (StrictBif→Bif (StrictSym ↓f')) (→f' .F-ob c3))
      ϕ : LHS._⊗_ → RHS._⊗_
      ϕ = LHS.rec RHS.isSet⊗
        (λ {d'} u v → α .SPshHom.N-ob (c1 , d') u RHS.,⊗ β .SPshHom.N-ob (d' , c3) v)
        (λ {d'}{d''} u g v →
          cong₂ RHS._,⊗_ refl (natLS ↑f' (scompLRS ↓f' (→f ^opS) →f') β g v)
          ∙ RHS.swap _ (→f .F-hom g) _
          ∙ cong₂ RHS._,⊗_ (sym (natRS ↑f (scompLRS ↓f (←f ^opS) →f) α g u)) refl)
  -- the left unitor uses a version of CoYoneda that I had Claude port over
  -- into the strict world
  -- This should probably be rewritten to be more high-level
  PROF .λᴴ  f .SPshHom.N-ob (c , d) = λRel-ob f c d
  PROF .λᴴ {x = C} f .SPshHom.N-hom (c , d) (c' , d') (f₁ , f₃) p' p eq =
    helper p' ∙ cong (λRel-ob f c d) eq
    where
      module T = ⊗.Tensor
        (appL (StrictBif→Bif (StrictHomBif C)) c')
        (appL (StrictBif→Bif (StrictSym f)) d')
      helper : ∀ q
        → StrictBifunctor.Bif-hom× f f₁ f₃ (λRel-ob f c' d' q)
        ≡ λRel-ob f c d (StrictRelator→Psh (PROF ._⋆ᴴ_ (PROF .idᴴ {x = C}) f)
              .F-hom (f₁ , f₃) q)
      helper = T.ind
        (λ _ → f .StrictBifunctor.Bif-ob c d .snd _ _)
        (λ {x} g r →
          sym (funExt⁻ (f .StrictBifunctor.Bif-LR-fuse f₁ f₃)
                       (f .StrictBifunctor.Bif-homL g d' r))
          ∙ cong (f .StrictBifunctor.Bif-homR c f₃)
                 (sym (funExt⁻ (f .StrictBifunctor.Bif-L-seq g f₁ _ refl) r))
          ∙ funExt⁻ (f .StrictBifunctor.Bif-LR-fuse
                       (Category._⋆_ (C ^op) g f₁) f₃) r
          ∙ sym (funExt⁻ (f .StrictBifunctor.Bif-RL-fuse
                             (Category._⋆_ (C ^op) g f₁) f₃) r))
  PROF .λᴴ⁻ f .SPshHom.N-ob (c , d) = λRel⁻-ob f c d
  PROF .λᴴ⁻ {x = C} f .SPshHom.N-hom (c , d) (c' , d') (f₁ , f₃) p' p eq =
    cong (T._,⊗ q) (C.⋆IdR f₁ ∙ sym (C.⋆IdL f₁))
    ∙ sym (T.swap C.id f₁ q)
    ∙ cong (C.id T.,⊗_) (funExt⁻ (f .StrictBifunctor.Bif-RL-fuse f₁ f₃) p' ∙ eq)
    where
      module C = Category C
      module T = ⊗.Tensor
        (appL (StrictBif→Bif (StrictHomBif C)) c)
        (appL (StrictBif→Bif (StrictSym f)) d)
      q = f .StrictBifunctor.Bif-homR c' f₃ p'
  PROF .λᴴλᴴ⁻ {x = C}{y = D} f = makeSPshHomPath
    (funExt λ (c , d) → funExt (λRel-ret f c d))
  PROF .λᴴ⁻λᴴ {x = C}{y = D} f = makeSPshHomPath
    (funExt λ (c , d) → funExt (λRel-sec f c d))
  PROF .λᴴ-nat {x = X}{y = Y}{z = Z}{w = W}{f = f}{g = g}{v = v}{u = u} α =
    -- gross
    subst2
      (λ pv pu → PathP
        (λ i → PROF .Sq {x = X}{y = Y}{z = Z}{w = W}
                         (PROF ._⋆ᴴ_ (PROF .idᴴ {x = X}) f) g (pv i) (pu i))
        (PROF ._⋆ⱽSq_ (PROF ._⋆ᴴSq_ (PROF .idᴴSq {v = v}) α) (PROF .λᴴ g))
        (PROF ._⋆ⱽSq_ (PROF .λᴴ f) α))
      (rUnit refl) (rUnit refl)
      (makeSPshHomPath
        (funExt λ (c , c3) →
          let module T = ⊗.Tensor
                (appL (StrictBif→Bif (StrictHomBif X)) c)
                (appL (StrictBif→Bif (StrictSym f)) c3)
          in funExt
            (T.ind
              (λ _ → (g .StrictBifunctor.Bif-ob (v .F-ob c) (u .F-ob c3)) .snd _ _)
              (λ {d} s r →
                sym (natLS f (scompLRS g (v ^opS) u) α s r)))))

  -- The right unitor should definitely be rewritten to be more high-level
  -- and reuse the ideas invoked in the left unitor rather than reimplementing
  -- them ad-hoc
  PROF .ρᴴ {x = C}{y = D} f .SPshHom.N-ob (c , d) =
    T.rec (f .StrictBifunctor.Bif-ob c d .snd)
      (λ {d'} p h → f .StrictBifunctor.Bif-homR c h p)
      (λ {d''}{d'} p g h →
        funExt⁻ (f .StrictBifunctor.Bif-R-seq g h _ refl) p)
    where
      module T = ⊗.Tensor (appL (StrictBif→Bif f) c)
                          (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d)
  PROF .ρᴴ {x = C}{y = D} f .SPshHom.N-hom
    (c , d) (c' , d') (f₁ , f₃) p' p eq =
    helper p' ∙ cong (ρ-ob c d) eq
    where
      module Dm = Category D
      module T' = ⊗.Tensor
        (appL (StrictBif→Bif f) c')
        (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d')
      ρ-ob : ∀ c d → _
      ρ-ob c d = T.rec (f .StrictBifunctor.Bif-ob c d .snd)
        (λ {d'} p h → f .StrictBifunctor.Bif-homR c h p)
        (λ {d''}{d'} p g h →
          funExt⁻ (f .StrictBifunctor.Bif-R-seq g h _ refl) p)
        where
          module T = ⊗.Tensor (appL (StrictBif→Bif f) c)
                              (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d)
      helper : ∀ q
        → f .StrictBifunctor.Bif-hom× f₁ f₃ (ρ-ob c' d' q)
        ≡ ρ-ob c d
            (StrictRelator→Psh (PROF ._⋆ᴴ_ f (PROF .idᴴ {x = D}))
              .F-hom (f₁ , f₃) q)
      helper = T'.ind
        (λ _ → f .StrictBifunctor.Bif-ob c d .snd _ _)
        (λ {x} s h →
          sym (funExt⁻ (f .StrictBifunctor.Bif-LR-fuse f₁ f₃)
                       (f .StrictBifunctor.Bif-homR c' h s))
          ∙ cong (f .StrictBifunctor.Bif-homR c f₃)
                 (funExt⁻ (f .StrictBifunctor.Bif-RL-fuse f₁ h) s
                  ∙ sym (funExt⁻ (f .StrictBifunctor.Bif-LR-fuse f₁ h) s))
          ∙ sym (funExt⁻ (f .StrictBifunctor.Bif-R-seq h f₃ _ refl)
                         (f .StrictBifunctor.Bif-homL f₁ x s)))
  PROF .ρᴴ⁻ {x = C}{y = D} f .SPshHom.N-ob (c , d) p = p T.,⊗ Category.id D
    where
      module T = ⊗.Tensor (appL (StrictBif→Bif f) c)
                          (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d)
  PROF .ρᴴ⁻ {y = D} f .SPshHom.N-hom (c , d) (c' , d') (f₁ , f₃) p' p eq =
    cong (q T.,⊗_) (D.⋆IdL f₃ ∙ sym (D.⋆IdR f₃))
    ∙ T.swap q f₃ D.id
    ∙ cong (T._,⊗ D.id) (funExt⁻ (f .StrictBifunctor.Bif-LR-fuse f₁ f₃) p' ∙ eq)
    where
      module D = Category D
      module T = ⊗.Tensor
        (appL (StrictBif→Bif f) c)
        (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d)
      q = f .StrictBifunctor.Bif-homL f₁ d' p'
  PROF .ρᴴρᴴ⁻ {x = C}{y = D} f = makeSPshHomPath
    (funExt λ (c , d) → funExt
      (T.ind (λ _ → T.isSet⊗ _ _)
        (λ {d'} p h →
          sym (T.swap p h (Category.id D))
          ∙ cong (p T.,⊗_) (Category.⋆IdR D h))))
    where
      module _ {c : Category.ob C} {d : Category.ob D} where
        module T = ⊗.Tensor (appL (StrictBif→Bif f) c)
                            (appL (StrictBif→Bif (StrictSym (StrictHomBif D))) d)
  PROF .ρᴴ⁻ρᴴ {y = D} f = makeSPshHomPath
    (funExt λ (c , d) → funExt
      (λ p → funExt⁻ (f .StrictBifunctor.Bif-R-id (Category.id D) refl) p))
  PROF .ρᴴ-nat {x = X}{y = Y}{z = Z}{w = W}{f = f}{g = g}{v = v}{u = u} α =
    subst2 (λ pv pu → PathP
        (λ i → PROF .Sq {x = X}{y = Y}{z = Z}{w = W}
                         (PROF ._⋆ᴴ_ f (PROF .idᴴ {x = Y})) g (pv i) (pu i))
        (PROF ._⋆ⱽSq_ (PROF ._⋆ᴴSq_ α (PROF .idᴴSq {v = u})) (PROF .ρᴴ g))
        (PROF ._⋆ⱽSq_ (PROF .ρᴴ f) α))
      (rUnit refl) (rUnit refl)
      (makeSPshHomPath
        (funExt λ (c , c3) →
          let module T = ⊗.Tensor
                (appL (StrictBif→Bif f) c)
                (appL (StrictBif→Bif (StrictSym (StrictHomBif Y))) c3)
          in funExt
            (T.ind
              (λ _ → (g .StrictBifunctor.Bif-ob (v .F-ob c) (u .F-ob c3)) .snd _ _)
              (λ {d'} p h →
                sym (natRS f (scompLRS g (v ^opS) u) α h p)))))
  PROF .αᴴ f g h .SPshHom.N-ob (c , d) = αᴴ-Nob f g h c d
  PROF .αᴴ f g h .SPshHom.N-hom (c , d) (c' , d') (f₁ , f₃) =
    ind _ _ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSet⊗ _ _)
      (ind _ _ (λ _ → isPropΠ3 λ _ _ _ → isSet⊗ _ _)
        (λ w x y → ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
          (ind _ _ (λ _ → isPropΠ2 λ _ _ → isSet⊗ _ _)
            (λ u v r e → cong (αᴴ-Nob f g h c d) e))))
  PROF .αᴴ⁻ f g h .SPshHom.N-ob (c , d) = αᴴ⁻-Nob f g h c d
  PROF .αᴴ⁻ f g h .SPshHom.N-hom (c , d) (c' , d') (f₁ , f₃) =
    ind _ _ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isSet⊗ _ _)
      (λ p → ind _ _ (λ _ → isPropΠ2 λ _ _ → isSet⊗ _ _)
        (λ q r p₂ eq → cong (αᴴ⁻-Nob f g h c d) eq))
  PROF .αᴴαᴴ⁻ f g h = makeSPshHomPath (funExt λ _ → funExt
    (ind _ _ (λ _ → isSet⊗ _ _) (ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
      (λ _ _ _ → refl))))
  PROF .αᴴ⁻αᴴ f g h = makeSPshHomPath (funExt λ _ → funExt
    (ind _ _ (λ _ → isSet⊗ _ _)
      (λ p → ind _ _ (λ _ → isSet⊗ _ _) (λ _ _ → refl))))
  PROF .αᴴ-nat {x₁ = X₁}{x₄ = X₄}{y₁ = Y₁}{y₄ = Y₄}
               {f₁ = f₁}{f₂ = f₂}{f₃ = f₃}
               {g₁ = g₁}{g₂ = g₂}{g₃ = g₃} α₁ α₂ α₃ =
    subst2
      (λ pv pu → PathP
        (λ i → PROF .Sq {x = X₁}{y = X₄}{z = Y₁}{w = Y₄}
                         (PROF ._⋆ᴴ_ (PROF ._⋆ᴴ_ f₁ f₂) f₃)
                         (PROF ._⋆ᴴ_ g₁ (PROF ._⋆ᴴ_ g₂ g₃))
                         (pv i) (pu i))
        (PROF ._⋆ⱽSq_ (PROF ._⋆ᴴSq_ (PROF ._⋆ᴴSq_ α₁ α₂) α₃)
                       (PROF .αᴴ g₁ g₂ g₃))
        (PROF ._⋆ⱽSq_ (PROF .αᴴ f₁ f₂ f₃)
                       (PROF ._⋆ᴴSq_ α₁ (PROF ._⋆ᴴSq_ α₂ α₃))))
      (rUnit refl) (rUnit refl)
      (makeSPshHomPath (funExt λ _ → funExt
        (ind _ _ (λ _ → isSet⊗ _ _)
          (ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
            (λ _ _ _ → refl)))))
  PROF .pentagon _ _ _ _ =
    makeSPshHomPath (funExt λ _ → funExt
      (ind _ _ (λ _ → isSet⊗ _ _)
        (ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
          (ind _ _ (λ _ → isPropΠ2 λ _ _ → isSet⊗ _ _)
            (λ _ _ _ _ → refl)))))
  PROF .triangle f g =
    makeSPshHomPath (funExt λ _ → funExt
      (ind _ _ (λ _ → isSet⊗ _ _)
        (ind _ _ (λ _ → isPropΠ λ _ → isSet⊗ _ _)
          (λ w x y → Tensor.swap w x y))))
  PROF .interchange α β γ δ =
    makeSPshHomPath (funExt λ _ → funExt
      (ind _ _ (λ _ → isSet⊗ _ _) (λ _ _ → refl)))
