-- Strict bifunctors
-- Also strict relators,
-- StrictHomBif, StrictCurryBifunctor, ⊗-BifS, natLS/natRS helpers,
-- and the specialized CoYoneda for strict relators used by PROF.λᴴ.
-- Written by Claude
module Cubical.Categories.Functors.Strict.Bifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Morphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Constructions.Tensor

open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Functors.Strict.Presheaf

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' : Level

open StrictFunctor
open Bifunctor
open BifunctorSepAx

-- ===== Strict Bifunctors =====
-- Witness-passing identity and composition laws on both sides,
-- mirroring BifunctorSepAx.

record StrictBifunctor (C : Category ℓc ℓc')
                       (D : Category ℓd ℓd')
                       (E : Category ℓe ℓe')
       : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓd (ℓ-max ℓd' (ℓ-max ℓe ℓe'))))) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
  field
    Bif-ob : C .Category.ob → D .Category.ob → E .Category.ob

    Bif-homL : ∀ {c c'} → (f : C [ c , c' ]) → ∀ d
             → E [ Bif-ob c d , Bif-ob c' d ]
    Bif-L-id : ∀ {c d} (f : C [ c , c ]) → C.id ≡ f
             → Bif-homL f d ≡ E.id
    Bif-L-seq : ∀ {c c' c'' d}
              (f : C [ c , c' ])(f' : C [ c' , c'' ])(h : C [ c , c'' ])
             → f C.⋆ f' ≡ h
             → Bif-homL h d ≡ Bif-homL f d E.⋆ Bif-homL f' d

    Bif-homR : ∀ {d d'} c → (g : D [ d , d' ]) → E [ Bif-ob c d , Bif-ob c d' ]
    Bif-R-id : ∀ {c d} (g : D [ d , d ]) → D.id ≡ g
             → Bif-homR c g ≡ E.id
    Bif-R-seq : ∀ {c d d' d''}
              (g : D [ d , d' ])(g' : D [ d' , d'' ])(h : D [ d , d'' ])
             → g D.⋆ g' ≡ h
             → Bif-homR c h ≡ Bif-homR c g E.⋆ Bif-homR c g'

    Bif-hom× : ∀ {c c' d d'} (f : C [ c , c' ])(g : D [ d , d' ])
             → E [ Bif-ob c d , Bif-ob c' d' ]
    Bif-LR-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homL f d E.⋆ Bif-homR c' g
               ≡ Bif-hom× f g
    Bif-RL-fuse : ∀ {c c' d d'} → (f : C [ c , c' ]) (g : D [ d , d' ])
               → Bif-homR c g E.⋆ Bif-homL f d'
               ≡ Bif-hom× f g

open StrictBifunctor

StrictBif→Bif : ∀ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → StrictBifunctor C D E → Bifunctor C D E
StrictBif→Bif F = mkBifunctorSepAx B where
  B : BifunctorSepAx _ _ _
  B .Bif-ob = F .StrictBifunctor.Bif-ob
  B .Bif-homL = F .StrictBifunctor.Bif-homL
  B .BifunctorSepAx.Bif-L-id = F .Bif-L-id _ refl
  B .BifunctorSepAx.Bif-L-seq f f' = F .Bif-L-seq f f' _ refl
  B .Bif-homR = F .StrictBifunctor.Bif-homR
  B .BifunctorSepAx.Bif-R-id = F .Bif-R-id _ refl
  B .BifunctorSepAx.Bif-R-seq g g' = F .Bif-R-seq g g' _ refl
  B .BifunctorSepAx.Bif-hom× = F .StrictBifunctor.Bif-hom×
  B .BifunctorSepAx.Bif-LR-fuse = F .StrictBifunctor.Bif-LR-fuse
  B .BifunctorSepAx.Bif-RL-fuse = F .StrictBifunctor.Bif-RL-fuse

-- Reverse direction: any Bifunctor can be viewed as a StrictBifunctor
-- by synthesizing the witness-passing laws from the ordinary laws.
Bif→StrictBif : ∀ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → Bifunctor C D E → StrictBifunctor C D E
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-ob =
  F .Bifunctor.Bif-ob
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-homL =
  F .Bifunctor.Bif-homL
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-L-id {d = d} f e =
  cong (λ x → F .Bifunctor.Bif-homL x d) (sym e) ∙ F .Bifunctor.Bif-L-id
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-L-seq {d = d} f f' h e =
  cong (λ x → F .Bifunctor.Bif-homL x d) (sym e) ∙ F .Bifunctor.Bif-L-seq f f'
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-homR =
  F .Bifunctor.Bif-homR
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-R-id {c = c} g e =
  cong (λ x → F .Bifunctor.Bif-homR c x) (sym e) ∙ F .Bifunctor.Bif-R-id
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-R-seq {c = c} g g' h e =
  cong (λ x → F .Bifunctor.Bif-homR c x) (sym e) ∙ F .Bifunctor.Bif-R-seq g g'
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-hom× =
  F .Bifunctor.Bif-hom×
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-LR-fuse =
  F .Bifunctor.Bif-LR-fuse
Bif→StrictBif {C = C}{D = D}{E = E} F .StrictBifunctor.Bif-RL-fuse =
  F .Bifunctor.Bif-RL-fuse

-- Strict Sym: swap the two arguments of a StrictBifunctor.
StrictSym : ∀ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → StrictBifunctor C D E → StrictBifunctor D C E
StrictSym F .StrictBifunctor.Bif-ob d c = F .Bif-ob c d
StrictSym F .StrictBifunctor.Bif-homL g c = F .Bif-homR c g
StrictSym F .StrictBifunctor.Bif-L-id g e = F .Bif-R-id g e
StrictSym F .StrictBifunctor.Bif-L-seq g g' h e = F .Bif-R-seq g g' h e
StrictSym F .StrictBifunctor.Bif-homR d f = F .Bif-homL f d
StrictSym F .StrictBifunctor.Bif-R-id f e = F .Bif-L-id f e
StrictSym F .StrictBifunctor.Bif-R-seq f f' h e = F .Bif-L-seq f f' h e
StrictSym F .StrictBifunctor.Bif-hom× g f = F .Bif-hom× f g
StrictSym F .StrictBifunctor.Bif-LR-fuse g f = F .Bif-RL-fuse f g
StrictSym F .StrictBifunctor.Bif-RL-fuse g f = F .Bif-LR-fuse f g

-- ===== Strict Relators and constructions =====

-- A strict relator: StrictBifunctor (C^op) D (SET ℓ)
StrictRelatoro* : (C : Category ℓc ℓc') → ∀ ℓe → (D : Category ℓd ℓd')
  → Type _
StrictRelatoro* C ℓ D = StrictBifunctor (C ^op) D (SET ℓ)

-- Strict composition of a StrictBifunctor with StrictFunctors on both sides.
scompLS : ∀ {ℓc ℓc' ℓc'' ℓc''' ℓd ℓd' ℓe ℓe' : Level}
  → {C : Category ℓc ℓc'}{C' : Category ℓc'' ℓc'''}
    {D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → StrictBifunctor C' D E → StrictFunctor C C' → StrictBifunctor C D E
scompLS F G .StrictBifunctor.Bif-ob c d = F .StrictBifunctor.Bif-ob (G .F-ob c) d
scompLS F G .StrictBifunctor.Bif-homL f d = F .StrictBifunctor.Bif-homL (G .F-hom f) d
scompLS F G .StrictBifunctor.Bif-L-id f e =
  F .Bif-L-id (G .F-hom f) (sym (G .F-id f e))
scompLS F G .StrictBifunctor.Bif-L-seq f f' h e =
  F .Bif-L-seq (G .F-hom f) (G .F-hom f') (G .F-hom h) (sym (G .F-seq f f' h e))
scompLS F G .StrictBifunctor.Bif-homR c g = F .StrictBifunctor.Bif-homR (G .F-ob c) g
scompLS F G .StrictBifunctor.Bif-R-id g e = F .Bif-R-id g e
scompLS F G .StrictBifunctor.Bif-R-seq g g' h e = F .Bif-R-seq g g' h e
scompLS F G .StrictBifunctor.Bif-hom× f g = F .StrictBifunctor.Bif-hom× (G .F-hom f) g
scompLS F G .StrictBifunctor.Bif-LR-fuse f g = F .StrictBifunctor.Bif-LR-fuse (G .F-hom f) g
scompLS F G .StrictBifunctor.Bif-RL-fuse f g = F .StrictBifunctor.Bif-RL-fuse (G .F-hom f) g

scompRS : ∀ {ℓc ℓc' ℓd ℓd' ℓd'' ℓd''' ℓe ℓe' : Level}
  → {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
    {D' : Category ℓd'' ℓd'''}{E : Category ℓe ℓe'}
  → StrictBifunctor C D' E → StrictFunctor D D' → StrictBifunctor C D E
scompRS F H .StrictBifunctor.Bif-ob c d = F .StrictBifunctor.Bif-ob c (H .F-ob d)
scompRS F H .StrictBifunctor.Bif-homL f d = F .StrictBifunctor.Bif-homL f (H .F-ob d)
scompRS F H .StrictBifunctor.Bif-L-id f e = F .Bif-L-id f e
scompRS F H .StrictBifunctor.Bif-L-seq f f' h e = F .Bif-L-seq f f' h e
scompRS F H .StrictBifunctor.Bif-homR c g = F .StrictBifunctor.Bif-homR c (H .F-hom g)
scompRS F H .StrictBifunctor.Bif-R-id g e =
  F .Bif-R-id (H .F-hom g) (sym (H .F-id g e))
scompRS F H .StrictBifunctor.Bif-R-seq g g' h e =
  F .Bif-R-seq (H .F-hom g) (H .F-hom g') (H .F-hom h) (sym (H .F-seq g g' h e))
scompRS F H .StrictBifunctor.Bif-hom× f g = F .StrictBifunctor.Bif-hom× f (H .F-hom g)
scompRS F H .StrictBifunctor.Bif-LR-fuse f g = F .StrictBifunctor.Bif-LR-fuse f (H .F-hom g)
scompRS F H .StrictBifunctor.Bif-RL-fuse f g = F .StrictBifunctor.Bif-RL-fuse f (H .F-hom g)

scompLRS : ∀ {ℓc ℓc' ℓc'' ℓc''' ℓd ℓd' ℓd'' ℓd''' ℓe ℓe' : Level}
  → {C : Category ℓc ℓc'}{C' : Category ℓc'' ℓc'''}
    {D : Category ℓd ℓd'}{D' : Category ℓd'' ℓd'''}
    {E : Category ℓe ℓe'}
  → StrictBifunctor C' D' E
  → StrictFunctor C C' → StrictFunctor D D'
  → StrictBifunctor C D E
scompLRS F G H = scompLS (scompRS F H) G

-- Strict HomBif: witness-passing identity and composition laws.
-- Bif-hom× f g h = (f ⋆ h) ⋆ g, making LR-fuse = refl.
module _ {ℓc ℓc' : Level} where
  private module H (C : Category ℓc ℓc') = Category C
  StrictHomBif : (C : Category ℓc ℓc') → StrictBifunctor (C ^op) C (SET ℓc')
  StrictHomBif C .StrictBifunctor.Bif-ob c c' = (C [ c , c' ]) , H.isSetHom C
  StrictHomBif C .StrictBifunctor.Bif-homL f c' g = H._⋆_ C f g
  StrictHomBif C .StrictBifunctor.Bif-L-id f e =
    funExt λ g → cong (λ x → H._⋆_ C x g) (sym e) ∙ H.⋆IdL C g
  StrictHomBif C .StrictBifunctor.Bif-L-seq f f' h e =
    funExt λ g → cong (λ x → H._⋆_ C x g) (sym e) ∙ H.⋆Assoc C f' f g
  StrictHomBif C .StrictBifunctor.Bif-homR c g f = H._⋆_ C f g
  StrictHomBif C .StrictBifunctor.Bif-R-id g e =
    funExt λ f → cong (H._⋆_ C f) (sym e) ∙ H.⋆IdR C f
  StrictHomBif C .StrictBifunctor.Bif-R-seq g g' h e =
    funExt λ f → cong (H._⋆_ C f) (sym e) ∙ sym (H.⋆Assoc C f g g')
  StrictHomBif C .StrictBifunctor.Bif-hom× f g h = H._⋆_ C (H._⋆_ C f h) g
  StrictHomBif C .StrictBifunctor.Bif-LR-fuse f g = refl
  StrictHomBif C .StrictBifunctor.Bif-RL-fuse f g =
    funExt λ h → sym (H.⋆Assoc C f h g)

-- Relator→Psh for strict relators: produces a StrictPresheaf on C ×C D^op.
-- The key: morphisms in C ×C (D^op) are pairs, and the action is Bif-hom×.
module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  StrictRelator→Psh : (P : StrictRelatoro* C ℓe D)
    → StrictPresheaf (C ×C D ^op) ℓe
  StrictRelator→Psh P .F-ob (c , d) = P .StrictBifunctor.Bif-ob c d
  StrictRelator→Psh P .F-hom (f , g) = P .StrictBifunctor.Bif-hom× f g
  StrictRelator→Psh {ℓe = ℓe} P .F-id (f , g) e =
    sym (P .StrictBifunctor.Bif-LR-fuse f g)
    -- ∙ cong₂ (P .Bif-L-id f (cong fst e)) (P .Bif-R-id g (cong snd e))
    ∙ funExt (λ y → funExt⁻ (P .Bif-R-id g (cong snd e)) _
                  ∙ funExt⁻ (P .Bif-L-id f (cong fst e)) _)
    where open Category (SET ℓe)
  StrictRelator→Psh {ℓe = ℓe} P .F-seq (f₁ , g₁) (f₂ , g₂) (f , g) e =
    sym (P .Bif-LR-fuse f g)
    ∙ funExt (λ y →
        -- Start: R(c'',g)(L(f,d)(y))
        funExt⁻ (P .Bif-R-seq g₁ g₂ g (cong snd e)) (P .Bif-homL f _ y)
        -- Expand L(f,d)(y) to L(f₂,d)(L(f₁,d)(y))
        ∙ cong (λ x → P .Bif-homR _ g₂ (P .Bif-homR _ g₁ x))
               (funExt⁻ (P .Bif-L-seq f₁ f₂ f (cong fst e)) y)
        -- Interchange: R(c'',g₁)∘L(f₂,d) = L(f₂,d')∘R(c',g₁)
        ∙ cong (P .Bif-homR _ g₂)
               (funExt⁻ (P .Bif-LR-fuse f₂ g₁
                       ∙ sym (P .Bif-RL-fuse f₂ g₁))
                        (P .Bif-homL f₁ _ y))
        -- Fold R(c'',g₂)∘L(f₂,d') into hom×(f₂,g₂)
        ∙ funExt⁻ (P .Bif-LR-fuse f₂ g₂) _
        -- Fold R(c',g₁)∘L(f₁,d) into hom×(f₁,g₁)
        ∙ cong (P .Bif-hom× f₂ g₂)
               (funExt⁻ (P .Bif-LR-fuse f₁ g₁) y))
    where open Category (SET ℓe)

-- Strict CurryBifunctor: StrictBifunctor → StrictFunctor C (FUNCTOR D E).
-- The witness-passing F-id/F-seq use makeNatTransPath.
StrictCurryBifunctor : ∀ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
  → StrictBifunctor C D E → StrictFunctor C (FUNCTOR D E)
StrictCurryBifunctor F .F-ob c = appL (StrictBif→Bif F) c
StrictCurryBifunctor F .F-hom f .NatTrans.N-ob d = appR (StrictBif→Bif F) d .Functor.F-hom f
StrictCurryBifunctor F .F-hom f .NatTrans.N-hom g = Bif-RL-commute (StrictBif→Bif F) f g
StrictCurryBifunctor F .F-id f e =
  makeNatTransPath (funExt λ d → F .Bif-L-id f e)
StrictCurryBifunctor F .F-seq f₁ f₂ f e =
  makeNatTransPath (funExt λ d → F .Bif-L-seq f₁ f₂ f e)

-- Strict ⊗-Bif: the tensor product of presheaves as a StrictBifunctor.
-- Obtained by converting the non-strict ⊗-Bif via Bif→StrictBif.
module _ {C : Category ℓc ℓc'} where
  ⊗-BifS : ∀ {ℓP ℓQ}
    → StrictBifunctor (FUNCTOR C (SET ℓP))
                      (FUNCTOR (C ^op) (SET ℓQ))
                      (SET (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓP ℓQ)))
  ⊗-BifS = Bif→StrictBif (⊗-Bif {C = C})

-- ===== L/R naturality helpers for SPshHom on strict relators =====
module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} {ℓp ℓq}
  (P : StrictRelatoro* C ℓp D) (Q : StrictRelatoro* C ℓq D)
  where
  private
    module Cm = Category C
    module Dm = Category D
    module P = StrictBifunctor P
    module Q = StrictBifunctor Q

  open SPshHom

  natLS : (α : SPshHom (StrictRelator→Psh P) (StrictRelator→Psh Q))
        → ∀ {c c' d} (f : C [ c' , c ]) (p : ⟨ P.Bif-ob c d ⟩)
        → α .N-ob (c' , d) (P.Bif-homL f d p)
        ≡ Q.Bif-homL f d (α .N-ob (c , d) p)
  natLS α {c}{c'}{d} f p =
    sym (α .N-hom (c' , d) (c , d) (f , Dm.id) p (P.Bif-homL f d p) witness-P)
    ∙ witness-Q
    where
      witness-P : P.Bif-hom× f Dm.id p ≡ P.Bif-homL f d p
      witness-P = funExt⁻ (sym (P.Bif-LR-fuse f Dm.id)) p
                ∙ funExt⁻ (P.Bif-R-id Dm.id refl) (P.Bif-homL f d p)
      witness-Q : Q.Bif-hom× f Dm.id (α .N-ob (c , d) p)
                ≡ Q.Bif-homL f d (α .N-ob (c , d) p)
      witness-Q = funExt⁻ (sym (Q.Bif-LR-fuse f Dm.id)) _
                ∙ funExt⁻ (Q.Bif-R-id Dm.id refl) _

  natRS : (α : SPshHom (StrictRelator→Psh P) (StrictRelator→Psh Q))
        → ∀ {c d d'} (g : D [ d , d' ]) (p : ⟨ P.Bif-ob c d ⟩)
        → α .N-ob (c , d') (P.Bif-homR c g p)
        ≡ Q.Bif-homR c g (α .N-ob (c , d) p)
  natRS α {c}{d}{d'} g p =
    sym (α .N-hom (c , d') (c , d) (Cm.id , g) p (P.Bif-homR c g p) witness-P)
    ∙ witness-Q
    where
      witness-P : P.Bif-hom× Cm.id g p ≡ P.Bif-homR c g p
      witness-P = funExt⁻ (sym (P.Bif-RL-fuse Cm.id g)) p
                ∙ funExt⁻ (P.Bif-L-id Cm.id refl) (P.Bif-homR c g p)
      witness-Q : Q.Bif-hom× Cm.id g (α .N-ob (c , d) p)
                ≡ Q.Bif-homR c g (α .N-ob (c , d) p)
      witness-Q = funExt⁻ (sym (Q.Bif-RL-fuse Cm.id g)) _
                ∙ funExt⁻ (Q.Bif-L-id Cm.id refl) _

-- ===== Specialized CoYoneda for strict relators =====
-- PROF.λᴴ needs an iso between the tensor
--   (appL (StrictBif→Bif (StrictHomBif C)) c ⊗ appL (StrictBif→Bif (StrictSym f)) d)
-- and ⟨ f .Bif-ob c d ⟩.  This is CoYoneda specialized to the strict
-- relator's shape, so we can take advantage of fr's witness-passing
-- L-id/L-seq laws directly rather than going through Fun→Strict.
module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}{ℓp}
  (fr : StrictRelatoro* C ℓp D) where
  private
    module fr = StrictBifunctor fr
    module Cm = Category C
    module Dm = Category D

  λRelPc : Cm.ob → Functor C (SET ℓc')
  λRelPc c = appL (StrictBif→Bif (StrictHomBif C)) c

  λRelQd : Dm.ob → Functor (C ^op) (SET ℓp)
  λRelQd d = appL (StrictBif→Bif (StrictSym fr)) d

  λRel-ob : ∀ c d → (λRelPc c ⊗ λRelQd d) → ⟨ fr .Bif-ob c d ⟩
  λRel-ob c d = T.rec (fr .Bif-ob c d .snd)
    (λ {x} g p → fr .Bif-homL g d p)
    (λ {x}{y} p h q → sym (funExt⁻ (fr .Bif-L-seq h p _ refl) q))
    where module T = Tensor (λRelPc c) (λRelQd d)

  λRel⁻-ob : ∀ c d → ⟨ fr .Bif-ob c d ⟩ → (λRelPc c ⊗ λRelQd d)
  λRel⁻-ob c d p = Cm.id T.,⊗ p
    where module T = Tensor (λRelPc c) (λRelQd d)

  -- Section: λRel-ob ∘ λRel⁻-ob = id
  λRel-sec : ∀ c d (p : ⟨ fr .Bif-ob c d ⟩)
           → λRel-ob c d (λRel⁻-ob c d p) ≡ p
  λRel-sec c d p = funExt⁻ (fr .Bif-L-id Cm.id refl) p

  -- Retraction: λRel⁻-ob ∘ λRel-ob = id
  λRel-ret : ∀ c d (x : λRelPc c ⊗ λRelQd d)
           → λRel⁻-ob c d (λRel-ob c d x) ≡ x
  λRel-ret c d = T.ind (λ _ → T.isSet⊗ _ _)
    (λ {y} g p →
      T.swap Cm.id g p
      ∙ cong (T._,⊗ p) (Cm.⋆IdL g))
    where module T = Tensor (λRelPc c) (λRelQd d)
