{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.ContractiveCompleteness
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
  (dir : DirectStr A Wo) where

open import Cubical.Foundations.Isomorphism using (Iso ; isoFunInjective)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open FE using (EnrichmentFor)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
open import Cubical.Categories.Enriched.Enrichment.Stage.Yoneda A ℓ
open import Cubical.Categories.Enriched.Enrichment.Limits.Power
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical
import Cubical.Categories.Enriched.Enrichment.Stage.Limits as StageLimits
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.Terminal.More using (terminalToUniversalElement)
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras using (ALG ; InitialAlgebra)
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras using (TerminalCoalgebra)
import Cubical.Categories.Enriched.Enrichment.Stage as Stage
import Cubical.Categories.Enriched.Enrichment.Stage.Functor as StageFunctor
open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded)

open Functor
open PshHomStrict
open DirectNotation dir
open PshMon A ℓ using (𝓟Mon ; 𝓟 ; ℓm)
open import Cubical.Categories.Monoidal.Base using (MonoidalCategory)
open MonoidalCategory 𝓟Mon using (_⊗_)

private
  module A = Category A

module _ {ℓC ℓC' : Level} {C : Category ℓC ℓC'} (ℰ : Enrichment C 𝓟Mon)
  (F : Functor C C) (lc : isLocallyContractive pshGuarded ℰ ℰ F) where
  private
    module ℰ = Enrichment ℰ
    module C = Category C
    module ▷S = Stage (Later.▷ℰ pshGuarded ℰ)
  open Stage ℰ

  nextₛ : ∀ c → Functor (Stage c) (▷S.Stage c)
  nextₛ = StageFunctor.stageF (forgetAgree pshGuarded (Later.nextF-Enr pshGuarded ℰ))

  F▷ₛ : ∀ c → Functor (▷S.Stage c) (Stage c)
  F▷ₛ = StageFunctor.stageF (lc .fst)

  Fₛ : ∀ c → Functor (Stage c) (Stage c)
  Fₛ c = F▷ₛ c ∘F nextₛ c

  at-F : ∀ c {X Y} (f : C [ X , Y ]) → at c ⟪ F ⟪ f ⟫ ⟫ ≡ Fₛ c ⟪ at c ⟪ f ⟫ ⟫
  at-F c f = funExt⁻ (funExt⁻ (cong N-ob (lc .snd f)) c) tt*

  Fₛ-res : ∀ {c c'} (k : A [ c' , c ]) {X Y} (α : Stage c [ X , Y ])
    → res k ⟪ Fₛ c ⟪ α ⟫ ⟫ ≡ Fₛ c' ⟪ res k ⟪ α ⟫ ⟫
  Fₛ-res k α =
    StageFunctor.stageF-res (lc .fst) k _
    ∙ cong (F▷ₛ _ ⟪_⟫) (StageFunctor.stageF-res (forgetAgree pshGuarded (Later.nextF-Enr pshGuarded ℰ)) k α)

  record Approx (c : A.ob) : Type (ℓ-max ℓC ℓm) where
    field
      obj : C.ob
      roll : CatIso (Stage c) (Fₛ c ⟅ obj ⟆) obj

    τ : Stage c [ F ⟅ obj ⟆ , obj ]
    τ = roll .fst

    σ : Stage c [ obj , F ⟅ obj ⟆ ]
    σ = roll .snd .isIso.inv

  open Approx

  resA : ∀ {c c'} → A [ c' , c ] → Approx c → Approx c'
  resA k a .obj = a .obj
  resA k a .roll = F-Iso {F = res k} (a .roll)

  module _ {c : A.ob} (a b : Approx c) where
    private
      H = ℰ.VE[ a .obj , b .obj ]
      E = ▷Psh H ⇒PshLargeStrict H

      Φ : ⟨ E .F-ob c ⟩
      Φ .N-ob d (g , β) = res g ⟪ (σ a) ⟫ ⋆ₛ (F▷ₛ d ⟪ β ⟫ ⋆ₛ res g ⟪ (τ b) ⟫)
      Φ .N-hom d' d k (g , β) (g' , β') e =
          res k .F-seq _ _
        ∙ cong (res k ⟪ res g ⟪ (σ a) ⟫ ⟫ ⋆ₛ_) (res k .F-seq _ _)
        ∙ cong₂ _⋆ₛ_
            (res-seq g k ((σ a)) ∙ cong (λ m → res m ⟪ (σ a) ⟫) (cong fst e))
            (cong₂ _⋆ₛ_
              (StageFunctor.stageF-res (lc .fst) k β ∙ cong (F▷ₛ d' ⟪_⟫) (cong snd e))
              (res-seq g k ((τ b)) ∙ cong (λ m → res m ⟪ (τ b) ⟫) (cong fst e)))

    κ : Stage c [ a .obj , b .obj ]
    κ = löb H .N-ob c Φ

    κ-fix : κ ≡ (σ a) ⋆ₛ (Fₛ c ⟪ κ ⟫ ⋆ₛ (τ b))
    κ-fix =
      funExt⁻ (funExt⁻ (cong N-ob (löb-fix H)) c) Φ
      ∙ cong₂ (λ m n → m ⋆ₛ (Fₛ c ⟪ κ ⟫ ⋆ₛ n)) (res-id _) (res-id _)

    κ-uniq : (h : Stage c [ a .obj , b .obj ]) → h ≡ (σ a) ⋆ₛ (Fₛ c ⟪ h ⟫ ⋆ₛ (τ b)) → h ≡ κ
    κ-uniq h h-fix =
      sym (res-id h)
      ∙ (λ i → löb-uniq H (yoneda c E .Iso.inv Φ) (yoneda c H .Iso.inv h) hyp i .N-ob c (lift A.id))
      ∙ cong (löb H .N-ob c) (funExt⁻ (E .F-id) Φ)
      where
      hyp : yoneda c H .Iso.inv h
        ≡ ×PshIntroStrict (yoneda c E .Iso.inv Φ) (yoneda c H .Iso.inv h ⋆PshHomStrict next H)
          ⋆PshHomStrict appPshHomStrict (▷Psh H) H
      hyp = makePshHomStrictPath (funExt λ d → funExt λ (lift g) →
          cong (res g ⟪_⟫) h-fix
        ∙ res g .F-seq _ _
        ∙ cong (res g ⟪ (σ a) ⟫ ⋆ₛ_) (res g .F-seq _ _ ∙ cong (_⋆ₛ res g ⟪ (τ b) ⟫) (Fₛ-res g h))
        ∙ cong₂ (λ m n → res m ⟪ (σ a) ⟫ ⋆ₛ (Fₛ d ⟪ res g ⟪ h ⟫ ⟫ ⋆ₛ res n ⟪ (τ b) ⟫))
            (sym (A.⋆IdL g)) (sym (A.⋆IdL g)))

  module _ {c : A.ob} where
    private
      module S = Category (Stage c)

    στ : (a : Approx c) → σ a ⋆ₛ τ a ≡ idₛ
    στ a = a .roll .snd .isIso.sec

    τσ : (a : Approx c) → τ a ⋆ₛ σ a ≡ idₛ
    τσ a = a .roll .snd .isIso.ret

    κ-id : (a : Approx c) → κ a a ≡ idₛ
    κ-id a = sym (κ-uniq a a idₛ
      (sym (cong (σ a ⋆ₛ_) (cong (_⋆ₛ τ a) (Fₛ c .F-id) ∙ S.⋆IdL _) ∙ στ a)))

    κ-comp : (a b b' : Approx c) → κ a b ⋆ₛ κ b b' ≡ κ a b'
    κ-comp a b b' = κ-uniq a b' _
      ( cong₂ _⋆ₛ_ (κ-fix a b) (κ-fix b b')
      ∙ S.⋆Assoc _ _ _
      ∙ cong (σ a ⋆ₛ_) (S.⋆Assoc _ _ _)
      ∙ cong (λ m → σ a ⋆ₛ (Fₛ c ⟪ κ a b ⟫ ⋆ₛ m)) (sym (S.⋆Assoc _ _ _))
      ∙ cong (λ m → σ a ⋆ₛ (Fₛ c ⟪ κ a b ⟫ ⋆ₛ (m ⋆ₛ (Fₛ c ⟪ κ b b' ⟫ ⋆ₛ τ b')))) (τσ b)
      ∙ cong (λ m → σ a ⋆ₛ (Fₛ c ⟪ κ a b ⟫ ⋆ₛ m)) (S.⋆IdL _)
      ∙ cong (σ a ⋆ₛ_) (sym (S.⋆Assoc _ _ _))
      ∙ cong (λ m → σ a ⋆ₛ (m ⋆ₛ τ b')) (sym (Fₛ c .F-seq (κ a b) (κ b b'))))

    κ-inv : (a b : Approx c) → κ a b ⋆ₛ κ b a ≡ idₛ
    κ-inv a b = κ-comp a b a ∙ κ-id a

    κ-iso : (a b : Approx c) → CatIso (Stage c) (a .obj) (b .obj)
    κ-iso a b = κ a b , isiso (κ b a) (κ-inv b a) (κ-inv a b)

    σ-κ : (b b' : Approx c) → σ b' ⋆ₛ Fₛ c ⟪ κ b' b ⟫ ≡ κ b' b ⋆ₛ σ b
    σ-κ b b' = sym
      ( cong (_⋆ₛ σ b) (κ-fix b' b)
      ∙ S.⋆Assoc _ _ _
      ∙ cong (σ b' ⋆ₛ_) (S.⋆Assoc _ _ _)
      ∙ cong (λ m → σ b' ⋆ₛ (Fₛ c ⟪ κ b' b ⟫ ⋆ₛ m)) (τσ b)
      ∙ cong (σ b' ⋆ₛ_) (S.⋆IdR _))

    τ-κ : (b b' : Approx c) → τ b ⋆ₛ κ b b' ≡ Fₛ c ⟪ κ b b' ⟫ ⋆ₛ τ b'
    τ-κ b b' =
      cong (τ b ⋆ₛ_) (κ-fix b b')
      ∙ sym (S.⋆Assoc _ _ _)
      ∙ cong (_⋆ₛ (Fₛ c ⟪ κ b b' ⟫ ⋆ₛ τ b')) (τσ b)
      ∙ S.⋆IdL _

  κ-res : ∀ {c c'} (k : A [ c' , c ]) (a b : Approx c)
    → res k ⟪ κ a b ⟫ ≡ κ (resA k a) (resA k b)
  κ-res k a b = κ-uniq (resA k a) (resA k b) _
    ( cong (res k ⟪_⟫) (κ-fix a b)
    ∙ res k .F-seq _ _
    ∙ cong (res k ⟪ σ a ⟫ ⋆ₛ_) (res k .F-seq _ _ ∙ cong (_⋆ₛ res k ⟪ τ b ⟫) (Fₛ-res k (κ a b))))

  Approx≡ : ∀ {c} {a b : Approx c} (p : a .obj ≡ b .obj)
    → PathP (λ i → Stage c [ F ⟅ p i ⟆ , p i ]) (τ a) (τ b) → a ≡ b
  Approx≡ p q i .obj = p i
  Approx≡ {c} {a} {b} p q i .roll =
    q i , isProp→PathP (λ j → isPropIsIso {C = Stage c} (q j)) (a .roll .snd) (b .roll .snd) i

  resA-id : ∀ {c} (a : Approx c) → resA A.id a ≡ a
  resA-id a = Approx≡ refl (res-id (τ a))

  resA-seq : ∀ {c c' c''} (k : A [ c' , c ]) (k' : A [ c'' , c' ]) (a : Approx c)
    → resA k' (resA k a) ≡ resA (k' A.⋆ k) a
  resA-seq k k' a = Approx≡ refl (res-seq k k' (τ a))

  resA-seq' : ∀ {c c' c''} (k : A [ c' , c ]) (k' : A [ c'' , c' ]) {m : A [ c'' , c ]}
    (a : Approx c) → k' A.⋆ k ≡ m → resA k' (resA k a) ≡ resA m a
  resA-seq' k k' a p = Approx≡ refl (res-seq k k' (τ a) ∙ cong (λ x → res x ⟪ τ a ⟫) p)

  module _ {c : A.ob} where
    private
      module S = Category (Stage c)

    transportApprox : (b : Approx c) {G : C.ob} → CatIso (Stage c) G (b .obj) → Approx c
    transportApprox b {G} e .obj = G
    transportApprox b e .roll = ⋆Iso (F-Iso {F = Fₛ c} e) (⋆Iso (b .roll) (invIso e))

    transport-κ : (b b' : Approx c) {G : C.ob} (e : CatIso (Stage c) G (b .obj))
      → τ (transportApprox b' (⋆Iso e (κ-iso b b'))) ≡ τ (transportApprox b e)
    transport-κ b b' e =
      ( cong (_⋆ₛ (τ b' ⋆ₛ (κ b' b ⋆ₛ e .snd .isIso.inv))) (Fₛ c .F-seq _ _)
      ∙ S.⋆Assoc _ _ _
      ∙ cong (Fₛ c ⟪ e .fst ⟫ ⋆ₛ_)
          ( sym (S.⋆Assoc _ _ _)
          ∙ cong (_⋆ₛ (κ b' b ⋆ₛ e .snd .isIso.inv)) (sym (τ-κ b b'))
          ∙ S.⋆Assoc _ _ _
          ∙ cong (τ b ⋆ₛ_) (sym (S.⋆Assoc _ _ _) ∙ cong (_⋆ₛ e .snd .isIso.inv) (κ-inv b b')
                            ∙ S.⋆IdL _)))

  transport-res : ∀ {c c'} (k : A [ c' , c ]) (b : Approx c) {G : C.ob}
    (e : CatIso (Stage c) G (b .obj))
    → τ (resA k (transportApprox b e)) ≡ τ (transportApprox (resA k b) (F-Iso {F = res k} e))
  transport-res k b e =
    res k .F-seq _ _
    ∙ cong₂ _⋆ₛ_ (Fₛ-res k (e .fst)) (res k .F-seq _ _)

  module Construction
    (pws : ∀ z X → EnrichedPower ℰ (ŷ z) X)
    (S : A.ob → Type ℓ') (Sdown : ∀ {z w} → A [ w , z ] → S z → S w)
    (lims : (D : Functor (FullSubcategory A S ^op) C) → EnrichedLimit ℰ D)
    (Ap : ∀ z → S z → Approx z) where
    private
      module Pw (z : A.ob) (X : C.ob) = UniversalElementNotation (pws z X .fst)

      Az : ∀ z → S z → C.ob
      Az z s = Ap z s .obj

      P : ∀ z → S z → C.ob
      P z s = pws z (Az z s) .fst .UniversalElement.vertex

      ev : ∀ z (s : S z) → Stage z [ P z s , Az z s ]
      ev z s = StageLimits.powEvₛ ℰ (pws z (Az z s))

      module _ {W : C.ob} {z : A.ob} (X : C.ob) where
        powIntroₛ : Stage z [ W , X ] → C [ W , pws z X .fst .UniversalElement.vertex ]
        powIntroₛ e = Pw.intro z X (yoneda z ℰ.VE[ W , X ] .Iso.inv e)

        powIntroₛ-β : (e : Stage z [ W , X ])
          → at z ⟪ powIntroₛ e ⟫ ⋆ₛ StageLimits.powEvₛ ℰ (pws z X) ≡ e
        powIntroₛ-β e = (λ i → Pw.β z X {p = yoneda z ℰ.VE[ W , X ] .Iso.inv e} i .N-ob z (lift A.id))
          ∙ res-id e

        pow-extₛ : {f g : C [ W , pws z X .fst .UniversalElement.vertex ]}
          → at z ⟪ f ⟫ ⋆ₛ StageLimits.powEvₛ ℰ (pws z X) ≡ at z ⟪ g ⟫ ⋆ₛ StageLimits.powEvₛ ℰ (pws z X)
          → f ≡ g
        pow-extₛ p = Pw.extensionality z X (isoFunInjective (yoneda z ℰ.VE[ W , X ]) _ _ p)

    module _ {z z' : A.ob} (s : S z) (s' : S z') (k : A [ z' , z ]) where
      tr : C [ P z s , P z' s' ]
      tr = powIntroₛ (Az z' s') (res k ⟪ ev z s ⟫ ⋆ₛ κ (resA k (Ap z s)) (Ap z' s'))

      tr-β : at z' ⟪ tr ⟫ ⋆ₛ ev z' s' ≡ res k ⟪ ev z s ⟫ ⋆ₛ κ (resA k (Ap z s)) (Ap z' s')
      tr-β = powIntroₛ-β (Az z' s') _

    D : Functor (FullSubcategory A S ^op) C
    D .F-ob (z , s) = P z s
    D .F-hom {z , s} {z' , s'} k = tr s s' k
    D .F-id {z , s} = pow-extₛ (Az z s)
      ( tr-β s s A.id
      ∙ cong₂ _⋆ₛ_ (res-id _) (cong (λ x → κ x (Ap z s)) (resA-id _) ∙ κ-id _)
      ∙ Stage z .Category.⋆IdR _
      ∙ sym (cong (_⋆ₛ ev z s) (at z .F-id) ∙ Stage z .Category.⋆IdL _))
    D .F-seq {x , sx} {y , sy} {z , sz} f g = pow-extₛ (Az z sz)
      ( tr-β sx sz (g A.⋆ f)
      ∙ cong₂ _⋆ₛ_ (sym (res-seq f g _))
          (cong (λ a → κ a (Ap z sz)) (sym (resA-seq f g _))
           ∙ sym (κ-comp (resA g (resA f (Ap x sx))) (resA g (Ap y sy)) (Ap z sz)))
      ∙ sym (Stage z .Category.⋆Assoc _ _ _)
      ∙ cong (_⋆ₛ κ (resA g (Ap y sy)) (Ap z sz))
          ( cong (res g ⟪ res f ⟪ ev x sx ⟫ ⟫ ⋆ₛ_) (sym (κ-res g (resA f (Ap x sx)) (Ap y sy)))
          ∙ sym (res g .F-seq _ _)
          ∙ cong (res g ⟪_⟫) (sym (tr-β sx sy f))
          ∙ res g .F-seq _ _
          ∙ cong (_⋆ₛ res g ⟪ ev y sy ⟫) (at-res _ g))
      ∙ Stage z .Category.⋆Assoc _ _ _
      ∙ cong (at z ⟪ tr sx sy f ⟫ ⋆ₛ_) (sym (tr-β sy sz g))
      ∙ sym (Stage z .Category.⋆Assoc _ _ _)
      ∙ cong (_⋆ₛ ev z sz) (sym (at z .F-seq _ _)))

    private
      lm = lims D
      π = lm .fst .UniversalElement.element

    L : C.ob
    L = lm .fst .UniversalElement.vertex

    ε : ∀ y (s : S y) → Stage y [ L , Az y s ]
    ε y s = at y ⟪ π ⟦ y , s ⟧ ⟫ ⋆ₛ ev y s

    πev : ∀ {z} (s : S z) {w} (g : A [ w , z ]) (sw : S w)
      → at w ⟪ π ⟦ z , s ⟧ ⟫ ⋆ₛ (res g ⟪ ev z s ⟫ ⋆ₛ κ (resA g (Ap z s)) (Ap w sw))
        ≡ at w ⟪ π ⟦ w , sw ⟧ ⟫ ⋆ₛ ev w sw
    πev {z} s {w} g sw =
        cong (at w ⟪ π ⟦ z , s ⟧ ⟫ ⋆ₛ_) (sym (tr-β s sw g))
      ∙ sym (Stage w .Category.⋆Assoc _ _ _)
      ∙ cong (_⋆ₛ ev w sw)
          (sym (at w .F-seq _ _) ∙ cong (at w ⟪_⟫) (sym (π .NatTrans.N-hom g) ∙ C.⋆IdL _))

    module _ (y : A.ob) (s : S y) where
      private
        module SL = UniversalElementNotation (StageLimits.stageLimit ℰ lm y)
        module Sy = Category (Stage y)

        ψ : ∀ z (s' : S z) → 𝓟 [ ŷ y ⊗ ŷ z , ℰ.VE[ Az y s , Az z s' ] ]
        ψ z s' .N-ob w (lift g , lift h) = κ (resA g (Ap y s)) (resA h (Ap z s'))
        ψ z s' .N-hom w' w k (lift g , lift h) (lift g' , lift h') e =
          κ-res k _ _
          ∙ (λ i → κ (resA-seq' g k (Ap y s) (cong (λ p → p .fst .lower) e) i)
                     (resA-seq' h k (Ap z s') (cong (λ p → p .snd .lower) e) i))

        module SP (z : A.ob) (s' : S z) = Iso (StageLimits.stagePower ℰ (pws z (Az z s')) y (Az y s))

        coneComp : ∀ z (s' : S z) → Stage y [ Az y s , P z s' ]
        coneComp z s' = SP.inv z s' (ψ z s')

        coneComp-β : ∀ z (s' : S z) w (g : A [ w , y ]) (h : A [ w , z ])
          → res g ⟪ coneComp z s' ⟫ ⋆ₛ res h ⟪ ev z s' ⟫ ≡ κ (resA g (Ap y s)) (resA h (Ap z s'))
        coneComp-β z s' w g h =
          sym (StageLimits.stagePower-β ℰ (pws z (Az z s')) y (Az y s) (coneComp z s') w g h)
          ∙ (λ i → SP.sec z s' (ψ z s') i .N-ob w (lift g , lift h))

        powExt : ∀ {X} {z} {s' : S z} {α β : Stage y [ X , P z s' ]}
          → (∀ w (g : A [ w , y ]) (h : A [ w , z ])
               → res g ⟪ α ⟫ ⋆ₛ res h ⟪ ev z s' ⟫ ≡ res g ⟪ β ⟫ ⋆ₛ res h ⟪ ev z s' ⟫)
          → α ≡ β
        powExt {X} {z} {s'} {α} {β} p =
          isoFunInjective (StageLimits.stagePower ℰ (pws z (Az z s')) y X) α β
            (makePshHomStrictPath (funExt λ w → funExt λ (lift g , lift h) →
              StageLimits.stagePower-β ℰ (pws z (Az z s')) y X α w g h
              ∙ p w g h
              ∙ sym (StageLimits.stagePower-β ℰ (pws z (Az z s')) y X β w g h)))

      εcone : NatTrans (ΔCone ⟅ Az y s ⟆) (at y ∘F D)
      εcone .NatTrans.N-ob (z , s') = coneComp z s'
      εcone .NatTrans.N-hom {z , s'} {z' , s''} k = powExt λ w g h →
          cong (λ m → res g ⟪ m ⟫ ⋆ₛ res h ⟪ ev z' s'' ⟫) (Sy.⋆IdL _)
        ∙ coneComp-β z' s'' w g h
        ∙ sym
          ( cong (_⋆ₛ res h ⟪ ev z' s'' ⟫) (res g .F-seq _ _)
          ∙ Stage w .Category.⋆Assoc _ _ _
          ∙ cong (res g ⟪ coneComp z s' ⟫ ⋆ₛ_)
              ( cong (_⋆ₛ res h ⟪ ev z' s'' ⟫) (at-res _ g ∙ sym (at-res _ h))
              ∙ sym (res h .F-seq _ _)
              ∙ cong (res h ⟪_⟫) (tr-β s' s'' k)
              ∙ res h .F-seq _ _
              ∙ cong₂ _⋆ₛ_ (res-seq k h _) (κ-res h _ _))
          ∙ sym (Stage w .Category.⋆Assoc _ _ _)
          ∙ cong (_⋆ₛ κ (resA h (resA k (Ap z s'))) (resA h (Ap z' s''))) (coneComp-β z s' w g (h A.⋆ k))
          ∙ (λ i → κ (resA g (Ap y s)) (resA (h A.⋆ k) (Ap z s'))
                   ⋆ₛ κ (resA-seq' k h (Ap z s') refl i) (resA h (Ap z' s'')))
          ∙ κ-comp _ _ _)

      εinv : Stage y [ Az y s , L ]
      εinv = SL.intro εcone

      private
        εinv-π : ∀ z (s' : S z) → εinv ⋆ₛ at y ⟪ π ⟦ z , s' ⟧ ⟫ ≡ coneComp z s'
        εinv-π z s' = cong (λ t → t ⟦ z , s' ⟧) SL.β

      εinv-ε : εinv ⋆ₛ ε y s ≡ idₛ
      εinv-ε =
          sym (Sy.⋆Assoc _ _ _)
        ∙ cong (_⋆ₛ ev y s) (εinv-π y s)
        ∙ sym (cong₂ _⋆ₛ_ (res-id _) (res-id _))
        ∙ coneComp-β y s y A.id A.id
        ∙ κ-id _

      chain : ∀ {z} (s' : S z) w (g : A [ w , y ]) (h : A [ w , z ])
        → (at w ⟪ π ⟦ y , s ⟧ ⟫ ⋆ₛ res g ⟪ ev y s ⟫) ⋆ₛ κ (resA g (Ap y s)) (resA h (Ap z s'))
          ≡ at w ⟪ π ⟦ z , s' ⟧ ⟫ ⋆ₛ res h ⟪ ev z s' ⟫
      chain {z} s' w g h =
          cong ((at w ⟪ π ⟦ y , s ⟧ ⟫ ⋆ₛ res g ⟪ ev y s ⟫) ⋆ₛ_)
            (sym (κ-comp (resA g (Ap y s)) (Ap w (Sdown g s)) (resA h (Ap z s'))))
        ∙ sym (Stage w .Category.⋆Assoc _ _ _)
        ∙ cong (_⋆ₛ κ (Ap w (Sdown g s)) (resA h (Ap z s')))
            ( Stage w .Category.⋆Assoc _ _ _
            ∙ πev s g (Sdown g s)
            ∙ sym (πev s' h (Sdown g s))
            ∙ sym (Stage w .Category.⋆Assoc _ _ _))
        ∙ Stage w .Category.⋆Assoc _ _ _
        ∙ cong ((at w ⟪ π ⟦ z , s' ⟧ ⟫ ⋆ₛ res h ⟪ ev z s' ⟫) ⋆ₛ_)
            (κ-inv (resA h (Ap z s')) (Ap w (Sdown g s)))
        ∙ Stage w .Category.⋆IdR _

      ε-εinv : ε y s ⋆ₛ εinv ≡ idₛ
      ε-εinv = SL.extensionality (makeNatTransPath (funExt λ (z , s') →
          Sy.⋆Assoc _ _ _
        ∙ cong (ε y s ⋆ₛ_) (εinv-π z s')
        ∙ powExt (λ w g h →
              cong (_⋆ₛ res h ⟪ ev z s' ⟫) (res g .F-seq _ _)
            ∙ Stage w .Category.⋆Assoc _ _ _
            ∙ cong (res g ⟪ ε y s ⟫ ⋆ₛ_) (coneComp-β z s' w g h)
            ∙ cong (_⋆ₛ κ (resA g (Ap y s)) (resA h (Ap z s')))
                (res g .F-seq _ _ ∙ cong (_⋆ₛ res g ⟪ ev y s ⟫) (at-res _ g))
            ∙ chain s' w g h
            ∙ cong (_⋆ₛ res h ⟪ ev z s' ⟫) (sym (at-res _ g)))
        ∙ sym (Sy.⋆IdL _)))

      εIso : CatIso (Stage y) L (Az y s)
      εIso = ε y s , isiso εinv εinv-ε ε-εinv

    approxL : ∀ y (s : S y) → Approx y
    approxL y s = transportApprox (Ap y s) (εIso y s)

    ε-res : ∀ {y y'} (s : S y) (s' : S y') (k : A [ y' , y ])
      → res k ⟪ ε y s ⟫ ⋆ₛ κ (resA k (Ap y s)) (Ap y' s') ≡ ε y' s'
    ε-res {y} {y'} s s' k =
        cong (_⋆ₛ κ (resA k (Ap y s)) (Ap y' s'))
          (res k .F-seq _ _ ∙ cong (_⋆ₛ res k ⟪ ev y s ⟫) (at-res _ k))
      ∙ Stage y' .Category.⋆Assoc _ _ _
      ∙ πev s k s'

    approxL-res : ∀ {y y'} (s : S y) (s' : S y') (k : A [ y' , y ])
      → resA k (approxL y s) ≡ approxL y' s'
    approxL-res {y} {y'} s s' k = Approx≡ refl
      ( transport-res k (Ap y s) (εIso y s)
      ∙ sym (transport-κ (resA k (Ap y s)) (Ap y' s') (F-Iso {F = res k} (εIso y s)))
      ∙ cong (λ e → τ (transportApprox (Ap y' s') e)) (CatIso≡ _ _ (ε-res s s' k)))

  module _ (pws : ∀ z X → EnrichedPower ℰ (ŷ z) X)
    (lims : ∀ (S : A.ob → Type ℓ') (D : Functor (FullSubcategory A S ^op) C) → EnrichedLimit ℰ D) where

    module Step (c : A.ob) (IH : ∀ z → z ≺ c → Approx z) where
      open Construction pws (λ z → z ≺ c) ≺-precomp (lims _) IH

      ▷roll : CatIso (▷S.Stage c) (F ⟅ L ⟆) L
      ▷roll .fst .N-ob y (g , q) = τ (approxL y q)
      ▷roll .fst .N-hom y' y k (g , q) (g' , q') e = cong τ (approxL-res q q' k)
      ▷roll .snd .isIso.inv .N-ob y (g , q) = σ (approxL y q)
      ▷roll .snd .isIso.inv .N-hom y' y k (g , q) (g' , q') e = cong σ (approxL-res q q' k)
      ▷roll .snd .isIso.sec = makePshHomStrictPath (funExt λ y → funExt λ (g , q) → στ (approxL y q))
      ▷roll .snd .isIso.ret = makePshHomStrictPath (funExt λ y → funExt λ (g , q) → τσ (approxL y q))

      step : Approx c
      step .obj = F ⟅ L ⟆
      step .roll = F-Iso {F = F▷ₛ c} ▷roll

    approx : ∀ c → Approx c
    approx = WFI.induction wf≺ Step.step

    private
      module Fix = Construction pws (λ _ → Unit*) (λ _ _ → tt*) (lims _) (λ z _ → approx z)

    fix : C.ob
    fix = Fix.L

    fixIso : CatIso C (F ⟅ fix ⟆) fix
    fixIso = glueIso (λ c → Fix.approxL c tt* .roll)
      (λ k → cong τ (Fix.approxL-res tt* tt* k))
      (λ k → cong σ (Fix.approxL-res tt* tt* k))

    private
      in-fix = fixIso .fst
      out-fix = fixIso .snd .isIso.inv

    initialAlgebra : InitialAlgebra F
    initialAlgebra = terminalToUniversalElement {C = ALG F ^op}
      ((fix , in-fix) , λ (B , b) → contr B b)
      where
      contr : ∀ B b → isContr (Σ[ h ∈ C [ fix , B ] ] (in-fix C.⋆ h ≡ F ⟪ h ⟫ C.⋆ b))
      contr B b = (H.hylo , fold H.hylo H.hylo-eq)
        , λ (h , p) → Σ≡Prop (λ _ → C.isSetHom _ _) (sym (H.hylo-uniq h (unfold h p)))
        where
        module H = Hylo pshGuarded {F = F} lc out-fix b
        fold : ∀ h → h ≡ out-fix C.⋆ (F ⟪ h ⟫ C.⋆ b) → in-fix C.⋆ h ≡ F ⟪ h ⟫ C.⋆ b
        fold h p = cong (in-fix C.⋆_) p ∙ sym (C.⋆Assoc _ _ _)
          ∙ cong (C._⋆ (F ⟪ h ⟫ C.⋆ b)) (fixIso .snd .isIso.ret) ∙ C.⋆IdL _
        unfold : ∀ h → in-fix C.⋆ h ≡ F ⟪ h ⟫ C.⋆ b → h ≡ out-fix C.⋆ (F ⟪ h ⟫ C.⋆ b)
        unfold h p = sym (C.⋆IdL h) ∙ cong (C._⋆ h) (sym (fixIso .snd .isIso.sec))
          ∙ C.⋆Assoc _ _ _ ∙ cong (out-fix C.⋆_) p

    terminalCoalgebra : TerminalCoalgebra F
    terminalCoalgebra = terminalToUniversalElement {C = ALG (F ^opF) ^op}
      ((fix , out-fix) , λ (B , c) → contr B c)
      where
      contr : ∀ B c → isContr (Σ[ h ∈ C [ B , fix ] ] (h C.⋆ out-fix ≡ c C.⋆ F ⟪ h ⟫))
      contr B c = (H.hylo , fold H.hylo H.hylo-eq)
        , λ (h , p) → Σ≡Prop (λ _ → C.isSetHom _ _) (sym (H.hylo-uniq h (unfold h p)))
        where
        module H = Hylo pshGuarded {F = F} lc c in-fix
        fold : ∀ h → h ≡ c C.⋆ (F ⟪ h ⟫ C.⋆ in-fix) → h C.⋆ out-fix ≡ c C.⋆ F ⟪ h ⟫
        fold h p = cong (C._⋆ out-fix) p ∙ C.⋆Assoc _ _ _
          ∙ cong (c C.⋆_) (C.⋆Assoc _ _ _ ∙ cong (F ⟪ h ⟫ C.⋆_) (fixIso .snd .isIso.ret) ∙ C.⋆IdR _)
        unfold : ∀ h → h C.⋆ out-fix ≡ c C.⋆ F ⟪ h ⟫ → h ≡ c C.⋆ (F ⟪ h ⟫ C.⋆ in-fix)
        unfold h p = sym (C.⋆IdR h) ∙ cong (h C.⋆_) (sym (fixIso .snd .isIso.sec))
          ∙ sym (C.⋆Assoc _ _ _) ∙ cong (C._⋆ in-fix) p ∙ C.⋆Assoc _ _ _
