module Cubical.Categories.Instances.FinCard.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function as Func
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.SumFin
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
open import Cubical.Data.FinSet
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as ⊥

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Adjoint
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Instances.FinCard.Base
open import Cubical.Categories.Instances.FinOrd.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Instances.Democratic

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.Terminal renaming (preservesTerminal to secPreservesTerminal)
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category
open Functor
open AdjointEquivalence
open UnitCounit
open TriangleIdentities
open UniversalElement
open CartesianCategory
open Section
open UniversalElementᴰ
open PshHom
open PshIso
open PshSection
open isIsoOver

module _ ℓ where
  FINCARD→FINORD : Functor FINCARD (FINORD ℓ)
  FINCARD→FINORD .F-ob n =
    mkfo
      (Lift $ Fin n)
      (n , isoToEquiv (iso lower lift (λ _ → refl) (λ _ → refl)))
  FINCARD→FINORD .F-hom f .fst (lift m) = lift (f m)
  FINCARD→FINORD .F-hom f .snd = _
  FINCARD→FINORD .F-id = refl
  FINCARD→FINORD .F-seq _ _ = refl

  FINORD→FINCARD : Functor (FINORD ℓ) FINCARD
  FINORD→FINCARD .F-ob = cardfo
  FINORD→FINCARD .F-hom {x = A} {y = B} (f , _) m =
    B .snd .snd .fst (f (A .snd .snd .snd .equiv-proof m .fst .fst))
  FINORD→FINCARD .F-id {x = A} =
    funExt λ m → A .snd .snd .snd .equiv-proof m .fst .snd
  FINORD→FINCARD .F-seq {x = A} {y = B} {z = C} f g =
    funExt λ m →
      cong (λ z → C .snd .snd .fst (g .fst z))
        (λ i → B .snd .snd .snd .equiv-proof
          (B .snd .snd .fst
            (f .fst (A .snd .snd .snd .equiv-proof m .fst .fst)))
            .snd (f .fst (A .snd .snd .snd .equiv-proof m .fst .fst) , refl)
            (~ i) .fst)

  FINCARD≅FINORD : AdjointEquivalence FINCARD (FINORD ℓ)
  FINCARD≅FINORD .fun = FINCARD→FINORD
  FINCARD≅FINORD .inv = FINORD→FINCARD
  FINCARD≅FINORD .η .NatIso.trans .NatTrans.N-ob = λ _ z → z
  FINCARD≅FINORD .η .NatIso.trans .NatTrans.N-hom _ = refl
  FINCARD≅FINORD .η .NatIso.nIso n .isIso.inv = λ z → z
  FINCARD≅FINORD .η .NatIso.nIso n .isIso.sec = refl
  FINCARD≅FINORD .η .NatIso.nIso n .isIso.ret = refl
  FINCARD≅FINORD .ε .NatIso.trans .NatTrans.N-ob =
    λ x → (λ z → x .snd .snd .snd .equiv-proof (z .lower) .fst .fst) , tt
  FINCARD≅FINORD .ε .NatIso.trans .NatTrans.N-hom {x = A} {y = B} f =
    Σ≡Prop (λ _ → isPropUnit)
      (funExt λ x →
        λ i → B .snd .snd .snd .equiv-proof
          (B .snd .snd .fst
            (f .fst (A .snd .snd .snd .equiv-proof (x .lower) .fst .fst)))
          .snd ((f .fst (A .snd .snd .snd .equiv-proof (x .lower) .fst .fst)) ,
            refl) i .fst)
  FINCARD≅FINORD .ε .NatIso.nIso A .isIso.inv =
    (λ z → lift (A .snd .snd .fst z)) , tt
  FINCARD≅FINORD .ε .NatIso.nIso A .isIso.sec =
    Σ≡Prop (λ _ → isPropUnit) (funExt λ x → λ i →
      A .snd .snd .snd .equiv-proof (A .snd .snd .fst x) .snd (x , refl) i .fst)
  FINCARD≅FINORD .ε .NatIso.nIso A .isIso.ret =
    Σ≡Prop (λ _ → isPropUnit) (funExt λ (lift x) →
      cong lift (A .snd .snd .snd .equiv-proof x .fst .snd))
  FINCARD≅FINORD .triangleIdentities .Δ₁ _ = refl
  FINCARD≅FINORD .triangleIdentities .Δ₂ A =
    funExt λ x → A .snd .snd .snd .equiv-proof x .fst .snd

  TerminalFINCARD : Terminal' FINCARD
  TerminalFINCARD .vertex = 1
  TerminalFINCARD .element = _
  TerminalFINCARD .universal _ .equiv-proof _ .fst .fst _ = fzero
  TerminalFINCARD .universal _ .equiv-proof _ .fst .snd = refl
  TerminalFINCARD .universal _ .equiv-proof _ .snd (u , v) =
    Σ≡Prop (λ _ _ _ → refl) (funExt λ _ → isContrSumFin1 .snd (u _))

  InitialFINCARD : Initial FINCARD
  InitialFINCARD .vertex = 0
  InitialFINCARD .element = _
  InitialFINCARD .universal _ .equiv-proof _ .fst .fst ()
  InitialFINCARD .universal _ .equiv-proof _ .fst .snd = refl
  InitialFINCARD .universal _ .equiv-proof _ .snd (u , v) =
    Σ≡Prop (λ _ _ _ → refl) (funExt λ ())

  BinProductsFINCARD : BinProducts FINCARD
  BinProductsFINCARD (n , m) .vertex = n · m
  BinProductsFINCARD (n , m) .element .fst l =
    SumFin×≃ n m .snd .equiv-proof l .fst .fst .fst
  BinProductsFINCARD (n , m) .element .snd l =
    SumFin×≃ n m .snd .equiv-proof l .fst .fst .snd
  BinProductsFINCARD (n , m) .universal l .equiv-proof (f , g) .fst .fst k =
    SumFin×≃ n m .fst (f k , g k)
  BinProductsFINCARD (n , m) .universal l .equiv-proof (f , g) .fst .snd =
    ≡-×
      (funExt λ k → λ i →
        SumFin×≃ n m .snd .equiv-proof
          (SumFin×≃ n m .fst (f k , g k)) .snd ((f k , g k) , refl) i .fst .fst)
      (funExt λ k → λ i →
        SumFin×≃ n m .snd .equiv-proof
          (SumFin×≃ n m .fst (f k , g k)) .snd ((f k , g k) , refl) i .fst .snd)
  BinProductsFINCARD (n , m) .universal l .equiv-proof (f , g) .snd (u , v) =
    Σ≡Prop (λ _ → isSet× (isSet→ isSetFin) (isSet→ isSetFin) _ (f , g))
      (funExt λ k →
        cong (SumFin×≃ n m .fst) (λ i → (v (~ i) .fst k) , (v (~ i) .snd k))
        ∙ SumFin×≃ n m .snd .equiv-proof (u k) .fst .snd)

  -- Want this to be m + n instead of n + m so that the eliminator
  -- below aligns
  -- That is, the rec case of elimS-F-ob really should
  -- definitionally be a simple recursive call. However, if we use n + m here,
  -- then elimS-F-ob will need a transport or J-eliminator
  BinCoproductsFINCARD : BinCoproducts FINCARD
  BinCoproductsFINCARD (n , m) .vertex = m + n
  BinCoproductsFINCARD (n , m) .element .fst l =
    SumFin⊎≃ m n .fst (inr l)
  BinCoproductsFINCARD (n , m) .element .snd l =
    SumFin⊎≃ m n .fst (inl l)
  BinCoproductsFINCARD (n , m) .universal l .equiv-proof (f , g) .fst .fst k =
    Sum.elim g f (SumFin⊎≃ m n .snd .equiv-proof k .fst .fst)
  BinCoproductsFINCARD (n , m) .universal l .equiv-proof (f , g) .fst .snd =
    ≡-×
      (funExt λ k →
        cong (Sum.elim g f)
          (λ i → SumFin⊎≃ m n .snd .equiv-proof
            (SumFin⊎≃ m n .fst (inr k)) .snd ((inr k) , refl) i .fst))
      (funExt λ k →
        cong (Sum.elim g f)
          (λ i → SumFin⊎≃ m n .snd .equiv-proof
            (SumFin⊎≃ m n .fst (inl k)) .snd ((inl k) , refl) i .fst))
  BinCoproductsFINCARD (n , m) .universal l .equiv-proof (f , g) .snd (u , v) =
    Σ≡Prop (λ _ → isSet× (isSet→ isSetFin) (isSet→ isSetFin) _ (f , g))
      (funExt λ k →
        Sum.elim {C = λ z → Sum.elim g f z ≡ u (SumFin⊎≃ m n .fst z)}
          (λ km → λ i → v (~ i) .snd km)
          (λ kn → λ i → v (~ i) .fst kn)
          (SumFin⊎≃ m n .snd .equiv-proof k .fst .fst)
        ∙ cong u (SumFin⊎≃ m n .snd .equiv-proof k .fst .snd )
      )

  FINCARDCartesianCategory : CartesianCategory _ _
  FINCARDCartesianCategory .C = FINCARD
  FINCARDCartesianCategory .term = TerminalFINCARD
  FINCARDCartesianCategory .bp = BinProductsFINCARD

  FINCARD^opCartesianCategory : CartesianCategory _ _
  FINCARD^opCartesianCategory .C = FINCARD^op
  FINCARD^opCartesianCategory .term = InitialFINCARD
  FINCARD^opCartesianCategory .bp = BinCoproductsFINCARD

  FINCARDSCwF : SCwF _ _ _ _
  FINCARDSCwF = CartesianCategory→SCwF FINCARDCartesianCategory

  FINCARD^opTmPsh : Presheaf FINCARD^op ℓ-zero
  FINCARD^opTmPsh .F-ob Γ = Fin Γ , isSetFin
  FINCARD^opTmPsh .F-hom = λ f → f
  FINCARD^opTmPsh .F-id = refl
  FINCARD^opTmPsh .F-seq = λ _ _ → refl

  FINCARD^opTmPshIso :
    PshIso (FINCARD^op [-, 1 ]) FINCARD^opTmPsh
  FINCARD^opTmPshIso .trans .N-ob _ f = f fzero
  FINCARD^opTmPshIso .trans .N-hom _ _ _ _ = refl
  FINCARD^opTmPshIso .nIso _ =
    (λ z _ → z) ,
    (λ _ → refl) ,
    λ f → funExt λ where fzero → refl

  FINCARD^opTmPshIso× : ∀ Γ →
    PshIso
      ((FINCARD^op [-, Γ ]) ×Psh (FINCARD^op [-, 1 ]))
      ((FINCARD^op [-, Γ ]) ×Psh FINCARD^opTmPsh)
  FINCARD^opTmPshIso× Γ = ×PshIso idPshIso FINCARD^opTmPshIso

  FINCARD^opSCwF : SCwF _ _ _ _
  FINCARD^opSCwF .fst = FINCARD^op
  FINCARD^opSCwF .snd .fst = Unit
  FINCARD^opSCwF .snd .snd .fst _ = FINCARD^opTmPsh
  FINCARD^opSCwF .snd .snd .snd .fst = InitialFINCARD
  FINCARD^opSCwF .snd .snd .snd .snd _ Γ =
    BinCoproductsFINCARD (Γ , 1) ◁PshIso FINCARD^opTmPshIso× Γ

  module isFreeSCwFFINCARD^op {ℓC ℓC' ℓSᴰ ℓSᴰ'} (Sᴰ : SCwFᴰ FINCARD^opSCwF ℓC ℓC' ℓSᴰ ℓSᴰ') where
    private
      module Sᴰ = SCwFᴰNotation Sᴰ
      ∫Sᴰ = ∫C Sᴰ.Cᴰ
      module ∫Sᴰ = Category ∫Sᴰ
      module FINCARD^op = SCwFNotation FINCARD^opSCwF
      module C = Category FINCARD^op.C
      module ∫Tmᴰ {A}{Aᴰ : Sᴰ.Tyᴰ A} = PresheafNotation (∫P (Sᴰ.Tmᴰ Aᴰ))

    open TerminalNotation InitialFINCARD
    open TerminalᴰNotation _ Sᴰ.termᴰ

    module _ {n m} {f : FINCARD^op [ n , suc m ]} where
      private
        module 1,m = UniversalElementNotation (FINCARD^op.ext tt m)
      suc-sole-lem : 1,m.intro (f Func.∘ inr , f fzero) ≡ f
      suc-sole-lem = 1,m.intro≡ refl

    module _ (elimTy : (A : FINCARD^op.Ty) → Sᴰ.Tyᴰ A) where
      elimS-F-ob : ∀ n → Sᴰ.Cᴰ.ob[ n ]
      elimS-F-ob zero = 𝟙ᴰ
      elimS-F-ob (suc n) =
        Sᴰ.extᴰ.vertexᴰ {Γᴰ = elimS-F-ob n}{Aᴰ = elimTy tt}

      elimTm : ∀ {Γ A} (M : Γ FINCARD^op.⊢ A ) → elimS-F-ob Γ Sᴰ.[ M ]⊢ᴰ elimTy A
      elimTm {suc Γ} {_} fzero = Sᴰ.extᴰ.elementᴰ .snd
      elimTm {suc Γ} {_} (fsuc M) =
        Sᴰ.extᴰ.elementᴰ .fst Sᴰ.Tmᴰ.⋆ᴰ elimTm M

      elimSubst : ∀ {Δ Γ} (γ : C.Hom[ Δ , Γ ]) →
        Sᴰ.Cᴰ [ γ ][ elimS-F-ob Δ , elimS-F-ob Γ ]
      elimSubst {Δ} {zero} γ =
        Sᴰ.Cᴰ.reind 𝟙extensionality $ !tᴰ (elimS-F-ob Δ)
      elimSubst {Δ} {suc Γ} γ =
        Sᴰ.Cᴰ.reind suc-sole-lem $
          Sᴰ.extᴰ.introᴰ ((elimSubst (γ Func.∘ fsuc)) , (elimTm (γ fzero)))

      elimSubst-fsuc : ∀ {Δ Γ} (γ : C.Hom[ Δ , Γ ]) →
        Path (∫Sᴰ [ _ , _ ])
          (_ , elimSubst (fsuc Func.∘ γ))
          (_ , (Sᴰ.extᴰ.elementᴰ .fst Sᴰ.Cᴰ.⋆ᴰ elimSubst γ))
      elimSubst-fsuc {Γ = zero} γ = 𝟙extensionalityᴰ
      elimSubst-fsuc {Γ = suc Γ} γ =
        (sym $ Sᴰ.Cᴰ.reind-filler _ _)
         ∙ Sᴰ.extᴰ.introᴰ≡
             (ΣPathPᴰ
               (elimSubst-fsuc (γ Func.∘ fsuc)
               ∙ Sᴰ.Cᴰ.⟨
                   refl
                 ⟩⋆⟨
                   (sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .fst)
                   ∙ Sᴰ.Cᴰ.⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
                 ⟩
               ∙ (sym $ Sᴰ.Cᴰ.⋆Assoc _ _ _)
               )
               (Sᴰ.Tmᴰ.⟨⟩⋆⟨ sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .snd ⟩
               ∙ (sym $ Sᴰ.Tmᴰ.⋆Assoc _ _ _)
               ∙ Sᴰ.Tmᴰ.⟨ Sᴰ.Cᴰ.⟨⟩⋆⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩ ⟩⋆⟨⟩))

      elimSubst-id : ∀ Γ →
        Path (∫Sᴰ [ (Γ , elimS-F-ob Γ) , _ ])
          (_ , elimSubst λ z → z)
          (_ , Sᴰ.Cᴰ.idᴰ)
      elimSubst-id zero = Sᴰ.termᴰ.extensionalityᴰ refl
      elimSubst-id (suc Γ) =
        (sym $ Sᴰ.Cᴰ.reind-filler _ _)
        ∙ Sᴰ.extᴰ.introᴰ≡
            (ΣPathPᴰ
              (elimSubst-fsuc (λ z → z)
              ∙ Sᴰ.Cᴰ.⟨⟩⋆⟨ elimSubst-id Γ ⟩
              ∙ Sᴰ.Cᴰ.⋆IdR _
              ∙ (sym $ Sᴰ.Cᴰ.⋆IdL _))
              (sym $ Sᴰ.Tmᴰ.⋆IdL _))

      elimSubst-Tm : ∀ {Δ Γ A} →
        (γ : C.Hom[ Δ , Γ ]) →
        (M : Γ FINCARD^op.⊢ A) →
        Path (∫Tmᴰ.p[ _ ])
          (_ , elimTm (γ M))
          (_ , (elimSubst γ Sᴰ.Tmᴰ.⋆ᴰ elimTm M))
      elimSubst-Tm {Γ = suc Γ} γ fzero =
        (sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .snd)
        ∙ Sᴰ.Tmᴰ.⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
      elimSubst-Tm {Γ = suc Γ} γ (fsuc M) =
        elimSubst-Tm (γ Func.∘ fsuc) M
        ∙ Sᴰ.Tmᴰ.⟨ sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .fst ⟩⋆⟨⟩
        ∙ Sᴰ.Tmᴰ.⋆Assoc _ _ _
        ∙ Sᴰ.Tmᴰ.⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩⋆⟨⟩

      elimSubst-seq : ∀ {Θ Δ Γ} →
        {δ : C.Hom[ Θ , Δ ]} →
        (γ : C.Hom[ Δ , Γ ]) →
        Path (∫Sᴰ [ _ , _ ])
          (_ , elimSubst (δ C.⋆ γ))
          (_ , (elimSubst δ Sᴰ.Cᴰ.⋆ᴰ elimSubst γ))
      elimSubst-seq {Γ = zero} γ = 𝟙extensionalityᴰ
      elimSubst-seq {Γ = suc Γ} γ =
        (sym $ Sᴰ.Cᴰ.reind-filler _ _)
        ∙ Sᴰ.extᴰ.introᴰ≡
            (ΣPathPᴰ
              (elimSubst-seq (γ Func.∘ fsuc)
              ∙ Sᴰ.Cᴰ.⟨⟩⋆⟨ (sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .fst)
                            ∙ Sᴰ.Cᴰ.⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩⋆⟨⟩ ⟩
              ∙ (sym $ Sᴰ.Cᴰ.⋆Assoc _ _ _))
              (elimSubst-Tm _ _
              ∙ Sᴰ.Tmᴰ.⟨⟩⋆⟨ sym $ PathPᴰΣ Sᴰ.extᴰ.βᴰ .snd ⟩
              ∙ Sᴰ.Tmᴰ.⟨⟩⋆⟨ Sᴰ.Tmᴰ.⟨ Sᴰ.Cᴰ.reind-filler _ _ ⟩⋆⟨⟩ ⟩
              ∙ (sym $ Sᴰ.Tmᴰ.⋆Assoc _ _ _ )))

      elimSection : GlobalSection Sᴰ.Cᴰ
      elimSection .F-obᴰ = elimS-F-ob
      elimSection .F-homᴰ = elimSubst
      elimSection .F-idᴰ = Sᴰ.Cᴰ.rectify $ Sᴰ.Cᴰ.≡out $ elimSubst-id _
      elimSection .F-seqᴰ δ γ =
        Sᴰ.Cᴰ.rectify $ Sᴰ.Cᴰ.≡out $ elimSubst-seq {δ = δ} γ

      elimPshSection :
        (A : FINCARD^op.Ty) →
        PshSection elimSection (Sᴰ.Tmᴰ $ elimTy A)
      elimPshSection _ .N-ob = elimTm
      elimPshSection _ .N-hom γ M =
        Sᴰ.Tmᴰ.rectify $ Sᴰ.Tmᴰ.≡out $ elimSubst-Tm γ M

      elimFINCARD^opStrict : StrictSection FINCARD^opSCwF Sᴰ
      elimFINCARD^opStrict .fst = elimSection
      elimFINCARD^opStrict .snd .fst = elimTy
      elimFINCARD^opStrict .snd .snd .fst = elimPshSection
      elimFINCARD^opStrict .snd .snd .snd .fst = refl
      elimFINCARD^opStrict .snd .snd .snd .snd _ Γ =
        ΣPathP (
          refl ,
          (ΣPathP (
            (Sᴰ.Cᴰ.rectify $ Sᴰ.Cᴰ.≡out $
              elimSubst-fsuc _
              ∙ Sᴰ.Cᴰ.⟨⟩⋆⟨ elimSubst-id Γ ⟩
              ∙ Sᴰ.Cᴰ.⋆IdR _) ,
            refl)))


  -- TODO need StrictSection → SCwFSection
  -- isFreeSCwFFINCARD^op : isFreeSCwF FINCARD^opSCwF
  -- isFreeSCwFFINCARD^op Sᴰ = {!!}
