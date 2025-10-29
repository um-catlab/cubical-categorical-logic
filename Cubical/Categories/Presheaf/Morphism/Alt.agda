{- This is intended to replace Presheaf.Morphism upstream -}
module Cubical.Categories.Presheaf.Morphism.Alt where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.More
-- open import Cubical.Foundations.Transport hiding (pathToIso)
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Isomorphism.More
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Structure

-- open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Reflection.RecordEquiv.More
-- open import Cubical.Data.Sigma
-- import Cubical.Data.Equality as Eq

-- open import Cubical.Categories.Category renaming (isIso to isIsoC)
-- open import Cubical.Categories.Constructions.Elements
-- open import Cubical.Categories.Constructions.Lift
-- open import Cubical.Categories.Functor
-- open import Cubical.Categories.Instances.Functors
-- open import Cubical.Categories.Instances.Sets
-- open import Cubical.Categories.Instances.Sets.More
-- open import Cubical.Categories.Limits
-- import Cubical.Categories.LocallySmall.Base
--   as LocallySmall renaming (isIso to isIsoLSC)
-- open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
-- open import Cubical.Categories.Presheaf.Base
-- open import Cubical.Categories.Presheaf.More
-- open import Cubical.Categories.Presheaf.Representable
-- open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
-- open import Cubical.Categories.Profunctor.General

-- {-

--   Given two presheaves P and Q on the same category C, a morphism
--   between them is a natural transformation. Here we generalize this to
--   situations where P and Q are presheaves on *different*
--   categories. This is equivalent to the notion of morphism of
--   fibrations if viewing P and Q as discrete fibrations.

--   Given a functor F : C → D, a presheaf P on C and a presheaf Q on D,
--   we can define a homomorphism from P to Q over F as a natural
--   transformation from P to Q o F^op. (if we had implicit cumulativity)

--   These are the homs of a 2-category of presheaves displayed over the
--   2-category of categories.

-- -}
-- private
--   variable
--     ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr ℓs : Level

-- open Category
-- open Contravariant
-- open Functor
-- open isUnivalent
-- open UniversalElement

-- module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
--   private
--     module C = Category C
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q

--   PshHomΣ : Type _
--   PshHomΣ = Σ[ α ∈ (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) ]
--     (∀ x y (f : C [ x , y ]) (p : P.p[ y ]) →
--      α x (f P.⋆ p) ≡ (f Q.⋆ α y p))

--   isPropN-hom : ∀ (α : (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ])) →
--     isProp (∀ x y (f : C [ x , y ]) (p : P.p[ y ])→
--      α x (f P.⋆ p) ≡ (f Q.⋆ α y p))
--   isPropN-hom =
--     λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Q.isSetPsh _ _

--   isSetPshHomΣ : isSet PshHomΣ
--   isSetPshHomΣ =
--     isSetΣ (isSetΠ (λ _ → isSet→ Q.isSetPsh)) λ _ → isProp→isSet (isPropN-hom _)

--   -- Natural transformation between presheaves of different levels
--   record PshHom : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
--     no-eta-equality
--     constructor pshhom
--     field
--       N-ob : ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]
--       N-hom : ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
--         N-ob c (f P.⋆ p) ≡ (f Q.⋆ N-ob c' p)

--   PshHomΣIso : Iso PshHom PshHomΣ
--   unquoteDef PshHomΣIso = defineRecordIsoΣ PshHomΣIso (quote (PshHom))

--   isSetPshHom : isSet PshHom
--   isSetPshHom = isOfHLevelRetractFromIso 2 PshHomΣIso isSetPshHomΣ

-- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓp}
--   where
--   private
--     module C = Category C
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--   NatTrans→PshHom : NatTrans P Q → PshHom P Q
--   NatTrans→PshHom α .PshHom.N-ob = α .NatTrans.N-ob
--   NatTrans→PshHom α .PshHom.N-hom x y f = funExt⁻ (α .NatTrans.N-hom f)

--   PshHom→NatTrans : PshHom P Q → NatTrans P Q
--   PshHom→NatTrans α .NatTrans.N-ob = α .PshHom.N-ob
--   PshHom→NatTrans α .NatTrans.N-hom f = funExt (α .PshHom.N-hom _ _ f)

-- open PshHom
-- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
--   private
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--   makePshHomΣPath : ∀ {α β : PshHomΣ P Q} → α .fst ≡ β .fst
--    → α ≡ β
--   makePshHomΣPath = ΣPathPProp (isPropN-hom P Q)

--   makePshHomPath : ∀ {α β : PshHom P Q} → α .N-ob ≡ β .N-ob
--    → α ≡ β
--   makePshHomPath {α} {β} N-ob≡ =
--     isoFunInjective (PshHomΣIso P Q) α β (makePshHomΣPath N-ob≡)

-- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where
--   idPshHom : PshHom P P
--   idPshHom .N-ob x z = z
--   idPshHom .N-hom x y f p = refl

-- module _ {C : Category ℓc ℓc'} where
--   module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} (α : PshHom P Q) (β : PshHom Q R) where
--     private
--       module P = PresheafNotation P
--       module R = PresheafNotation R
--     opaque
--       ⋆PshHom-N-hom : ∀ x y (f : C [ x , y ]) (p : P.p[ y ])
--         → β .N-ob x (α .N-ob x (f P.⋆ p)) ≡ f R.⋆ β .N-ob y (α .N-ob y p)
--       ⋆PshHom-N-hom x y f p =
--         cong (β .N-ob _) (α .N-hom x y f p)
--         ∙ β .N-hom x y f (α .N-ob y p)

--     _⋆PshHom_ : PshHom P R
--     _⋆PshHom_ .N-ob x p = β .N-ob x (α .N-ob x p)
--     _⋆PshHom_ .N-hom = ⋆PshHom-N-hom

--   _⋆PshHomNatTrans_ :
--     ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓq} →
--       PshHom P Q → NatTrans Q R → PshHom P R
--   α ⋆PshHomNatTrans β = α ⋆PshHom NatTrans→PshHom β
--   _⋆NatTransPshHom_ :
--     ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓp}{R : Presheaf C ℓr} →
--       NatTrans P Q → PshHom Q R → PshHom P R
--   α ⋆NatTransPshHom β = NatTrans→PshHom α ⋆PshHom β

-- -- TODO:
-- --   should be able to rewrite this as LocallySmallNatTransᴰ
-- -- PRESHEAF : ∀ (C : Category ℓc ℓc')
-- --   → LocallySmallCategory (Σω[ (liftω ℓP) ∈ Liftω Level ] Liftω (Presheaf C ℓP))
-- -- PRESHEAF C .LocallySmallCategory.Hom-ℓ = _
-- -- PRESHEAF C .LocallySmallCategory.Hom[_,_] (_ , (liftω P)) (_ , (liftω Q)) = PshHom P Q
-- -- PRESHEAF C .LocallySmallCategory.id = idPshHom
-- -- PRESHEAF C .LocallySmallCategory._⋆_ = _⋆PshHom_
-- -- PRESHEAF C .LocallySmallCategory.⋆IdL = λ _ → makePshHomPath refl
-- -- PRESHEAF C .LocallySmallCategory.⋆IdR = λ _ → makePshHomPath refl
-- -- PRESHEAF C .LocallySmallCategory.⋆Assoc = λ _ _ _ → makePshHomPath refl
-- -- PRESHEAF C .LocallySmallCategory.isSetHom = isSetPshHom _ _

-- -- module _ {C : Category ℓc ℓc'} where
-- --   PshHomPsh :
-- --     ∀ (Q : Presheaf C ℓq) →
-- --       Presheaf (PresheafCategory C ℓp) (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓq) ℓp)
-- --   PshHomPsh Q .F-ob P = (PshHom P Q) , (isSetPshHom _ _)
-- --   PshHomPsh Q .F-hom α β = α ⋆NatTransPshHom β
-- --   PshHomPsh Q .F-id = funExt (λ _ → makePshHomPath refl)
-- --   PshHomPsh Q .F-seq α α' = funExt λ _ → makePshHomPath refl

-- --   PshHomProf :
-- --     Profunctor
-- --       (PresheafCategory C ℓq)
-- --       (PresheafCategory C ℓp)
-- --       (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
-- --   PshHomProf .F-ob Q = PshHomPsh Q
-- --   PshHomProf .F-hom β .NatTrans.N-ob P α = α ⋆PshHomNatTrans β
-- --   PshHomProf .F-hom β .NatTrans.N-hom α = funExt λ _ → makePshHomPath refl
-- --   PshHomProf .F-id =
-- --     makeNatTransPath (funExt (λ _ → funExt λ _ → makePshHomPath refl))
-- --   PshHomProf .F-seq β β' =
-- --     makeNatTransPath (funExt λ _ → funExt λ _ → makePshHomPath refl)

-- -- {- a PshIso is a PshHom whose underlying functions are iso -}
-- -- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
-- --   isPshIso : PshHom P Q → Type _
-- --   isPshIso α = ∀ x → isIso (α .N-ob x)

-- --   isPropIsPshIso : ∀ {α} → isProp (isPshIso α)
-- --   isPropIsPshIso = isPropΠ λ _ → isPropIsIsoSet (P .F-ob _ .snd) (Q .F-ob _ .snd)

-- -- module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
-- --   private
-- --     module P = PresheafNotation P using (p[_])
-- --     module Q = PresheafNotation Q using (p[_])
-- --   PshIsoΣ : Type _
-- --   PshIsoΣ = Σ[ α ∈ PshHom P Q ] isPshIso {P = P}{Q = Q} α

-- --   record PshIso : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
-- --     no-eta-equality
-- --     constructor pshiso
-- --     field
-- --       trans : PshHom P Q
-- --       nIso : isPshIso {P = P}{Q = Q} trans

-- --   PshIsoΣIso : Iso PshIso PshIsoΣ
-- --   unquoteDef PshIsoΣIso = defineRecordIsoΣ PshIsoΣIso (quote (PshIso))

-- --   open PshIso

-- --   PshIso→PshIsoLift : PshIso → PshIsoLift C P Q
-- --   PshIso→PshIsoLift α .NatIso.trans .NatTrans.N-ob x x₁ =
-- --     lift (α .trans .N-ob x (x₁ .lower))
-- --   PshIso→PshIsoLift α .NatIso.trans .NatTrans.N-hom f =
-- --     funExt (λ x₁ → cong lift (α .trans .N-hom _ _ f (x₁ .lower)))
-- --   PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.inv =
-- --     λ z → lift (α .nIso x .fst (z .lower))
-- --   PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.sec =
-- --     funExt (λ x₁ → cong lift (α .nIso x .snd .fst (x₁ .lower)) )
-- --   PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.ret =
-- --     funExt (λ x₁ → cong lift (α .nIso x .snd .snd (x₁ .lower)))

-- -- open PshIso

-- -- -- A PshCatIso is an iso in the (locally small) category of
-- -- -- presheaves, that is the inverse is known to be a homomorphism.
-- -- --
-- -- -- Eventually PshCatIso should become the default and PshIso should
-- -- -- only be used as a *method of construction* for PshCatIso.
-- -- module _ {C : Category ℓc ℓc'} where
-- --   private
-- --     PshC = PRESHEAF C
-- --     module PshC = LocallySmallCategoryNotation PshC
-- --   PshCatIso : ∀ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) → Type _
-- --   PshCatIso P Q = PshC.ISOC.Hom[ (_ , liftω P) , (_ , liftω Q) ]

-- --   module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
-- --     private
-- --       module P = PresheafNotation P
-- --       module Q = PresheafNotation Q
-- --     makePshIsoPath : {α β : PshIso P Q}
-- --       → α .trans .N-ob ≡ β .trans .N-ob
-- --       → α ≡ β
-- --     makePshIsoPath α≡β = isoFunInjective (PshIsoΣIso P Q) _ _
-- --       (Σ≡Prop (λ α → isPropIsPshIso {α = α}) (makePshHomPath α≡β))

-- --     invPshIso : PshIso P Q → PshIso Q P
-- --     invPshIso α .trans .N-ob c = α .nIso c .fst
-- --     invPshIso α .trans .N-hom c c' f p =
-- --       isoFun≡ (invIso (isIsoToIso (α .nIso _)))
-- --         (Q.⟨⟩⋆⟨ sym $ α .nIso c' .snd .fst p ⟩ ∙ sym (α .trans .N-hom _ _ _ _))
-- --     invPshIso α .nIso x .fst = α .trans .N-ob x
-- --     invPshIso α .nIso x .snd .fst = α .nIso x .snd .snd
-- --     invPshIso α .nIso x .snd .snd = α .nIso x .snd .fst

-- --     PshIso→PshCatIso : PshIso P Q
-- --       → PshCatIso P Q
-- --     PshIso→PshCatIso α .LocallySmall.CatIso.fun = α .trans
-- --     PshIso→PshCatIso α .LocallySmall.CatIso.inv = invPshIso α .trans
-- --     PshIso→PshCatIso α .LocallySmall.CatIso.sec = makePshHomPath (funExt λ x → funExt (α .nIso x .snd .fst))
-- --     PshIso→PshCatIso α .LocallySmall.CatIso.ret = makePshHomPath (funExt λ x → funExt (α .nIso x .snd .snd))

-- --     PshCatIso→isPshIso : (α : PshCatIso P Q) → isPshIso (α .LocallySmall.CatIso.fun)
-- --     PshCatIso→isPshIso α x .fst = α .LocallySmall.CatIso.inv .N-ob x
-- --     PshCatIso→isPshIso α x .snd .fst q i = α .LocallySmall.CatIso.sec i .N-ob x q
-- --     PshCatIso→isPshIso α x .snd .snd p i = α .LocallySmall.CatIso.ret i .N-ob x p

-- --     PshCatIso→PshIso
-- --       : PshCatIso P Q
-- --       → PshIso P Q
-- --     PshCatIso→PshIso α .trans = α .LocallySmall.CatIso.fun
-- --     PshCatIso→PshIso α .nIso = PshCatIso→isPshIso α

-- --   PshIso≅PshCatIso : ∀ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) →
-- --     Iso (PshIso P Q)
-- --         (PshCatIso P Q)
-- --   PshIso≅PshCatIso P Q .Iso.fun = PshIso→PshCatIso
-- --   PshIso≅PshCatIso P Q .Iso.inv = PshCatIso→PshIso
-- --   PshIso≅PshCatIso P Q .Iso.rightInv α = PshC.ISOC≡ refl
-- --   PshIso≅PshCatIso P Q .Iso.leftInv α = makePshIsoPath refl

-- -- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}
-- --   where
-- --   private
-- --     module C = Category C
-- --     module P = PresheafNotation P

-- --   PQ-ob-ty = Eq.singl (P .F-ob)
-- --   PQ-hom-ty : PQ-ob-ty → Type _
-- --   PQ-hom-ty PQ-ob =
-- --     Eq.singlP
-- --       (Eq.ap
-- --         (λ Q-ob → ∀ {x}{y} → C [ x , y ] → ⟨ Q-ob y ⟩ → ⟨ Q-ob x ⟩)
-- --         (PQ-ob .snd))
-- --       (P .F-hom)

-- --   eqToPshIso-ob : (PQ-ob : PQ-ob-ty) →
-- --     ∀ (c : C.ob) → hSet ℓp
-- --   eqToPshIso-ob (_ , Eq.refl) = P .F-ob

-- --   eqToPshIso-N-ob : (PQ-ob : PQ-ob-ty) →
-- --     ∀ (c : C.ob) → P.p[ c ] → ⟨ PQ-ob .fst c ⟩
-- --   eqToPshIso-N-ob (_ , Eq.refl) = λ _ z → z

-- --   eqToPshIso-N-hom :
-- --     (PQ-ob : PQ-ob-ty) →
-- --     (PQ-hom : PQ-hom-ty PQ-ob) →
-- --     ∀ (c c' : C.ob) → (f : C [ c , c' ]) →
-- --     (p : P.p[ c' ]) →
-- --     eqToPshIso-N-ob PQ-ob c (f P.⋆ p) ≡
-- --       PQ-hom .fst f (eqToPshIso-N-ob PQ-ob c' p)
-- --   eqToPshIso-N-hom (_ , Eq.refl) (_ , Eq.refl) =
-- --     λ _ _ _ _ → refl

-- --   eqToPshIso-nIso :
-- --     (PQ-ob : PQ-ob-ty) →
-- --     ∀ (c : C.ob) → isIso (eqToPshIso-N-ob PQ-ob c)
-- --   eqToPshIso-nIso (_ , Eq.refl) c =
-- --     (λ z → z) , (λ _ → refl) , (λ _ → refl)

-- --   module _
-- --     (Q : Presheaf C ℓp)
-- --     (eq-ob : P .F-ob Eq.≡ Q .F-ob)
-- --     (eq-hom :
-- --       Eq.HEq
-- --         (Eq.ap (λ F-ob' → ∀ {x}{y} →
-- --                  C [ x , y ] → ⟨ F-ob' y ⟩ → ⟨ F-ob' x ⟩) eq-ob)
-- --         (P .F-hom) (Q .F-hom))
-- --     where

-- --     private
-- --       PQ-ob : PQ-ob-ty
-- --       PQ-ob = _ , eq-ob

-- --       PQ-hom : PQ-hom-ty PQ-ob
-- --       PQ-hom = _ , eq-hom

-- --     eqToPshHom : PshHom P Q
-- --     eqToPshHom = record {
-- --           N-ob = eqToPshIso-N-ob PQ-ob
-- --         ; N-hom = eqToPshIso-N-hom PQ-ob PQ-hom }

-- --     -- TODO: make the default constructing a PshCatIso
-- --     eqToPshIso : PshIso P Q
-- --     eqToPshIso = record {
-- --         trans = eqToPshHom
-- --       ; nIso = eqToPshIso-nIso PQ-ob}

-- --     eqToPshCatIso : PshCatIso P Q
-- --     eqToPshCatIso = PshIso→PshCatIso eqToPshIso

-- -- -- -- Univalence stuff. Needed?
-- -- --   -- This is for when they have the same universe level
-- -- --   module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓp} where
-- -- --     private
-- -- --       module P = PresheafNotation P
-- -- --       module Q = PresheafNotation Q
-- -- --     PshIso→SETIso : PshIso P Q → ∀ x → CatIso (SET ℓp) (P .F-ob x) (Q .F-ob x)
-- -- --     PshIso→SETIso α c .fst = α .trans .N-ob c
-- -- --     PshIso→SETIso α c .snd .isIsoC.inv = α .nIso c .fst
-- -- --     PshIso→SETIso α c .snd .isIsoC.sec = funExt (α .nIso c .snd .fst)
-- -- --     PshIso→SETIso α c .snd .isIsoC.ret = funExt (α .nIso c .snd .snd)

-- -- --     PshIso→Path : PshIso P Q → P ≡ Q
-- -- --     PshIso→Path α =
-- -- --       Functor≡
-- -- --         (λ c → CatIsoToPath isUnivalentSET' (PshIso→SETIso α c))
-- -- --         λ {c}{c'} f →
-- -- --           toPathP (funExt (λ q →
-- -- --             (transport (Pc≡Qc c') $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
-- -- --               ≡⟨ univSet'β (PshIso→SETIso α c') ((f P.⋆ transport (sym $ Pc≡Qc c) q)) ⟩
-- -- --             (α .trans .N-ob c' $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
-- -- --               ≡⟨ cong (α .trans .N-ob c') P.⟨ refl ⟩⋆⟨ ~univSet'β (PshIso→SETIso α c) q ⟩ ⟩
-- -- --             (α .trans .N-ob c' $ f P.⋆ α .nIso c .fst q)
-- -- --               ≡⟨ α .trans .N-hom c' c f (α .nIso c .fst q) ⟩
-- -- --             f Q.⋆ (α .trans .N-ob c $ α .nIso c .fst q)
-- -- --               ≡⟨ Q.⟨ refl ⟩⋆⟨ α .nIso c .snd .fst q ⟩ ⟩
-- -- --             f Q.⋆ q
-- -- --               ∎ ))
-- -- --       where
-- -- --         Pc≡Qc : ∀ c → P.p[ c ] ≡ Q.p[ c ]
-- -- --         Pc≡Qc c i = ⟨ CatIsoToPath isUnivalentSET' (PshIso→SETIso α c) i ⟩
