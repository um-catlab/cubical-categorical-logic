-- The graph of a profunctor
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.Instances.CoGraph where


-- private
--   variable
--     ℓC ℓC' ℓD ℓD' ℓS : Level

-- open Category
-- open Functor

-- module _ {C : Category ℓC ℓC'}
          -- {D : Category ℓD ℓD'}
  -- (P : C o-[ ℓS ]-* D) where
--   CoGraphOb : Type (ℓ-max ℓC ℓD)
--   CoGraphOb = C .ob ⊎ D .ob

--   data CoGraphHom : CoGraphOb → CoGraphOb →
--                   Type (ℓ-max ℓS (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))) where
--     ↑o : ∀ {A B} → C [ A , B ] → CoGraphHom (inl A) (inl B)
--     ↑* : ∀ {A B} → D [ A , B ] → CoGraphHom (inr A) (inr B)
--     ↑p : ∀ {A B} → ⟨ P ⟅ A , B ⟆ ⟩ → CoGraphHom (inl A) (inr B)

--   CoGraphComp : ∀ {A B C} → CoGraphHom A B → CoGraphHom B C → CoGraphHom A C
--   CoGraphComp (↑o f) (↑o f') = ↑o (f ⋆⟨ C ⟩ f')
--   CoGraphComp (↑* g) (↑* g') = ↑* (g ⋆⟨ D ⟩ g')
--   CoGraphComp (↑o f) (↑p p) = ↑p (P .F-hom (f , (D .id)) p)
--   CoGraphComp (↑p p) (↑* g) = ↑p (P .F-hom ((C .id) , g) p)

--   ↑p-r : ∀ {A B} → CoGraphHom (inl A) (inr B) → ⟨ P ⟅ A , B ⟆ ⟩
--   ↑p-r (↑p p) = p

--   private
--     ↑o-r : ∀ {A B} → CoGraphHom (inl A) (inl B) → C [ A , B ]
--     ↑o-r (↑o f) = f

--     ↑o-r-retract : ∀ {A B} → (f : CoGraphHom (inl A) (inl B)) →
  --     ↑o (↑o-r f) ≡ f
--     ↑o-r-retract (↑o f) = refl

--     ↑*-r : ∀ {A B} → CoGraphHom (inr A) (inr B) → D [ A , B ]
--     ↑*-r (↑* g) = g

--     ↑*-r-retract : ∀ {A B} → (f : CoGraphHom (inr A) (inr B)) →
--     ↑* (↑*-r f) ≡ f
--     ↑*-r-retract (↑* f) = refl

--     ↑p-r-retract : ∀ {A B} → (f : CoGraphHom (inl A) (inr B)) →
                      --     ↑p (↑p-r f) ≡ f
--     ↑p-r-retract (↑p f) = refl

--     absurd-r : ∀ {A B} → CoGraphHom (inr A) (inl B) → ⊥
--     absurd-r ()

--   CoGraph : Category (ℓ-max ℓC ℓD)
--                      (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') ℓS)
--   CoGraph .ob = CoGraphOb
--   CoGraph .Hom[_,_] = CoGraphHom
--   CoGraph .id {inl A} = ↑o (C .id)
--   CoGraph .id {inr B} = ↑* (D .id)
--   CoGraph ._⋆_ = CoGraphComp
--   CoGraph .⋆IdL (↑o f) = cong ↑o (C .⋆IdL f)
--   CoGraph .⋆IdL (↑p p) = cong ↑p (λ i → (P .F-id i) p)
--   CoGraph .⋆IdL (↑* g) = cong ↑* (D .⋆IdL g)
--   CoGraph .⋆IdR (↑o f) = cong ↑o (C .⋆IdR f)
--   CoGraph .⋆IdR (↑p p) = cong ↑p (λ i → (P .F-id i) p)
--   CoGraph .⋆IdR (↑* g) = cong ↑* (D .⋆IdR g)
--   CoGraph .⋆Assoc (↑o f) (↑o f') (↑o f'') = cong ↑o (C .⋆Assoc _ _ _)
--   CoGraph .⋆Assoc (↑o f) (↑o f') (↑p p) =
--     cong ↑p ((λ i → P .F-hom (f ⋆⟨ C ⟩ f' , D .⋆IdL (D .id) (~ i)) p)
--       ∙ λ i → (P .F-seq (f' , D .id) (f , D .id) i) p)
--   CoGraph .⋆Assoc (↑o f) (↑p p) (↑* g) =
--     cong ↑p ((λ i → (P .F-seq (f , D .id) (C .id , g) (~ i)) p)
--       ∙ (λ i → P .F-hom ((C .⋆IdL f ∙ sym (C .⋆IdR f)) i ,
--                          (D .⋆IdL g ∙ sym (D .⋆IdR g)) i) p)
--       ∙ λ i → (P .F-seq ((C .id) , g) (f , (D .id)) i ) p)
--   CoGraph .⋆Assoc (↑p p) (↑* h) (↑* h') =
--     cong ↑p ((λ i → (P .F-seq (C .id , h) (C .id , h') (~ i)) p)
--       ∙ λ i → P .F-hom ( C .⋆IdL (C .id) i , h ⋆⟨ D ⟩ h' ) p)
--   CoGraph .⋆Assoc (↑* h) (↑* h') (↑* h'') = cong ↑* (D .⋆Assoc _ _ _)
--   CoGraph .isSetHom {inl A} {inl A'} =
--     isSetRetract ↑o-r ↑o ↑o-r-retract (C .isSetHom)
--   CoGraph .isSetHom {inl A} {inr B} =
--     isSetRetract ↑p-r ↑p ↑p-r-retract ((P ⟅ _ ⟆ ) .snd)
--   CoGraph .isSetHom {inr B} {inr B'} =
--     isSetRetract ↑*-r ↑* ↑*-r-retract (D .isSetHom)
--   CoGraph .isSetHom {inr B} {inl A} = λ f → Empty.rec (absurd-r f)

--   ↑oF : Functor C CoGraph
--   ↑oF .F-ob = inl
--   ↑oF .F-hom = ↑o
--   ↑oF .F-id = refl
--   ↑oF .F-seq f g = refl

--   ↑*F : Functor D CoGraph
--   ↑*F .F-ob = inr
--   ↑*F .F-hom = ↑*
--   ↑*F .F-id = refl
--   ↑*F .F-seq f g = refl

--   open ProfHom
--   ↑pH : ProfHom P ↑oF ↑*F (HomFunctor CoGraph)
--   ↑pH .R-hom b c = ↑p
--   ↑pH .R-nat b' b c c' f p g =
--     cong ↑p ((λ i → (P ⟪ C .⋆IdL f (~ i) , D .⋆IdL g (~ i) ⟫) p) ∙
--       (λ i → P .F-seq (f , (D .id)) ((C .id) , g) i p))

--   ↑pH-r : ProfHom (HomFunctor CoGraph ∘F ((↑oF ^opF) ×F ↑*F))
--                   (Id {C = C}) (Id {C = D}) P
--   ↑pH-r .R-hom b c = ↑p-r
--   ↑pH-r .R-nat b' b c c' f (↑p p) g =
--     (λ i → P .F-seq (f , (D .id)) ((C .id) , g) (~ i) p) ∙
--       λ i → P .F-hom (C .⋆IdL f i , D .⋆IdL g i) p
