{-
   Monads as extension systems, i.e., in terms of unit and bind,
   deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
module Cubical.Categories.Monad.ExtensionSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category
  private
    variable
      a b c : C .ob
      f g h : C [ a , b ]

  record ExtensionSystemFor (T : C .ob → C .ob) : Type (ℓ-max ℓ ℓ') where
    field
      η : C [ a , T a ]
      bind : C [ a , T b ] → C [ T a , T b ]
      bind-r : bind (η {a = a}) ≡ C .id
      bind-l : bind f ∘⟨ C ⟩ η ≡ f
      bind-comp : bind f ∘⟨ C ⟩ bind g ≡ bind (bind f ∘⟨ C ⟩ g)

  ExtensionSystem = Σ[ T ∈ (C .ob → C .ob) ] ExtensionSystemFor T

  -- module _ where
  --   open ExtensionSystemFor
  --   ExtensionSystem≡ : {T T' : ExtensionSystem}
  --     → (T≡ : T .fst ≡ T .fst)
  --     → PathP (λ i → ∀ {a} → C [ a , T≡ i a ]) (T .snd .η) (T .snd .η)
  --     → PathP (λ i → ∀ {a}{b} → C [ a , T≡ i b ] → C [ T≡ i a , T≡ i b ])
           --     (T .snd .bind) (T .snd .bind)
  --     → T ≡ T'
  --   ExtensionSystem≡ = {!!}

  module _ (E : ExtensionSystem) where
    private
      T = E .fst
    open ExtensionSystemFor (E .snd)
    Kleisli : Category _ _
    Kleisli .ob = C .ob
    Kleisli .Hom[_,_] a b = C [ a , T b ]
    Kleisli .id = η
    Kleisli ._⋆_ f g = bind g ∘⟨ C ⟩ f
    Kleisli .⋆IdL f = bind-l
    Kleisli .⋆IdR f = cong₂ (comp' C) bind-r refl ∙ C .⋆IdR f
    Kleisli .⋆Assoc f g h = C .⋆Assoc _ _ _ ∙ cong₂ (comp' C) bind-comp refl
    Kleisli .isSetHom = C .isSetHom

    open Functor
    G : Functor Kleisli C
    G .F-ob = T
    G .F-hom = bind
    G .F-id = bind-r
    G .F-seq f g = sym bind-comp

    open import Cubical.Categories.Adjoint.UniversalElements
    open import Cubical.Categories.Presheaf.Representable
    open UniversalElement
    open isEquiv
    F : LeftAdjoint G
    F c .vertex = c
    F c .element = η
    F c .universal d = isIsoToIsEquiv
      ( (λ x → x)
      , (λ b → bind-l)
      , λ f → bind-l)
    -- TODO: by abstract nonsense construct a monad structure for T

  open ExtensionSystemFor
  record MonadMorphism (T : ExtensionSystem) (T' : ExtensionSystem) :
    Type (ℓ-max ℓ ℓ') where
    field
      trans : ∀ a → C [ T .fst a , T' .fst a ]
      preserve-η : ∀ a → trans a ∘⟨ C ⟩ T .snd .η {a} ≡ T' .snd .η
      preserve-bind : ∀ a b (f : C [ a , T .fst b ]) →
        trans b ∘⟨ C ⟩ T .snd .bind f
        ≡ T' .snd .bind (trans b ∘⟨ C ⟩ f) ∘⟨ C ⟩ trans a
    trans' : C [ T .fst a , T' .fst a ]
    trans' = trans _

    preserve-η' : trans' ∘⟨ C ⟩ T .snd .η {a} ≡ T' .snd .η
    preserve-η' = preserve-η _

    preserve-bind' : trans' ∘⟨ C ⟩ T .snd .bind f ≡
                     T' .snd .bind (trans' ∘⟨ C ⟩ f) ∘⟨ C ⟩ trans'
    preserve-bind' = preserve-bind _ _ _

  unquoteDecl MonadMorphismIsoΣ =
    declareRecordIsoΣ MonadMorphismIsoΣ (quote MonadMorphism)
  open MonadMorphism
  open Iso
  MonadMorphism≡ : {T T' : ExtensionSystem} {ϕ ϕ' : MonadMorphism T T'}
                 → (ϕ .trans ≡ ϕ' .trans)
                 → ϕ ≡ ϕ'
  MonadMorphism≡ p = isoFunInjective MonadMorphismIsoΣ _ _
    (Σ≡Prop (λ ϕ → isPropΣ (isPropΠ (λ _ → C .isSetHom _ _))
            λ _ → isPropΠ3 (λ _ _ _ → C .isSetHom _ _)) p)

  MONAD : Category (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  MONAD .ob = ExtensionSystem
  MONAD .Hom[_,_] = MonadMorphism
  MONAD .id .trans _ = C .id
  MONAD .id .preserve-η _ = C .⋆IdR _
  MONAD .id {x = T} .preserve-bind _ _ _ =
    C .⋆IdR _ ∙ cong (T .snd .bind) (sym (C .⋆IdR _)) ∙ sym (C .⋆IdL _)
  (MONAD ⋆ ϕ) ψ .trans _ =
    trans' ψ ∘⟨ C ⟩ trans' ϕ -- ψ .trans' ∘⟨ C ⟩ ϕ .trans'
  (MONAD ⋆ ϕ) ψ .preserve-η _ =
    sym (C .⋆Assoc _ _ _) ∙
    cong₂ (comp' C) refl (ϕ .preserve-η _) ∙ ψ .preserve-η _
  MONAD ._⋆_ {z = T''} ϕ ψ .preserve-bind _ _ _ =
    sym (C .⋆Assoc _ _ _)
    ∙ cong₂ (comp' C) refl (ϕ .preserve-bind _ _ _)
    ∙ C .⋆Assoc _ _ _ ∙ cong₂ (seq' C) refl
    (ψ .preserve-bind _ _ _ ∙
      cong₂ (seq' C) refl (cong (T'' .snd .bind) (C .⋆Assoc _ _ _))) ∙
      sym (C .⋆Assoc _ _ _)
  MONAD .⋆IdL f = MonadMorphism≡ (funExt λ x → C .⋆IdL _)
  MONAD .⋆IdR f = MonadMorphism≡ (funExt λ x → C .⋆IdR _)
  MONAD .⋆Assoc f g h = MonadMorphism≡ (funExt (λ _ → C .⋆Assoc _ _ _))
  MONAD .isSetHom =
    isSetRetract
      (MonadMorphismIsoΣ .fun)
      ((MonadMorphismIsoΣ .inv))
      (MonadMorphismIsoΣ .ret)
    (isSetΣ (isSetΠ (λ _ → C .isSetHom))
      (λ _ → isSetΣ (isSetΠ (λ _ → isProp→isSet (C .isSetHom _ _)))
                    λ _ → isSetΠ3 (λ _ _ _ → isProp→isSet (C .isSetHom _ _))))

  open Functor
  -- Functor from the 1Category MONAD to the 2Category CATEGORY
  push : {T T' : ExtensionSystem} →
         MonadMorphism T T' → Functor (Kleisli T) (Kleisli T')
  push ϕ .F-ob = λ z → z
  push ϕ .F-hom f = ϕ .trans _ ∘⟨ C ⟩ f
  push ϕ .F-id = ϕ .preserve-η _
  push ϕ .F-seq f g =
    C .⋆Assoc _ _ _ ∙
      cong₂ (seq' C) refl (ϕ .preserve-bind _ _ _) ∙ sym (C .⋆Assoc _ _ _)

  pushId : {T : ExtensionSystem} → push (MONAD .id {T}) ≡ Id
  pushId = Functor≡ (λ _ → refl) λ f → C .⋆IdR _

  pushComp : {T T' T'' : ExtensionSystem}
             (ϕ' : MONAD [ T' , T'' ]) (ϕ : MONAD [ T , T' ])
             → push (ϕ' ∘⟨ MONAD ⟩ ϕ) ≡ (push ϕ' ∘F push ϕ)
  pushComp ϕ' ϕ = Functor≡ (λ _ → refl) (λ f → sym (C .⋆Assoc _ _ _))

  -- Extend the above to a Functor from the 1Category MONAD C to Cat / C
  open NatTrans
  push-G : {T T' : ExtensionSystem} (ϕ : MonadMorphism T T') →
           NatTrans (G T) (G T' ∘F push ϕ)
  push-G ϕ .N-ob = ϕ .trans
  push-G ϕ .N-hom f = ϕ .preserve-bind _ _ f

  -- Avoid transport hell by reproving these explicitly...
  push-G-Id-Path : (T : ExtensionSystem) → (G T ∘F push (MONAD .id)) ≡ G T
  push-G-Id-Path T =
    Functor≡ (λ c → refl) (λ f → cong (T .snd .bind) (C .⋆IdR _))

  push-G-Id : {T : ExtensionSystem} →
              PathP (λ i → NatTrans (G T)
                      (push-G-Id-Path T i))
                      (push-G (MONAD .id)) (idTrans (G T))
  push-G-Id {T} = makeNatTransPathP refl (push-G-Id-Path T) λ i x → C .id

  push-G-Comp-Path : {T T' T'' : ExtensionSystem}
                    (ϕ' : MONAD [ T' , T'' ])(ϕ : MONAD [ T , T' ])
                   → (G T'' ∘F push (ϕ' ∘⟨ MONAD ⟩ ϕ)) ≡
                        ((G T'' ∘F push ϕ') ∘F push ϕ)
  push-G-Comp-Path {T'' = T''} ϕ' ϕ =
    Functor≡ (λ c → refl) λ f → cong (T'' .snd .bind) (sym (C .⋆Assoc _ _ _))

  push-G-Comp : {T T' T'' : ExtensionSystem}
                (ϕ' : MONAD [ T' , T'' ])(ϕ : MONAD [ T , T' ])
              → PathP (λ i → NatTrans (G T) (push-G-Comp-Path ϕ' ϕ i))
                (push-G (ϕ' ∘⟨ MONAD ⟩ ϕ)) ((push-G ϕ' ∘ˡ (push ϕ)) ∘ᵛ push-G ϕ)
  push-G-Comp ϕ' ϕ =
    makeNatTransPathP refl ((push-G-Comp-Path ϕ' ϕ)) (funExt λ x → refl)

  Monad→ExtensionSystem : Monad C → ExtensionSystem
  Monad→ExtensionSystem M .fst = M .fst .F-ob
  Monad→ExtensionSystem M .snd .η = M .snd .IsMonad.η ⟦ _ ⟧
  Monad→ExtensionSystem M .snd .bind f =
    M .snd .IsMonad.μ ⟦ _ ⟧ ∘⟨ C ⟩ M .fst ⟪ f ⟫
  Monad→ExtensionSystem M .snd .bind-r = λ i → M .snd .IsMonad.idr-μ i ⟦ _ ⟧
  Monad→ExtensionSystem M .snd .bind-l =
    sym (C .⋆Assoc _ _ _)
    ∙ cong₂ (C ._⋆_) (sym (M .snd .IsMonad.η .N-hom _)) refl
    ∙ C .⋆Assoc _ _ _
    ∙ cong₂ (seq' C) refl (λ i → M .snd .IsMonad.idl-μ i ⟦ _ ⟧)
    ∙ C .⋆IdR _
  Monad→ExtensionSystem M .snd .bind-comp =
    lem0
    ∙ cong₂ (comp' C) refl (cong₂ (seq' C) refl
      (sym (M .snd .IsMonad.μ .N-hom _)))
    ∙ lem1
    ∙ cong₂ (seq' C) refl (λ i → M .snd .IsMonad.assoc-μ (~ i) ⟦ _ ⟧)
    ∙ lem2
    where
      lem0 : comp' C (comp' C (M .snd .IsMonad.μ ⟦ _ ⟧) (M .fst ⟪ f ⟫))
        (comp' C (M .snd .IsMonad.μ ⟦ _ ⟧) (M .fst ⟪ g ⟫))
           ≡ M .snd .IsMonad.μ ⟦ _ ⟧ ∘⟨ C ⟩
             (M .fst ⟪ f ⟫ ∘⟨ C ⟩
               M .snd .IsMonad.μ ⟦ _ ⟧) ∘⟨ C ⟩ (M .fst ⟪ g ⟫)
      lem0 = solveCat! C

      lem1 : (C ⋆ (C ⋆ F-hom (M .fst) g)
             ((C ⋆ F-hom (M .fst) (F-hom (M .fst) f))
             (M .snd .IsMonad.μ .N-ob (F-ob (M .fst) _))))
               (N-ob (M .snd .IsMonad.μ) _)
           ≡ (((M .snd .IsMonad.μ) ⟦ _ ⟧) ∘⟨ C ⟩
              M .snd .IsMonad.μ ⟦ _ ⟧) ∘⟨ C ⟩
                (M .fst ⟪ M .fst ⟪ f ⟫ ⟫ ∘⟨ C ⟩ M .fst ⟪ g ⟫)
      lem1 = solveCat! C

      lem2 : (C ⋆ (C ⋆ F-hom (M .fst) g) (F-hom (M .fst) (F-hom (M .fst) f)))
             ((C ⋆ F-hom (M .fst)
               (N-ob (M .snd .IsMonad.μ) _)) (M .snd .IsMonad.μ .N-ob _))
           ≡ (C ⋆ F-hom (M .fst)
                ((C ⋆ g) ((C ⋆ F-hom (M .fst) f) (N-ob (M .snd .IsMonad.μ) _)))
              ) (N-ob (M .snd .IsMonad.μ) _)
      lem2 = solveFunctor! C C (M .fst)

  ExtensionSystem→Monad : ExtensionSystem → Monad C
  ExtensionSystem→Monad M .fst .F-ob              = M .fst
  ExtensionSystem→Monad M .fst .F-hom {x} {y} f   = (M .snd .bind) (((M .snd .η) {y}) ∘⟨ C ⟩ f)
  ExtensionSystem→Monad M .fst .F-id {x}          =
    (cong (M .snd .bind) ((C .⋆IdL) ((M .snd .η) {x})))
    ∙ (M .snd .bind-r)
  ExtensionSystem→Monad M .fst .F-seq {x} {y} {z} f g =
    (cong (M .snd .bind) (((C .⋆Assoc) f g (M .snd .η {z}))))
    ∙ (cong
      (λ e → (M .snd .bind) (e ∘⟨ C ⟩ f))
      (sym ((M .snd .bind-l) {f = ((M .snd .η {z}) ∘⟨ C ⟩ g)}))
    )
    ∙ (sym (cong
      (M .snd .bind)
      ((C .⋆Assoc)
        f
        ((M .snd .η) {y})
        ((M .snd .bind) (((M .snd .η) {z}) ∘⟨ C ⟩ g))
      )
    ))
    ∙ (sym ((M .snd .bind-comp) {f = ((M .snd .η) {z}) ∘⟨ C ⟩ g} {g = ((M .snd .η) {y}) ∘⟨ C ⟩ f}))
  ExtensionSystem→Monad M .snd .IsMonad.η .N-ob x = (M .snd .η)
  ExtensionSystem→Monad M .snd .IsMonad.η .N-hom {x} {y} f = sym ((M .snd .bind-l) {f = ((M .snd .η) {y}) ∘⟨ C ⟩ f})
  ExtensionSystem→Monad M .snd .IsMonad.μ .N-ob x = (M .snd .bind) (C .id {(M .fst x)})
  ExtensionSystem→Monad M .snd .IsMonad.μ .N-hom {x} {y} f =
    ((M .snd .bind-comp)
      {f = C .id}
      {g = ((M .snd .η)) ∘⟨ C ⟩ ( (M .snd .bind) (((M .snd .η)) ∘⟨ C ⟩ f) )}
    )
    ∙ (cong
      (M .snd .bind)
      ((C .⋆Assoc)
        ( (M .snd .bind) (((M .snd .η)) ∘⟨ C ⟩ f) )
        (M .snd .η)
        ( (M .snd .bind) (C .id {(M .fst y)}) )
      )
    )
    ∙ (cong
      (λ e → (M .snd .bind) (e ∘⟨ C ⟩ ( (M .snd .bind) (((M .snd .η)) ∘⟨ C ⟩ f) )))
      ((M .snd .bind-l) {f = C .id})
    )
    ∙ (cong
      (M .snd .bind)
      ((C .⋆IdR) ( (M .snd .bind) (((M .snd .η)) ∘⟨ C ⟩ f) ))
    )
    ∙ (sym (cong
      (M .snd .bind)
      ((C .⋆IdL) ( (M .snd .bind) (((M .snd .η)) ∘⟨ C ⟩ f) ))
    ))
    ∙ (sym (
      (M .snd .bind-comp)
      {f = (((M .snd .η)) ∘⟨ C ⟩ f)}
      {g = (C .id)}
    ))
  ExtensionSystem→Monad M .snd .IsMonad.idl-μ     =
    makeNatTransPathP
    F-rUnit
    refl
    (funExt
      (λ x → (M .snd .bind-l) {f = C .id})
    )
  ExtensionSystem→Monad M .snd .IsMonad.idr-μ     =
    makeNatTransPathP
    F-lUnit
    refl
    (funExt
      (λ x →
        (M .snd .bind-comp) {f = C .id} {g = (M .snd .η) ∘⟨ C ⟩ (M .snd .η)}
        ∙ (cong
          (M .snd .bind)
          ((C .⋆Assoc)
            (M .snd .η)
            (M .snd .η)
            ((M .snd .bind) (C .id))
          )
        )
        ∙ (cong
          (λ e → (M .snd .bind) (e ∘⟨ C ⟩ (M .snd .η)))
          ((M .snd .bind-l) {f = C .id})
        )
        ∙ (cong
          (M .snd .bind)
          ((C .⋆IdR) (M .snd .η))
        )
        ∙ (M .snd .bind-r))
    )
  ExtensionSystem→Monad M .snd .IsMonad.assoc-μ   =
    makeNatTransPathP
    F-assoc
    refl
    (funExt λ x →
      (M .snd .bind-comp) {f = C .id} {g = (M .snd .η) ∘⟨ C ⟩ ((M .snd .bind) (C .id))}
      ∙ ((cong
        (M .snd .bind)
        ((C .⋆Assoc)
          ((M .snd .bind) (C .id))
          (M .snd .η)
          ((M .snd .bind) (C .id))
        )
      )
      ∙ (cong
        (λ e → (M .snd .bind) (e ∘⟨ C ⟩ ((M .snd .bind) (C .id))))
        ((M .snd .bind-l) {f = C .id})
      )
      ∙ (cong
        (M .snd .bind)
        ((C .⋆IdR) ((M .snd .bind) (C .id)))
      )
      ∙ (sym (cong
        (M .snd .bind)
        ((C .⋆IdL) ((M .snd .bind) (C .id)))
      )))
      ∙ (sym
        ((M .snd .bind-comp) {f = C .id} {g = C .id})
      )
    )
