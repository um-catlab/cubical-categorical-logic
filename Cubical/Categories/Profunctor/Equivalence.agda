{-
  Show equivalence of definitions from Profunctor.General
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Equivalence where
{-
open import Cubical.Categories.Profunctor.General

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Limits.Terminal

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Tactics.CategorySolver.Reflection
open import Cubical.Tactics.FunctorSolver.Reflection




private
  variable ℓC ℓC' ℓD ℓD' ℓS : Level

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') (R : C *-[ ℓS ]-o D) where

  open Category
  open NatIso
  open NatTrans
  open Functor
  open Contravariant
  open Iso
  open ProfHomo
  open UnivElt
  open isUniversal
  open Bifunctor

  ProfRepresentation≅PshFunctorRepresentation : Iso (ProfRepresentation C D R)
                                                (PshFunctorRepresentation C D R)
  ProfRepresentation≅PshFunctorRepresentation =
    record {
     fun = (ProfRepresentation→PshFunctorRepresentation C D R) ;
     inv = (PshFunctorRepresentation→ProfRepresentation C D R) ;
     rightInv = Psh→Prof→Psh ;
     leftInv = Prof→Psh→Prof
    }
    where
    Psh→Prof→Psh : (Psh : PshFunctorRepresentation C D R)
      → (ProfRepresentation→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ProfRepresentation C D R) Psh)
        ≡ Psh
    Psh→Prof→Psh (G , η) =
      ΣPathP (
        refl ,
        makeNatIsoPathP
          refl
          refl
          (funExt (λ c → makeNatTransPath (funExt (λ d → refl))))
      )

    Prof→Psh→Prof : (Prof : ProfRepresentation C D R)
      → (PshFunctorRepresentation→ProfRepresentation C D R)
        ((ProfRepresentation→PshFunctorRepresentation C D R) Prof)
        ≡ Prof
    Prof→Psh→Prof (G , η) =
      let
        (G' , η') = (PshFunctorRepresentation→ProfRepresentation C D R)
                    (ProfRepresentation→PshFunctorRepresentation C D R (G , η))
        R' = (Functor→Prof*-o C D
               (fst (PshFunctorRepresentation→ProfRepresentation C D R
               (ProfRepresentation→PshFunctorRepresentation C D R (G , η)))))
      in
      ΣPathP (
        refl ,
        ΣPathP (
          cong′
          (λ X → isoProfHomoProfHomo' R R' .inv (ProfHomo'IsoΣ R R' .inv X))
          -- Turn the records into Σ types, then prove we have a path between
          -- the Σ-tized versions of η and η'
          (ΣPathP
            (refl ,
              (ΣPathP (
                (isProp-natL R R'
                  (isoProfHomoProfHomo' R R' .fun (η .fst))
                  (ProfHomo'.PH-natL (isoProfHomoProfHomo' R R' .fun (η' .fst)))
                  (λ c c' d f r i → PH-natL (fst η) f r i)
                ) ,
                (isProp-natR R R'
                  ((isoProfHomoProfHomo' R R' .fun (η .fst)))
                  ((ProfHomo'.PH-natR (isoProfHomoProfHomo' R R'
                    .fun (η' .fst))))
                  (λ c d d' r g i → PH-natR (fst η) r g i)
                )
              ))
            )
          ) ,
          funExt (λ d → funExt (λ c → refl))
        )
      )

  PshFunctorRepresentation≅ParamUnivElt : Iso (PshFunctorRepresentation C D R)
                                              (ParamUnivElt C D R)
  PshFunctorRepresentation≅ParamUnivElt =
    record {
      fun = PshFunctorRepresentation→ParamUnivElt C D R ;
      inv = ParamUnivElt→PshFunctorRepresentation C D R ;
      rightInv = Univ→PshFunctor→Univ ;
      leftInv = PshFunctor→Univ→PshFunctor
    }
    where
    Univ→PshFunctor→Univ : ∀ (U : ParamUnivElt C D R) →
      ((PshFunctorRepresentation→ParamUnivElt C D R)
        ((ParamUnivElt→PshFunctorRepresentation C D R) U) ≡
      U)
    Univ→PshFunctor→Univ U =
      let (G , η) = (ParamUnivElt→PshFunctorRepresentation C D R) U
          U' = PshFunctorRepresentation→ParamUnivElt C D R (G , η)
      in
      funExt (λ c →
        -- easier to do proof with UniversalElements, use isomorphism
        sym (UniversalElement≅UnivElt D (pAppR R c) .Iso.rightInv (U' c))
        ∙
        congS (UniversalElement→UnivElt D (pAppR R c))
          -- underlying proof of Universal Elements being the same
          -- terminal object
          ( ΣPathPProp
            {u = UnivElt→UniversalElement D (pAppR R c) (U' c)}
            {v = UnivElt→UniversalElement D (pAppR R c) (U c)}
            (isPropIsTerminal (∫ᴾ_ {C = D} (pAppR R c)))
            ( ΣPathP (
              -- same object
              refl ,
              -- paths equal as εc ⋆ id = εc
              (λ i → ((pAppR R c) .F-id (i)) (U c .element))
            ))
          )
        ∙
        UniversalElement≅UnivElt D (pAppR R c) .Iso.rightInv (U c)
      )

    PshFunctor→Univ→PshFunctor : ∀ (Psh : (PshFunctorRepresentation C D R)) →
      ((ParamUnivElt→PshFunctorRepresentation C D R)
        ((PshFunctorRepresentation→ParamUnivElt C D R) Psh) ≡
      Psh)
    PshFunctor→Univ→PshFunctor (G , η) =
      let η⁻¹ = symNatIso η
          U' = ((PshFunctorRepresentation→ParamUnivElt C D R) (G , η))
          (G' , η') = ((ParamUnivElt→PshFunctorRepresentation C D R) U')
          G'≡G = (Functor≡
                    -- object map is same
                    (λ c → refl)
                    -- morphisms are the same due to the
                    -- uniqueness of coinduction
                    (λ {x} {y} ϕ →
                      let dx = U' x .vertex
                          εx = U' x .element
                          dy = U' y .vertex
                          εy = U' y .element
                          R⟅-,y⟆ = (pAppR R y)
                          R⟅dx,-⟆ = (pAppL R dx)
                      in
                       G' ⟪ ϕ ⟫
                       ≡⟨ sym(U' y .universal .is-uniq
                        ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx)
                        (G ⟪ ϕ ⟫)
                        {-
                          nested proof that G ⟪ ϕ ⟫ also satisfies this
                          coinduction
                          this works by the following diagram between
                            the presheafs R⟅-,a⟆ and D[-,Ga]
                                   ηx
                             R⟅-,x⟆ ==> D[-,Gx]
                           λR(ϕ)  ∥         ∥ (G(ϕ) ∘ -)
                                  ⇓    ηy   ⇓
                             R⟅-,y⟆ ==> D[-,Gy]

                          These are presheafs D ^op ⟶ SET, and we consider
                            the slice of this diagram at G ⟅ x ⟆
                                        ηxᴳˣ
                                 R⟅Gx,x⟆ --→ D[Gx,Gx]
                          λR(ϕ)ᴳˣ  |            |  (G(ϕ) ∘ -)
                                  ↓            ↓
                                 R⟅Gx,y⟆ --→ D[Gx,Gy]
                                        ηyᴳˣ
                          Note that by construction, the η and G here define
                          the coinduction and εx ⋆ maps
                            (these are what form the NatIso)
                          Thus the equality of the 2 expressions below follows
                            from the fact that η is a natural transformation

                                              εx ⋆
                                    D[Gx,Gx] ---→ R⟅Gx,x⟆
                                      |  id   ⊢→ εx  |
                          (G(ϕ) ∘ -)  |   ↓       ↓  |  λR(ϕ)ᴳˣ = R⟅Gx,-⟆ ⟪ ϕ ⟫
                                      ↓  G(ϕ) ⊢→  ∎  ↓
                                    D[Gx,Gy] --→ R⟅Gx,y⟆
                                             εy ⋆
                        -}
                        (
                          (D [ εy ∘ᴾ⟨ R⟅-,y⟆ ⟩ (G ⟪ ϕ ⟫) ])
                            ≡⟨ refl ⟩
                          lower (((LiftF ∘F R⟅-,y⟆) ⟪ G ⟪ ϕ ⟫ ⟫)
                          ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ y ⟆)) (lift (D .id))))
                            ≡⟨ (λ i → lower (((LiftF ∘Fb R ) .Bif-idR (~ i))
                               (((LiftF ∘Fb R) .Bif-homL (G ⟪ ϕ ⟫) _)
                                ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ y ⟆))
                                  (lift (D .id)))))) ⟩
                          lower ((((Prof*-o→Functor C D (LiftF ∘Fb R )) ⟅ y ⟆)
                            ⟪ G ⟪ ϕ ⟫ ⟫) ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ y ⟆))
                              (lift (D .id))))
                            -- since εy is defined in terms of R(Gy, y), we
                              -- first use naturality
                            -- to consider the relevant component of the εy ⋆
                              -- map, namely the component at Gx
                            ≡⟨ (λ i → lower (((η⁻¹ .trans .N-ob y
                              .N-hom (G ⟪ ϕ ⟫)) (~ i)) (lift (D .id)) ) ) ⟩
                            -- next, we use some recombining of G ϕ to see
                              -- it as an application
                            -- of a different Hom Functor applied to id at
                              -- Gx instead of Gy:
                              lower ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆))
                                (((Bifunctor→Functor (LiftF ∘Fb (HomBif D)))
                                  ⟪ G ⟪ ϕ ⟫ , G ⟪ C .id ⟫ ⟫) (lift (D .id))))
                            ≡⟨ (λ i → lower ((η⁻¹ .trans
                              .N-ob y .N-ob (G ⟅ x ⟆))
                              (lift (((Bifunctor→Functor (HomBif D))
                                ⟪ G ⟪ ϕ ⟫ , G .F-id i ⟫) (D .id))))
                            )⟩
                          lower ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆))
                            (lift (((Bifunctor→Functor (HomBif D)) ⟪ G ⟪ ϕ ⟫ ,
                              D .id ⟫) (D .id))))
                            ≡⟨ (λ i → lower ((η⁻¹ .trans .N-ob y .N-ob
                              (G ⟅ x ⟆)) (lift (((HomBif D) .Bif-idR (i) ∘f
                                (HomBif D) ⟪ G ⟪ ϕ ⟫ ⟫l ) (D .id))))) ⟩
                          lower ((η⁻¹ .trans .N-ob y .N-ob (G ⟅ x ⟆))
                            (lift (G ⟪ ϕ ⟫ ⋆⟨ D ⟩ D .id)))
                            ≡⟨ (λ i → lower ((η⁻¹ .trans .N-ob y .N-ob
                              (G ⟅ x ⟆)) (lift (D .⋆IdL (D .⋆IdR (G ⟪ ϕ ⟫)
                                (i)) (~ i))))) ⟩
                          lower (((η⁻¹ .trans .N-ob y) .N-ob (G ⟅ x ⟆))
                            (lift ((D .id) ⋆⟨ D ⟩ G ⟪ ϕ ⟫)))
                            ≡⟨ (λ i → lower (
                                ((η⁻¹ .trans .N-ob y) .N-ob (G ⟅ x ⟆))
                                  (lift (((HomBif D) ⟪ G ⟪ ϕ ⟫ ⟫r ∘f
                                    ((HomBif D) .Bif-idL (~ i))) (D .id)))
                            )) ⟩
                          lower (
                            ((η⁻¹ .trans .N-ob y) .N-ob (G ⟅ x ⟆))
                              (lift (((Bifunctor→Functor (HomBif D))
                                ⟪ D .id , G ⟪ ϕ ⟫ ⟫) (D .id)))
                          )
                            ≡⟨ refl ⟩
                          lower (
                            ((((Prof*-o→Functor C D (LiftF ∘Fb
                              (Functor→Prof*-o C D G))) ⟪ ϕ ⟫)
                              ⋆⟨ FUNCTOR (D ^op) (SET _) ⟩
                            η⁻¹ .trans .N-ob y) .N-ob (G ⟅ x ⟆))
                            (lift (D .id))
                          )
                            -- now, since we are operating of the section of Gx
                              -- as described above, we
                            -- can use the above argument to port over to εx
                            ≡⟨ (λ i → lower (
                              (((η⁻¹ .trans .N-hom ϕ) (i)) .N-ob (G ⟅ x ⟆))
                              (lift (D .id))
                            )) ⟩
                          lower (
                            ((η⁻¹ .trans .N-ob x
                              ⋆⟨ FUNCTOR (D ^op) (SET _) ⟩
                            ((Prof*-o→Functor C D (LiftF ∘Fb R)) ⟪ ϕ ⟫)
                            ) .N-ob (G ⟅ x ⟆))
                            (lift (D .id))
                          )
                            ≡⟨ (λ i → (R .Bif-assoc (D .id) ϕ (i)) εx) ⟩
                          (R .Bif-homL (D .id) _) ((R .Bif-homR (G ⟅ x ⟆) ϕ) εx)
                            ≡⟨ ( λ i → (R .Bif-idL i)
                              ((R .Bif-homR (G ⟅ x ⟆) ϕ) εx))⟩
                          ((R⟅dx,-⟆ ⟪ ϕ ⟫) εx) ∎
                        )
                       )⟩
                       G ⟪ ϕ ⟫ ∎)
                )
      in ΣPathP (
        G'≡G ,
        (makeNatIsoPathP
          refl
          (cong′ (λ X → Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb
            Functor→Prof*-o C D X)) G'≡G)
          (funExt (λ (c : C .ob) →
            (makeNatTransPathP
              refl
              (cong′ (λ X → (Prof*-o→Functor C D (LiftF {ℓD'}{ℓS} ∘Fb
                Functor→Prof*-o C D X)) .F-ob c) G'≡G)
              (funExt (λ (d : D .ob) →
                (funExt λ _ → refl)
              ))
            )
          ))
        )
      )

  ParamUnivElt≅ParamUniversalElement : Iso (ParamUnivElt C D R)
                                           (ParamUniversalElement C D R)
  ParamUnivElt≅ParamUniversalElement =
    iso
      (ParamUnivElt→ParamUniversalElement C D R)
      (ParamUniversalElement→ParamUnivElt C D R)
      (λ U → funExt λ c → Σ≡Prop
        (isPropIsTerminal (∫ᴾ_ {C = D} (pAppR R c))) refl)
      λ U → refl

  ProfRepresentation≅ParamUnivElt : Iso (ProfRepresentation C D R)
                                        (ParamUnivElt C D R)
  ProfRepresentation≅ParamUnivElt = compIso
                                    ProfRepresentation≅PshFunctorRepresentation
                                    PshFunctorRepresentation≅ParamUnivElt

  ProfRepresentation≅ParamUniversalElement : Iso (ProfRepresentation C D R)
                                                 (ParamUniversalElement C D R)
  ProfRepresentation≅ParamUniversalElement = compIso
                                             ProfRepresentation≅ParamUnivElt
                                             ParamUnivElt≅ParamUniversalElement

  PshFunctorRepresentation≅ParamUniversalElement : Iso
    (PshFunctorRepresentation C D R) (ParamUniversalElement C D R)
  PshFunctorRepresentation≅ParamUniversalElement =
    compIso PshFunctorRepresentation≅ParamUnivElt
            ParamUnivElt≅ParamUniversalElement
-}
