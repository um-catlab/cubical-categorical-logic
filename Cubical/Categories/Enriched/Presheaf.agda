{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Enriched.Presheaf where

  open import Cubical.Categories.Category
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Functor
  open import Cubical.Foundations.HLevels
  open import Cubical.Categories.Monoidal.Base
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Categories.Constructions.BinProduct
  open import Cubical.Categories.Presheaf
  open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
  open import Cubical.Categories.Presheaf.Constructions
  open import Cubical.Categories.Presheaf.Constructions.Exponential
  open import Cubical.Categories.Presheaf.Constructions.BinProduct
  open import Cubical.Categories.Presheaf.Constructions.Reindex
  open import Cubical.Categories.Monoidal.Enriched
  open import Cubical.Categories.Enriched.More
  open import Cubical.Categories.Bifunctor
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Data.Unit
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Limits.BinProduct
  open MonoidalCategory
  open MonoidalStr
  open TensorStr
  open Category
  open Functor
  open NatIso
  open NatTrans
  open BinProduct
  open Bifunctor
  open EnrichedCategory


  private
      variable
          ℓ ℓ' ℓS : Level
  module model (𝓒 : Category ℓ ℓ') {ℓS : Level} where
    ℓm = ℓ-max ℓ' (ℓ-max ℓ ℓS)
    𝓟 = PresheafCategory 𝓒 (ℓm)

    ⨂' : Bifunctor 𝓟 𝓟 𝓟
    ⨂' = PshProd {ℓ}{ℓ'}{𝓒}{ℓm}{ℓm}

    -- Agda chokes without explicit args
    ⨂ : Functor (𝓟 ×C 𝓟) 𝓟
    ⨂ = BifunctorToParFunctor
        {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
        {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
        {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}⨂'


    𝟙 : ob 𝓟
    𝟙 .F-ob _ = Unit* , isSetUnit*
    𝟙 .F-hom = λ _ _ → tt*
    𝟙 .F-id = refl
    𝟙 .F-seq _ _ = refl

    𝓟Ten :  TensorStr 𝓟
    𝓟Ten . ─⊗─ = ⨂
    𝓟Ten .unit = 𝟙

    _^_ : ob 𝓟 → ob 𝓟 → ob 𝓟
    _^_ B A = A ⇒PshLarge B

    eval : {P Q : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh P , Q ]
    eval {P}{Q} = PshHom→NatTrans (appPshHom P Q)

    π₁p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , P ]
    π₁p {P}{Q} = PshHom→NatTrans (π₁ P Q)

    π₂p : {P Q  : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ]
    π₂p {P}{Q} = PshHom→NatTrans (π₂ P Q)

    idl : ⨂ ∘F rinj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
    idl .trans = natTrans (λ P → π₂p) λ _ → makeNatTransPath refl
    idl .nIso P =
        isiso
            (natTrans (λ x Px → tt* , Px) λ _ → refl)
            (makeNatTransPath refl)
            (makeNatTransPath refl)

    idr : ⨂ ∘F linj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
    idr .trans = natTrans (λ P → π₁p) λ _ → makeNatTransPath refl
    idr .nIso P =
        isiso
            (natTrans (λ x Px → Px , tt*) λ _ → refl)
            (makeNatTransPath refl)
            (makeNatTransPath refl)

    assoc : {P Q R : ob 𝓟} → 𝓟 [ P ×Psh (Q ×Psh R) , (P ×Psh Q ) ×Psh R ]
    assoc .N-ob c (p , (q , r)) = (p , q) , r
    assoc .N-hom f = refl

    𝓟Mon' : MonoidalStr 𝓟
    𝓟Mon' .tenstr = 𝓟Ten
    𝓟Mon' .α =
      record {
        trans =
          natTrans
            (λ {(P , (Q , R)) → assoc})
            λ _ → makeNatTransPath refl ;
        nIso = λ{ (P , Q , R) →
          isiso
              (natTrans (λ{ c ((p , q) , r ) → p , (q , r)}) λ _ → refl)
              (makeNatTransPath refl)
              (makeNatTransPath refl) }}
    𝓟Mon' .η = idl
    𝓟Mon' .ρ = idr
    𝓟Mon' .pentagon P Q R S = makeNatTransPath refl
    𝓟Mon' .triangle P Q = makeNatTransPath refl

    𝓟Mon : MonoidalCategory (ℓ-suc ℓm) (ℓm)
    𝓟Mon .C = 𝓟
    𝓟Mon .monstr = 𝓟Mon'

    adjL : {P Q R : ob 𝓟} → 𝓟 [ P ×Psh Q , R ] → 𝓟 [ P , R ^ Q ]
    adjL {P}{Q}{R} f = PshHom→NatTrans (λPshHom Q R (NatTrans→PshHom f))

    dup : {P : ob 𝓟} → 𝓟 [ P , P ×Psh P ]
    dup = natTrans (λ x x₁ → x₁ , x₁) λ _ → refl

    swap : {P Q : ob 𝓟} → 𝓟 [ P ×Psh Q , Q ×Psh P ]
    swap = dup ⋆⟨ 𝓟 ⟩  ⨂' .Bif-hom× π₂p π₁p

    selfid : {P : ob 𝓟} → NatTrans 𝟙 (P ^ P)
    selfid {P} .N-ob Γ tt* = π₂ _ _
    selfid {P} .N-hom γ = funExt λ tt* → makePshHomPath refl

    expseq : {P Q R : ob 𝓟} → 𝓟 [ (Q ^ P) ×Psh (R ^ Q) ,  (R ^ P) ]
    expseq {P}{Q}{R} =
        adjL (
            swap ⋆⟨ 𝓟 ⟩
            assoc ⋆⟨ 𝓟 ⟩
            ⨂' .Bif-hom× swap (idTrans _) ⋆⟨ 𝓟 ⟩
            ⨂' .Bif-hom× eval (idTrans _) ⋆⟨ 𝓟 ⟩
            swap ⋆⟨ 𝓟 ⟩
            eval )

    self : EnrichedCategory 𝓟Mon (ℓ-suc ℓm)
    self .ob = ob 𝓟
    self .Hom[_,_] P Q = Q ^ P
    self .id = selfid
    self .seq P Q R = expseq
    self .⋆IdL P Q =
        makeNatTransPath (funExt λ c → funExt λ{(tt* , f) →
          makePshHomPath  (funExt λ c' → funExt λ {(g , Pc') →
            cong (λ h → f .PshHom.N-ob c' (h , Pc')) (sym (𝓒 .⋆IdL _ ))})})
    self .⋆IdR P Q =
        makeNatTransPath (funExt λ c → funExt λ{(f , tt*) →
          makePshHomPath  (funExt λ c' → funExt λ {(g , Pc') →
            cong (λ h → f .PshHom.N-ob c' (h , Pc')) (sym (𝓒 .⋆IdL _ ))})})
    self .⋆Assoc P Q R S =
        makeNatTransPath (funExt λ c → funExt λ{ (f , g , h) →
          makePshHomPath (funExt λ c' → funExt λ{ (j , Pc') →
            cong (h .PshHom.N-ob c') ((cong₂ _,_ (sym (𝓒 .⋆IdL _)) refl))
            ∙ cong (λ e →
              h .PshHom.N-ob c' ((𝓒 ⋆ id 𝓒) ((𝓒 ⋆ id 𝓒) j),
              g .PshHom.N-ob c' ((𝓒 ⋆ id 𝓒) ((𝓒 ⋆ id 𝓒) j) ,
              f .PshHom.N-ob c' (e , Pc'))))
            (cong (𝓒 ⋆ id 𝓒)  (𝓒 .⋆IdL _))})})

  module _ {C D : Category ℓ ℓ'}(F : Functor D C)
      {ℓS ℓE : Level} (EC : EnrichedCategory (model.𝓟Mon C {ℓS}) ℓE )
      where
    open model C {ℓS} renaming (𝓟Mon to 𝓒Mon ; π₂p to Cπ₂p ; _^_ to _^𝓒_ ;
      self to self𝓒 ; ℓm to ℓm𝓒)
    open model D {ℓS} renaming (𝓟Mon to 𝓓Mon; _^_ to _^𝓓_ ;
      self to self𝓓 ; ℓm to ℓm𝓓)

    open MonoidalCategory 𝓒Mon
      renaming (ob to ob𝓒; Hom[_,_] to 𝓒[_,_]; id to id𝓒; _⋆_ to _⋆𝓒_;
        unit to unit𝓒; _⊗_ to _⊗𝓒_; η⟨_⟩ to η𝓒⟨_⟩ ; _⊗ₕ_ to _⊗ₕ𝓒_ )

    open MonoidalCategory 𝓓Mon
      renaming (ob to ob𝓓; Hom[_,_] to 𝓓[_,_]; id to id𝓓; _⋆_ to _⋆𝓓_;
        unit to unit𝓓 ; _⊗_ to _⊗𝓓_; η⟨_⟩ to η𝓓⟨_⟩ ; _⊗ₕ_ to _⊗ₕ𝓓_;
        ρ⟨_⟩ to ρ𝓓⟨_⟩ )

    distrib^ : {X Y : ob𝓒} →
      𝓓[ reindPsh F (Y ^𝓒 X) , reindPsh F Y ^𝓓 reindPsh F X ]
    distrib^ .N-ob d exp =
      pshhom
      (λ {d' (f , XFd') → exp .PshHom.N-ob (F .F-ob d') (F .F-hom f , XFd')})
      λ {d d' f (g , FXd') →
        cong (λ h → exp .PshHom.N-ob _ h) (cong₂ _,_ (F .F-seq _ _) refl)
      ∙ exp .PshHom.N-hom (F .F-ob d)(F .F-ob d')(F .F-hom f)
        (F .F-hom g , FXd')}
    distrib^ .N-hom {d}{d'} f = funExt λ p →
      makePshHomPath (funExt λ  d'' → funExt λ {(g , XFd'') →
        cong (λ h → p .PshHom.N-ob _ h) (cong₂ _,_ (sym ( F-seq F g f )) refl)})

    EC[_,_] = EC .Hom[_,_]

    const : 𝓓[ unit𝓓 , reindPsh F unit𝓒 ]
    const = natTrans (λ _ _ → tt*) λ _ → refl

    distrib : {x y z : ob EC} →
      𝓓[ reindPsh F EC[ x , y ] ⊗𝓓 reindPsh F EC[ y , z ] ,
         reindPsh F (EC[ x , y ] ⊗𝓒 EC[ y , z ]) ]
    distrib = natTrans (λ _ x → x) λ _ → refl

    Eid : {x : ob EC} → 𝓓[ unit𝓓 , reindPsh F EC[ x , x ] ]
    Eid = const ●ᵛ (EC .id ∘ˡ (F ^opF))

    Eseq : {x y z : ob EC} →
      𝓓[ reindPsh F EC[ x , y ] ⊗𝓓 reindPsh F EC[ y , z ] ,
         reindPsh F EC[ x , z ] ]
    Eseq {x}{y}{z} = distrib ●ᵛ (EC .seq x y z ∘ˡ (F ^opF))

    BaseChange : EnrichedCategory 𝓓Mon ℓE
    BaseChange .ob = ob EC
    BaseChange .Hom[_,_] c c' = reindPsh F (EC[ c , c' ])
    BaseChange .id {x} = Eid
    BaseChange .seq x y z = Eseq
    BaseChange .⋆IdL x y =
      makeNatTransPath (funExt λ d → funExt⁻
        (cong (N-ob) (EC .⋆IdL x y)) (F-ob F d))
    BaseChange .⋆IdR x y =
      makeNatTransPath (funExt λ d → funExt⁻
        (cong (N-ob) (EC .⋆IdR x y)) (F-ob F d))
    BaseChange .⋆Assoc x y z w =
      makeNatTransPath (funExt λ d → funExt⁻
        (cong N-ob (EC .⋆Assoc x y z w)) (F-ob F d))


  -- construct a normal category from an enriched category
  module _ {C : Category ℓ ℓ'}{ℓS : Level}  where
    open model C {ℓS}

    module _ (E : EnrichedCategory 𝓟Mon ℓS ) where

      open EnrichedCategory E renaming (ob to obE ; Hom[_,_] to E[_,_];
        id to idE ; seq to seqE ; ⋆IdL to ⋆IdLE ; ⋆IdR to ⋆IdRE ;
        ⋆Assoc to ⋆AssocE)
      open MonoidalCategory 𝓟Mon renaming (_⊗ₕ_ to _⊗ₕ𝓟_ ; η⟨_⟩  to η𝓟⟨_⟩ )

      norm : Category _ _
      norm .ob = obE
      norm .Hom[_,_] e₁ e₂ = 𝓟 [ 𝟙 , E[ e₁ , e₂ ] ]
      norm .id = idE
      norm ._⋆_ {e₁}{e₂}{e₃} f g = dup ⋆⟨ 𝓟 ⟩ f ⊗ₕ𝓟 g ⋆⟨ 𝓟 ⟩ seqE e₁ e₂ e₃
      norm .⋆IdL {e₁}{e₂} f =
          makeNatTransPath (funExt λ c → funExt λ {tt* →
          λ i → sym (⋆IdLE e₁ e₂) i .N-ob c (tt* , f .N-ob c tt*)})
      norm .⋆IdR {e₁}{e₂} f =
        makeNatTransPath (funExt λ c → funExt λ {tt* →
          λ i → sym (⋆IdRE e₁ e₂) i .N-ob c (f .N-ob c tt* ,  tt*)})
      norm .⋆Assoc f g h =
        makeNatTransPath (funExt λ c → funExt λ{ tt* →
          λ i → ⋆AssocE _ _ _ _ i .N-ob c
            (f .N-ob c tt* , (g .N-ob c tt* , h .N-ob c tt*))})
      norm .isSetHom = 𝓟 .isSetHom

  -- Psh(SET) enriched category from a normal category
  module _ (C : Category ℓ ℓ') where
    open model (SET ℓ') {ℓ'} renaming (𝓟Mon to 𝓟Set)
    open MonoidalCategory 𝓟Set renaming (Hom[_,_] to 𝓟Set[_,_] ; _⊗_ to _⊗𝓟_ ;
      η⟨_⟩ to η𝓟⟨_⟩ ; ρ⟨_⟩ to ρ𝓟⟨_⟩ ; _⊗ₕ_ to _⊗ₕ𝓟_) hiding (C)

    -- set indexed hom
    iHom : (c c' : ob C) → ob 𝓟
    iHom c c' = LiftF ∘F ((SET _) [-, (C [ c , c' ]) , C .isSetHom ])

    id' : {c : ob C} → 𝓟 [ 𝟙 , iHom c c ]
    id' {c} .N-ob _ tt* = lift (λ _ → C .id)
    id' {c} .N-hom _ = refl

    seqE : (c₁ c₂ c₃ : ob C) → 𝓟 [ iHom c₁ c₂ ⊗𝓟 iHom c₂ c₃ , iHom c₁ c₃ ]
    seqE c₁ c₂ c₃ .N-ob A (f , g) = lift λ a → f .lower a ⋆⟨ C ⟩ g .lower a
    seqE c₁ c₂ c₃ .N-hom _ = refl

    enrich : EnrichedCategory 𝓟Set ℓ
    enrich .ob = ob C
    enrich .Hom[_,_] = iHom
    enrich .id = id'
    enrich .seq  = seqE
    enrich .⋆IdL _ _ =
        makeNatTransPath (funExt λ A → funExt λ {(tt* , f) →
          cong lift (funExt λ a → sym (C .⋆IdL _))})
    enrich .⋆IdR _ _ =
      makeNatTransPath (funExt λ A → funExt λ {(f , tt*) →
        cong lift (funExt λ a → sym (C .⋆IdR _))})
    enrich .⋆Assoc _ _ _ _ =
      makeNatTransPath (funExt λ A → funExt λ (f , (g , h)) →
        cong lift (funExt λ a → C .⋆Assoc _ _ _))

  module _ (C D : Category ℓ ℓ') (F : Functor C D) where
    open model (SET ℓ') {ℓ'} renaming (𝓟Mon to 𝓟Set)
    open MonoidalCategory 𝓟Set renaming (Hom[_,_] to 𝓟Set[_,_] ; _⊗_ to _⊗𝓟_ ;
      η⟨_⟩ to η𝓟⟨_⟩ ; ρ⟨_⟩ to ρ𝓟⟨_⟩ ; _⊗ₕ_ to _⊗ₕ𝓟_) hiding (C)
    open EnrichedFunctor

    enrich-fmap : {c c' : ob (enrich C)} →
      𝓟 [ (enrich C) .Hom[_,_] c c' ,
          (enrich D) .Hom[_,_] (F .F-ob c) (F .F-ob c') ]
    enrich-fmap =
      natTrans
        (λ A P → lift (λ a → F .F-hom (P .lower a)))
        λ f → refl

    enrichF : EnrichedFunctor 𝓟Set (enrich C) (enrich D)
    enrichF .F₀ = F .F-ob
    enrichF .F₁ {c}{c'} = enrich-fmap
    enrichF .Fid =
      makeNatTransPath (funExt λ A → funExt λ {tt* →
        cong lift (funExt λ a → F .F-id)})
    enrichF .Fseq =
      makeNatTransPath (funExt λ A → funExt λ {(f , g) →
        cong lift (funExt λ a → sym (F .F-seq (f .lower a) (g .lower a) ))})

  -- change of base for self enrichment
  module _ {C D : Category ℓ ℓ'}(F : Functor D C)  where
    open model C {ℓ'} renaming (𝓟Mon to 𝓒Mon ; π₂p to Cπ₂p ; _^_ to _^𝓒_ ;
      self to self𝓒 ; ℓm to ℓm𝓒)
    open model D {ℓ'} renaming (𝓟Mon to 𝓓Mon; _^_ to _^𝓓_ ; self to self𝓓 ;
      ℓm to ℓm𝓓)
    ℓh = ℓ-max ℓ ℓ'
    -- note ℓm𝓒 = ℓh = ℓm𝓓

    _ : EnrichedCategory 𝓓Mon (ℓ-suc ℓh)
    _ = self𝓓

    _ : EnrichedCategory 𝓓Mon (ℓ-suc ℓh)
    _ = BaseChange F self𝓒

    open EnrichedFunctor
    BaseChangeSelf :  EnrichedFunctor 𝓓Mon (BaseChange F self𝓒) self𝓓
    BaseChangeSelf .F₀ = reindPsh F
    BaseChangeSelf .F₁ {X}{Y} = distrib^ F self𝓒
    BaseChangeSelf .Fid =
      makeNatTransPath (funExt λ m → funExt λ {tt* →
      makePshHomPath (funExt λ n → funExt λ {(f , XFn) → refl})})
    BaseChangeSelf .Fseq =
      makeNatTransPath (funExt λ m → funExt λ{(f , x) →
      makePshHomPath (funExt λ n → funExt λ {(g , XFn) →
        cong (λ h → x . PshHom.N-ob _ h)
            (cong₂ _,_
                (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))
                (cong (λ h → f .PshHom.N-ob _ (h , XFn))
                (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))))})})

  module _
      {𝓒 𝓓 : Category ℓ ℓ'}
      (F : Functor 𝓓 𝓒)
      {ℓS ℓE : Level} where
      open model 𝓒 {ℓS} renaming (𝓟Mon to 𝓒Mon)
      open model 𝓓 {ℓS} renaming (𝓟Mon to 𝓓Mon)

      module _
          {C C' : EnrichedCategory 𝓒Mon ℓE}
          (𝓖 : EnrichedFunctor 𝓒Mon C C' ) where

          open EnrichedFunctor

          BaseChangeF : EnrichedFunctor 𝓓Mon (BaseChange F C) (BaseChange F C')
          BaseChangeF .F₀ = F₀ 𝓖
          BaseChangeF .F₁ = 𝓖 .F₁ ∘ˡ ((F ^opF))
          BaseChangeF .Fid =
            makeNatTransPath (funExt λ d → funExt⁻
              (cong N-ob (Fid 𝓖)) (F-ob F d))
          BaseChangeF .Fseq =
            makeNatTransPath (funExt λ d → funExt⁻
              (cong N-ob (Fseq 𝓖)) (F-ob F d))

