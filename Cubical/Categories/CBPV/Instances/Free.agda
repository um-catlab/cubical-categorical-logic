-- Judgemental model of CBPV
-- no β/η laws for type connectives
{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.Free where
  open import Cubical.Foundations.Function
  open import Cubical.Data.List hiding (init)
  open import Cubical.Foundations.Prelude renaming (comp to compose)


  module Syn { ℓ : Level} where
    mutual
      data CTy : Type ℓ where
        fun : VTy → CTy → CTy
        F : VTy → CTy

      data VTy : Type ℓ where
        one : VTy
        prod : VTy → VTy → VTy
        U : CTy → VTy


    Ctx = List {ℓ} VTy

    ⊘ : Ctx
    ⊘ = []

    private
      variable
        Δ Γ Θ ξ Δ' Γ' Θ' ξ' : Ctx
        B B' B'' B''' : CTy
        A A' : VTy


    data Sub[_,_] : (Δ : Ctx) (Γ : Ctx) → Type ℓ
    data _⊢v_   : (Γ : Ctx) (S : VTy) → Type ℓ
    data _⊢c_  : (Γ : Ctx) (S : CTy) → Type ℓ
    data _◂_⊢k_ : (Γ : Ctx) (S : CTy) (T : CTy) → Type ℓ
    _[_]vP : Γ ⊢v A → Sub[ Δ , Γ ] → Δ ⊢v A
    varP : (A ∷ Γ) ⊢v A
    private
      variable
        γ : Sub[ Δ , Γ ]
        δ : Sub[ Θ , Δ ]
        ρ : Sub[ ξ , Θ ]
        v : Γ ⊢v A
        m : Γ ⊢c B
        E E' E'' : Γ ◂ B ⊢k B'

    data Sub[_,_] where
      -- axiomitize substitution as a category
      ids : Sub[ Γ ,  Γ ]
      _∘s_ : Sub[ Δ , Θ ] → Sub[ Γ , Δ ] → Sub[ Γ , Θ ]
      ∘sIdL : ids ∘s γ ≡ γ
      ∘sIdR : γ ∘s ids ≡ γ
      ∘sAssoc : γ ∘s (δ ∘s ρ ) ≡ (γ ∘s δ) ∘s ρ
      isSetSub : isSet (Sub[ Δ , Γ ])

      -- with a terminal object
      !s : Sub[ Γ , ⊘ ]
      ⊘η : γ ≡ !s

      -- universal property of context extension
      _,s_ : Sub[ Γ , Δ ] → Γ ⊢v A → Sub[ Γ , A ∷ Δ ]
      wk : Sub[ A ∷ Γ , Γ ]
      wkβ :  wk ∘s (γ ,s v) ≡ γ
      ,sη : γ  ≡ ((wk ∘s γ) ,s (varP [ γ ]vP))

    data _⊢v_ where
      -- substitution
      _[_]v : Γ ⊢v A → Sub[ Δ , Γ ] → Δ ⊢v A
      subIdV : v [ ids ]v ≡ v
      subAssocV : v [ γ ∘s δ ]v ≡ (v [ γ ]v) [ δ ]v
      isSetVal : isSet (Γ ⊢v A)

      -- variable
      var : (A ∷ Γ) ⊢v A
      varβ : var [ δ ,s v ]v ≡ v

      -- we arent' interested in preserving type structure here..
      -- so no natural isomorphisms
      u :
        ----------
        Γ ⊢v one

      pair :
        Γ ⊢v A →
        Γ ⊢v A' →
        -----------------
        Γ ⊢v (prod A A')

      thunk :
        Γ ⊢c B →
        ----------
        Γ ⊢v U B

    data _◂_⊢k_ where
      -- a cateogory of stacks
      ∙k : Γ ◂ B ⊢k B
      _∘k_ :  Γ ◂ B' ⊢k B'' → Γ ◂ B ⊢k B' → Γ ◂ B ⊢k B''
      ∘kIdL : ∙k ∘k E ≡ E
      ∘kIdR : E ∘k ∙k ≡ E
      ∘kAssoc : E'' ∘k (E' ∘k E) ≡ (E'' ∘k E')∘k E
      isSetStack : isSet (Γ ◂ B ⊢k B')

      -- enriched in presheaves over contests
      _[_]k : Γ ◂ B ⊢k B' → Sub[ Δ , Γ ] → Δ ◂ B ⊢k B'
      subIdK : E [ ids ]k ≡ E
      subAssocK : E [ γ ∘s δ ]k ≡ (E [ γ ]k) [ δ ]k
      plugDist : ∙k {B = B} [ γ ]k ≡ ∙k
      substDist : (E' ∘k E) [ γ ]k ≡  (E' [ γ ]k) ∘k (E [ γ ]k)

      -- stacks
      x←∙:M :
        Γ ◂ B ⊢k F A →
        (A ∷ Γ) ⊢c B' →
        -----------------
        Γ ◂ B ⊢k B'

      ∙V :
        Γ ⊢v A →
        Γ ◂ B ⊢k fun A B' →
        --------------------
        Γ ◂ B ⊢k B'

    data _⊢c_ where
      -- plug
      _[_]∙  : Γ ◂ B ⊢k B' → Γ ⊢c B → Γ ⊢c B'
      plugId : ∙k [ m ]∙ ≡ m
      plugAssoc : (E' ∘k E) [ m ]∙ ≡ (E' [ E [ m ]∙ ]∙)

      -- enriched in presehaves of contexts
      _[_]c : Γ ⊢c B → Sub[ Δ , Γ ] → Δ ⊢c B
      subIdC : m [ ids ]c ≡ m
      subAssocC : m [ γ ∘s δ ]c ≡ (m [ γ ]c) [ δ ]c
      subPlugDist : (E [ m ]∙) [ γ ]c ≡ ((E [ γ ]k) [ m [ γ ]c ]∙)
      subPlugComp : ((E [ δ ∘s γ ]k) [ m [ γ ]c ]∙) ≡
                    (((E [ δ ]k) [ m ]∙) [ γ ]c)
      isSetComp : isSet (Γ ⊢c B)

      -- computations
      ret :
        Γ ⊢v A →
        ---------
        Γ ⊢c F A

      force :
        Γ ⊢v U B →
        -----------
        Γ ⊢c B

      lam :
        (A ∷ Γ) ⊢c B →
        ----------------
        Γ ⊢c fun A B
      app :
        Γ ⊢c fun A B →
        Γ ⊢v A →
        ----------------
        Γ ⊢c B

      rec× :
        Γ ⊢v (prod A A') →
        (A' ∷ (A ∷  Γ)) ⊢c B →
        --------------------
        Γ ⊢c B

      bind :
        Γ ⊢c F A →
        (A ∷ Γ) ⊢c B →
        -----------
        Γ ⊢c B

    _[_]vP = _[_]v
    varP = var

  -- TODO initiality
  module InitialModel {ℓ : Level} where
    open import Cubical.Data.List hiding (init)
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Enriched.Presheaf
    open import Cubical.Categories.Enriched.More
    open import Cubical.Categories.CBPV.Base
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Data.Sigma
    open EnrichedCategory
    open EnrichedFunctor
    open Category
    open Functor
    open NatTrans
    open NatIso
    open CBPVModel {ℓ}
    open Syn {ℓ}

    SCat : Category _ _
    SCat .ob = Ctx
    SCat .Hom[_,_] = Sub[_,_]
    SCat .id = ids
    SCat ._⋆_ f g = g ∘s f
    SCat .⋆IdL _ = ∘sIdR
    SCat .⋆IdR _ = ∘sIdL
    SCat .⋆Assoc _ _ _ = ∘sAssoc
    SCat .isSetHom = isSetSub

    open model SCat {ℓ}

    Ehom : CTy  → CTy  → ob 𝓟
    Ehom B B' .F-ob Γ = Γ ◂ B ⊢k B' , isSetStack
    Ehom B B' .F-hom γ k = k [ γ ]k
    Ehom B B' .F-id = funExt λ _ → subIdK
    Ehom B B' .F-seq γ δ = funExt λ k → subAssocK

    E : EnrichedCategory 𝓟Mon _
    E .ob = CTy
    E .Hom[_,_] = Ehom
    E .id = natTrans (λ _ _ → ∙k) λ _ → funExt λ _ → sym plugDist
    E .seq _ _ _ =
      natTrans (λ{x₁ (k , k') → k' ∘k k}) λ _ → funExt λ _ →  sym substDist
    E .⋆IdL _ _ = makeNatTransPath (funExt λ _ → funExt λ _  → sym ∘kIdR)
    E .⋆IdR _ _ = makeNatTransPath (funExt λ _ → funExt λ _  → sym ∘kIdL)
    E .⋆Assoc _ _ _ _ =
      makeNatTransPath  (funExt λ _ → funExt λ _ →  ∘kAssoc)

    vtm : VTy → Functor (SCat ^op) (SET ℓ)
    vtm A .F-ob Γ = (Γ ⊢v A) , isSetVal
    vtm A .F-hom γ v = v [ γ ]v
    vtm A .F-id = funExt λ _ → subIdV
    vtm A .F-seq _ _ = funExt λ _ → subAssocV

    ctm' : E .ob → ob self
    ctm' B .F-ob Γ = (Γ ⊢c B) , isSetComp
    ctm' B .F-hom γ m = m [ γ ]c
    ctm' B .F-id = funExt λ _ → subIdC
    ctm' B .F-seq _ _ = funExt λ _ →  subAssocC

    𝓟[_,_] = 𝓟 .Hom[_,_]
    E[_,_] = E .Hom[_,_]
    self[_,_]  = self .Hom[_,_]

    plug : (B B' : ob E) → 𝓟[ E[ B , B' ] , self[ ctm' B , ctm' B' ] ]
    plug B B' .N-ob Γ k  =
      pshhom
        (λ Δ (γ , m) → (k [ γ ]k) [ m ]∙)
        λ Δ Θ γ (δ , m) → subPlugComp
    plug B B' .N-hom γ = funExt λ k →
      makePshHomPath (funExt λ Θ → funExt λ (δ , m) →
        cong (λ h → h [ m ]∙ ) (sym subAssocK))

    ctm : EnrichedFunctor 𝓟Mon E self
    ctm .F₀ = ctm'
    ctm .F₁ {B} {B'}= plug B B'
    ctm .Fid {B} =
      makeNatTransPath (funExt λ Γ → funExt λ tt* →
        makePshHomPath (funExt λ Δ → funExt λ (γ , m) →
        cong (λ h → h [ m ]∙) plugDist ∙ plugId ))
    ctm .Fseq =
      makeNatTransPath (funExt λ Γ → funExt λ (k , k') →
        makePshHomPath (funExt λ Δ → funExt λ (γ , m) →
          cong₂
          (λ h1 h2 → ((k' [ h1 ]k) [ (k [ h2 ]k) [ m ]∙ ]∙))
          ∘sIdR ∘sIdR
          ∙ sym plugAssoc
          ∙ cong (λ h → ( h [ m ]∙)) (sym substDist)))

    up : (Γ : Ctx) (A : VTy) →
      SCat [-, (A ∷ Γ) ] ≅ᶜ ((SCat [-, Γ ]) ×Psh vtm A)
    up Γ A .trans = goal where
      goal : NatTrans (SCat [-, A ∷ Γ ]) ((SCat [-, Γ ]) ×Psh vtm A)
      goal .N-ob Δ γ = (wk ∘s γ) , (var [ γ ]v)
      goal .N-hom γ = funExt λ δ → ΣPathP (∘sAssoc , subAssocV)
    up Γ A .nIso Δ .isIso.inv (γ , m) = γ ,s m
    up Γ A .nIso Δ .isIso.sec = funExt λ (γ , m) → ΣPathP (wkβ , varβ)
    up Γ A .nIso Δ .isIso.ret = funExt λ γ → sym ,sη

    init : CBPVModel
    init .𝓒 = SCat
    init .𝓔 = E
    init .vTy = VTy
    init .vTm = vtm
    init .cTm = ctm
    init .emp = ⊘ , λ Γ → !s , λ _ → sym ⊘η
    init ._×c_ Γ A = A ∷ Γ
    init .up×c = up
