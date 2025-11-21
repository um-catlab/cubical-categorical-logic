-- Judgemental model of CBPV
-- no β/η laws for type connectives

module Syntax.CBPV where 
  open import Cubical.Foundations.Function
  open import Cubical.Data.List 
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
      subPlugComp : ((E [ δ ∘s γ ]k) [ m [ γ ]c ]∙) ≡ (((E [ δ ]k) [ m ]∙) [ γ ]c)
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
