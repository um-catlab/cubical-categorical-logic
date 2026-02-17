module Cubical.Categories.CBPV.shulman where 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma
open Category
open Functor
open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Instances.Preorders.Monotone
open MonFun
open PreorderStr
open import Cubical.Categories.Adjoint
open NaturalBijection

{-
module Preorders where
    -- a type with a binary Relation
    -- homs are functors which preserve the relation
    RelG : Category (ℓ-suc ℓ-zero) ℓ-zero
    RelG .ob = Σ[ X ∈ Type ] (X → X → hProp ℓ-zero)
    RelG .Hom[_,_] (X , R) (Y , R') = Σ[ f ∈ (X → Y) ] ((x x' : X) → ⟨ R x x' ⟩  → ⟨ R' (f x) (f x') ⟩ )
    RelG .id = (λ z → z) , (λ x₁ x' z → z)
    RelG ._⋆_ = λ f g →
        (λ z₁ → g .fst (f .fst z₁)) ,
        (λ x₁ x' z₁ → g .snd (f .fst x₁) (f .fst x') (f .snd x₁ x' z₁))
    RelG .⋆IdL _ = refl
    RelG .⋆IdR _ = refl
    RelG .⋆Assoc _ _ _ = refl
    RelG .isSetHom = {!   !}

    ≡RelGHom : {X Y : ob RelG}{f g : RelG [ X , Y ]} → f .fst ≡ g .fst → f ≡ g
    ≡RelGHom {X}{Y}{f}{g} p = Σ≡Prop (λ f → isPropΠ λ x x₁ y  → funExt λ x₂  → funExt λ x₃ → Y .snd (f x) (f _) .snd (x₁ x₂ x₃) (y x₂ x₃)) p


    -- a type with a binary relation that is reflexive and transitive
    -- homs are functors which preserve the relation
    Pre : Category (ℓ-suc ℓ-zero) ℓ-zero
    Pre .ob = Preorder ℓ-zero ℓ-zero
    Pre .Hom[_,_] = MonFun
    Pre .id = MonId
    Pre ._⋆_ = MonComp
    Pre .⋆IdL _ = refl
    Pre .⋆IdR _ = refl
    Pre .⋆Assoc _ _ _ = refl
    Pre .isSetHom = MonFunIsSet {!   !}

    open PreorderStr
    open MonFun
    open IsPreorder
    open import Cubical.Foundations.Isomorphism
    -- we can forget that the relation is reflexive and transitive
    -- we do ensure it is valued in prop
    -- that is elements x x' : X are related in At Most One way
    U : Functor Pre RelG
    U .F-ob (X , preorderstr _≤_ str) = X , λ x y → (x ≤ y) , str .is-prop-valued x y
    U .F-hom mon = mon .f , λ _ _ → mon .isMon
    U .F-id = refl
    U .F-seq _ _ = refl

    {-
    this is the interesting part ..
    we are given a set with a prop valued binary relation
    so any x x' : X are related in At Most One way
    but now we need a preorder but not just any preorder..
    one which will be the left adjoint to the forgetful functor
    so we need a "freely generated preorder"
    this is the reflexive transitive closure
    -}

    data rtc (X : ob RelG ) : ⟨ X ⟩ → ⟨ X ⟩ → Type ℓ-zero where
        inc : {x y : ⟨ X ⟩ } → ⟨ X .snd x y ⟩ → rtc X x y
        squash : {x y : ⟨ X ⟩} → isProp (rtc X x y)
        ref : {x : ⟨ X ⟩ } → rtc X x x
        tran : {x y z : ⟨ X ⟩ } → rtc X x y → rtc X y z → rtc X x z

    -- this should trivially be a preorder
    -- is is by definition a free preorder
    rtcPre : (X : ob RelG ) → Preorder ℓ-zero ℓ-zero
    rtcPre X .fst = ⟨ X ⟩
    rtcPre X .snd ._≤_ = rtc X
    rtcPre X .snd .isPreorder .is-prop-valued _ _ = squash
    rtcPre X .snd .isPreorder .is-refl _ = ref
    rtcPre X .snd .isPreorder .is-trans _ _ _ = tran

    -- now given a morphism in RelG (f : X → Y, prf : (x x' : X) → Rx (x , x') → Ry (f x) (f x'))
    -- we should have a monotone map between rtc X and rtc Y
    rtcMon : (X Y : ob RelG) → RelG [ X , Y ] → Pre [ rtcPre X , rtcPre Y ]
    rtcMon X Y (f , prf) .MonFun.f = f
    rtcMon X Y (f , prf) .isMon {x}{x'} = goal  where
        -- we know this holds for the inclusion 'inc'
        -- the rest of the proof is recursive
        goal : {x x' : ⟨ X ⟩ } → rtc X x x' → rtc Y (f x) (f x')
        goal (inc p) = inc (prf _ _ p)
        goal (squash p q i) = squash (goal p) (goal q) i
        goal ref = ref
        goal (tran p q) = tran (goal p) (goal q)


    F : Functor RelG Pre
    F .F-ob = rtcPre
    F .F-hom {X}{Y} = rtcMon X Y
    F .F-id = eqMon _ _ refl
    F .F-seq _ _ = eqMon _ _ refl

    -- now we want to show the adjuction via natural isomorphism of homsets
    -- we are given a map from the RTC of c to some preorder d
    --
    to : {c : ob RelG} {d : ob Pre } → Pre [ F ⟅ c ⟆ , d ] → RelG [ c , U ⟅ d ⟆ ]
    to record { f = f ; isMon = isMon } = f , λ x x' z → isMon (inc z)

    fro : {c : ob RelG} {d : ob Pre } → RelG [ c , U ⟅ d ⟆ ] → Pre [ F ⟅ c ⟆ , d ]
    fro {c}{d} (f , prf) = record { f = f ; isMon = goal } where
        _ : (F ⟅ c ⟆) .fst → d .fst
        _ = f

        goal : {x y : fst c} → rtc c x y → (d .snd ≤ f x) (f y)
        goal (inc x) = prf _ _ x
        goal (squash x x₁ i) = is-prop-valued (isPreorder (d .snd)) (f _) (f _) (goal x) (goal x₁) i
        goal ref = is-refl (isPreorder (d .snd)) (f _)
        goal (tran x x₁) = is-trans (isPreorder (d .snd)) (f _) (f _) (f _) (goal x) (goal x₁)

    adj : F ⊣ U
    adj ._⊣_.adjIso .Iso.fun = to
    adj ._⊣_.adjIso .Iso.inv = fro
    adj ._⊣_.adjIso {c}{d} .Iso.sec b = ≡RelGHom {c}{U ⟅ d ⟆}  refl
    adj ._⊣_.adjIso .Iso.ret a = eqMon _ _ refl
    adj ._⊣_.adjNatInD {c}{d}{d'} f g = ≡RelGHom {c}{U ⟅ d' ⟆ } refl
    adj ._⊣_.adjNatInC f g = eqMon _ _ refl


    -- usage

    data Obs : Type where
        A B C D E : Obs

    open import Cubical.Functions.Logic
    open import Cubical.Data.Unit
    -- topological order
    -- D  A  C B E
    Rel : Obs → Obs → hProp ℓ-zero
    Rel A B = ⊤
    Rel A C = ⊤
    Rel D A = ⊤
    Rel B E = ⊤
    Rel D C = ⊤
    Rel _ _ = ⊥

    ex : ob RelG
    ex = Obs , Rel

    preex : ob Pre
    preex = rtcPre ex

    open import Cubical.Data.Nat
    open import Cubical.Data.Nat.Order renaming (_≤_ to _≤N_)

    natPre : ob Pre
    natPre .fst = ℕ
    natPre .snd ._≤_ = _≤N_
    natPre .snd .isPreorder .is-prop-valued n m = isProp≤ {n}{m}
    natPre .snd .isPreorder .is-refl n = ≤-refl
    natPre .snd .isPreorder .is-trans _ _ _ = ≤-trans

    ahh : RelG [ ex , U .F-ob natPre ]
    ahh .fst A = 1
    ahh .fst B = 3
    ahh .fst C = 2
    ahh .fst D = 0
    ahh .fst E = 4
    ahh .snd A B _ = ≤SumRight {k = 2}
    ahh .snd A C _ = ≤SumRight {k = 1}
    ahh .snd B E _ = ≤SumRight {k = 1}
    ahh .snd D A _ = ≤SumRight {k = 1}
    ahh .snd D C _ = ≤SumRight {k = 2}

    -- question: Is it possible to "derive" Rel D E
    deriv : rtc ex D E
    deriv = tran x (tran y z) where
        x : rtc ex D A
        x = inc tt*

        y : rtc ex A B
        y = inc tt*

        z : rtc ex B E
        z = inc tt*

    _ : deriv ≡ tran (inc tt*) (tran (inc tt*) (inc tt*))
    _ = refl

    oh : 0 ≤N 4
    oh = fro {ex} {natPre} ahh .isMon deriv

    {-
    The idea is this..
    perform a derivation in the free structure..
    then it should hold in any other structure of the same "type"
    we only need to map the generators of the

    note we have a concrete representation of the free structure here
    -}

    -- note this is just fancy syntax for the reflexive transitive closure
    module PreTT {X : ob RelG } where
        data _⊢_ : ⟨ X ⟩ → ⟨ X ⟩ → Type where
            axiom : {A B : ⟨ X ⟩} →
                ⟨ X .snd A B ⟩ →
                --------------
                A ⊢ B
            ref : {A : ⟨ X ⟩ } → A ⊢ A
            tran : {A B C : ⟨ X ⟩ } →
                A ⊢ B →
                B ⊢ C →
                -------------
                A ⊢ C
            squash : {A B : ⟨ X ⟩} →
                isProp (A ⊢ B)



        Free : ob Pre
        Free .fst = ⟨ X ⟩
        Free .snd ._≤_ = _⊢_
        Free .snd .isPreorder .is-prop-valued _ _ = squash
        Free .snd .isPreorder .is-refl _ = ref
        Free .snd .isPreorder .is-trans _ _ _ = tran
       

-}
-- Generalizing
CAT : Category (ℓ-suc ℓ-zero) ℓ-zero
CAT .ob = Category ℓ-zero ℓ-zero
CAT .Hom[_,_] = Functor
CAT .id = Id
CAT ._⋆_ F G = G ∘F F
CAT .⋆IdL _ = Functor≡  (λ _ → refl) λ _ → refl
CAT .⋆IdR _ = Functor≡  (λ _ → refl) λ _ → refl
CAT .⋆Assoc _ _ _ = Functor≡  (λ _ → refl) λ _ → refl
CAT .isSetHom = {!   !}

-- open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base hiding (Node ; Edge)

GRAPH : Category (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
GRAPH .ob = Graph ℓ-zero ℓ-zero
GRAPH .Hom[_,_] = GraphHom
GRAPH .id = IdHom
GRAPH ._⋆_ = _⋆GrHom_
GRAPH .⋆IdL _ = GrHom≡ (λ _ → refl)  λ _ → refl
GRAPH .⋆IdR _ = GrHom≡ (λ _ → refl)  λ _ → refl
GRAPH .⋆Assoc _ _ _ = GrHom≡ (λ _ → refl)  λ _ → refl
GRAPH .isSetHom = {!   !}

{-
-- The type theory corresponding to the free category on graph G
module GraphTT  where
{- previously A ⊢ B : hProp    
    there is at most one derivation (? but axioms and refl ?)
    now we can have multiple derivations of A ⊢ B

    these can be represented by "terms"
        A ⊢ f : B
    when should they be considered equal?
-}
    module quotiented (G : ob GRAPH) where
        open Graph G
        -- with "primitive cuts"
        data _⊢_ : Node →  Node → Type where
            ax : {A B : Node}
                (f : Edge A B)  →
                ---------------
                A ⊢ B
            _●_ : {A B C : Node} →
                (g : B ⊢ C) →
                (f : A ⊢ B) →
                ------------
                A ⊢ C
            id' : {A : Node} →
                --------------
                A ⊢ A

            idr : {A B : Node} →
                (f : A ⊢ B) →
                -------------
                id' ● f ≡ f

            idl : {A B : Node} →
                (f : A ⊢ B) →
                -------------
                f ● id' ≡ f

            assoc : {A B C D : Node } →
                (f : A ⊢ B) →
                (g : B ⊢ C) →
                (h : C ⊢ D) →
                (h ● (g ● f)) ≡ ((h ● g) ● f)

        FreeCat : Category ℓ-zero ℓ-zero
        FreeCat .ob = Node
        FreeCat .Hom[_,_] = _⊢_
        FreeCat .id = id'
        FreeCat ._⋆_ f g = g ● f
        FreeCat .⋆IdL = idl
        FreeCat .⋆IdR = idr
        FreeCat .⋆Assoc = assoc
        FreeCat .isSetHom = {!   !}

    U : Functor CAT GRAPH
    U .F-ob C = record { Node = C .ob ; Edge = C .Hom[_,_] }
    U .F-hom F = record { _$g_ = F .F-ob ; _<$g>_ = F .F-hom }
    U .F-id = GrHom≡  (λ _ → refl) λ _ → refl
    U .F-seq _ _ = GrHom≡  (λ _ → refl) λ _ → refl

    module eff where
        open quotiented
        F : Functor GRAPH CAT
        F .F-ob = FreeCat
        F .F-hom G .F-ob = _$g_ G
        F .F-hom {X}{Y} G .F-hom {x}{y} = goal {x}{y} where
            goal : {x : Graph.Node X}{x' : Graph.Node X} → FreeCat X [ x , x' ] → FreeCat Y [ G $g x , G $g x' ]
            goal (ax f₁) = ax (G <$g> f₁)
            goal (f ● g) = goal f ● goal g
            goal id' = id'
            goal (idr f i) = idr (goal f) i
            goal (idl f i) = idl (goal f) i
            goal (assoc f g h i) = assoc (goal f) (goal g) (goal h) i
        F .F-hom G .F-id = refl
        F .F-hom G .F-seq _ _ = {!   !}
            --cong₂ _●_ (cong₂ {!   !} refl refl) {!   !}
        F .F-id = Functor≡ (λ _ → refl)  (λ _ → {!   !})
        F .F-seq _ _ = Functor≡ ((λ _ → refl)) λ _ → {!   !}

    module _ (G : ob GRAPH)  where        
        open Graph G
        open quotiented G
        module _ {A B C D : Node}{f : Edge A B }{g : Edge B C}{h : Edge C D } where
            foo : A ⊢ D
            foo = ax h ● (ax g ● ax f)

            bar : A ⊢ D
            bar = (ax h ● ax g) ● ax f

            _ : foo  ≡ bar
            _ = assoc (ax f) (ax g) (ax h)

module Cut where
    module _ (G : ob GRAPH)  where
        open Graph G

        -- cut-free category
        -- the "proof relevant" reflexive transitive closure
        data _⊢_ : Node → Node → Type where
            id' :
                {A : Node} →
                --------------
                A ⊢ A
            mor : {A B Γ : Node} →
                (Edge A B) →
                Γ ⊢ A →
                -------
                Γ ⊢ B

        module _ {A B C D : Node}{f : Edge A B }{g : Edge B C}{h : Edge C D } where
            -- exactly ONE term representing the composition of these morphisms
            -- no need for quotienting
            _ : A ⊢ D
            _ = mor h (mor g (mor f id'))

        -- regular composition is a derived notion .. ?
        -- this is just appending lists in a way
        -- composition is ADMISSIBLE
        -- it is not derivable (that would mean that we could use our language to build up the term)
        -- CUT ADMISIBILITY
        -- SUBSTITUTION
        seq : {A B C : Node} → A ⊢ B → B ⊢ C → A ⊢ C
        seq m id' = m
        seq m (mor f n) = mor f (seq m n)

        -- cut ELIMINATION
        {-
            consider the cut free theory
                data _⊢_ : Node → Node → Type where
                    id' :  A ⊢ A
                    mor : Edge A B → Γ ⊢ A → Γ ⊢ B

            with the additional rule (cut)
                    _●_ : B ⊢ C → A ⊢ B → A ⊢ C
           
            IF A ⊢ B has a derivation in the theory WITH (cut) _●_
            THEN it has a derivation in the theory WITHOUT (cut) _●_
        -}

        data _⊢w_ : Node → Node → Type where
            id' : {A : Node} →  A ⊢w A
            mor : {A B Γ : Node} → Edge A B → Γ ⊢w A → Γ ⊢w B
            _●_ : {A B C : Node} → B ⊢w C → A ⊢w B → A ⊢w C

        cut-elim : {A B : Node} → A ⊢w B → A ⊢ B
        cut-elim id' = id'
        cut-elim (mor x x₁) = mor x (cut-elim x₁)
        cut-elim (g ● f) = seq (cut-elim f) (cut-elim g) -- using cut ADMISIBILITY to prove cut ELIMINATION

        {-
            A more category-theoretic way to say what is going on is that
            the morphisms in the free category on a directed graph G
            have an explicit description as finite strings of composable edges in G.
        -}

        -- is this some kind of normalization ..?

        test : {A B : Node} → A ⊢ B → A ⊢w B
        test id' = id'
        test (mor x x₁) = mor x (test x₁)
       
        {-
        open import Cubical.Foundations.Isomorphism
        -- not isomorphic.. but they present equivalent categories ..?
        proof : {A B : Node} → Iso (A ⊢ B) (A ⊢w B)
        proof .Iso.fun = test
        proof .Iso.inv = cut-elim
        proof .Iso.sec = {!   !}
        proof .Iso.ret = {!   !}
        -}

 -}      
-- more suggestive notation
module Unary where
    module _ (G : ob GRAPH)  where
        open Graph G

        data _⊢_ : Node → Node → Type where
            x :
                {A : Node} →
                --------------
                A ⊢ A
            app : {A B Γ : Node} →
                (Edge A B) →
                Γ ⊢ A →
                -------
                Γ ⊢ B

        sub : {A B C : Node} → A ⊢ B → B ⊢ C → A ⊢ C
        sub m x = m
        sub m (app f n) = app f (sub m n)

        subAssoc : {A B C D : Node}{f : A ⊢ B}{g : B ⊢ C}{h : C ⊢ D} →
            sub f (sub g h) ≡ sub (sub f g) h
        subAssoc {f = f} {g} {x} = refl
        subAssoc {f = f} {g} {app h' h} = cong₂ app refl (subAssoc {f = f}{g}{h})

        subidl : {A B  : Node} → (f : A ⊢ B) →   sub x f ≡ f
        subidl x = refl
        subidl (app f m) = cong₂ app refl (subidl m)

        FreeCat : Category ℓ-zero ℓ-zero
        FreeCat .ob = Node
        FreeCat .Hom[_,_] = _⊢_
        FreeCat .id = x
        FreeCat ._⋆_ = sub
        FreeCat .⋆IdL = subidl
        FreeCat .⋆IdR _ = refl
        FreeCat .⋆Assoc f g h = sym (subAssoc {f = f}{g}{h})
        FreeCat .isSetHom = {!   !}
{-
    U : Functor CAT GRAPH
    U .F-ob C = record { Node = C .ob ; Edge = C .Hom[_,_] }
    U .F-hom F = record { _$g_ = F .F-ob ; _<$g>_ = F .F-hom }
    U .F-id = GrHom≡  (λ _ → refl) λ _ → refl
    U .F-seq _ _ = GrHom≡  (λ _ → refl) λ _ → refl

    F : Functor GRAPH CAT
    F .F-ob = FreeCat
    F .F-hom {G}{H} = goal where
        goal : GRAPH [ G , H ] → CAT [ FreeCat G , FreeCat H ]
        goal f .F-ob = f ._$g_
        goal f .F-hom {X}{Y} = go {X}{Y} where
            -- recurse down the list
            go : {X Y : Graph.Node G} → FreeCat G [ X , Y ] → FreeCat H [ f $g X , f $g Y ]
            go x = x
            go (app g m) = app (f ._<$g>_ g) (go m)
        goal f .F-id = refl
        goal f .F-seq = seq  where
            seq : {X Y Z : Graph.Node G} →(g : FreeCat G [ X , Y ]) (h : FreeCat G [ Y , Z ]) → goal f .F-hom ((FreeCat G ⋆ g) h) ≡ (FreeCat H ⋆ goal f .F-hom g) (goal f .F-hom h)
            seq g x = refl
            seq g (app {A} x₁ h) = {!   !} -- cong₂ app refl (seq {!   !} {!   !}) -- (seq g h)
    F .F-id = Functor≡ (λ _ → refl) λ _ → {!  !}
    F .F-seq = {!   !}
 
    -- iso of homsets
    to : {G : ob GRAPH} {C : ob CAT} → CAT [ F ⟅ G ⟆ , C ] → GRAPH [ G , U ⟅ C ⟆ ]
    to F = record { _$g_ = F .F-ob ; _<$g>_ = λ {x = x₁} {y} z → F .F-hom (app z x) }

    fro : {G : ob GRAPH} {C : ob CAT} → GRAPH [ G , U ⟅ C ⟆ ] → CAT [ F ⟅ G ⟆ , C ]
    fro f .F-ob = _$g_ f
    fro {G}{C} f .F-hom = go where
        go : {X Y : ob (FreeCat G)} → (FreeCat G) [ X , Y ] → C [ f $g X , f $g Y ]
        go x = C .id
        go (app g m) = go m ⋆⟨ C ⟩ f ._<$g>_ g
    fro f .F-id = refl
    fro {G}{C} f .F-seq m x = sym (C .⋆IdR _)
    fro f .F-seq m (app x₁ n) = {!   !}

    -- Example program in unary type theory
    data Nodes : Type where
        A B X : Nodes

    open import Cubical.Data.Unit
    open import Cubical.Data.Empty
    open import Cubical.Data.Bool
    open import Cubical.Data.Nat
    open import Cubical.Categories.Instances.Sets

    Sig : Graph ℓ-zero ℓ-zero
    Sig .Graph.Node = Nodes
    Sig .Graph.Edge X A = Unit
    Sig .Graph.Edge X B = Unit
    Sig .Graph.Edge _ _ = ⊥

    ooh : GRAPH [ Sig , U ⟅ SET _ ⟆ ]
    ooh $g A = Bool , {!   !}
    ooh $g B = ℕ , {!   !}
    ooh $g X = Bool × ℕ , {!   !}
    _<$g>_ ooh {X} {A} tt = fst
    _<$g>_ ooh {X} {B} tt = snd

    prog : F ⟅ Sig ⟆ [ X , B ]
    prog = app tt x

    interp : (SET _) [ (Bool × ℕ , {!   !}) , (ℕ , {!   !}) ]
    interp = fro {Sig}{(SET _)} ooh .F-hom {X}{B} prog

    -- our unary type theory is very weak. but this is still very cool


-- cartesian type theory
module cartesian where  
    module _ (G : ob GRAPH)  where
        open Graph G

        data Ty : Type where
            ∣_∣ : Node → Ty
            one : Ty
            _⊗_ : Ty → Ty → Ty


        data _⊢_ : Ty → Ty → Type where
            id' :
                (X : Ty) →
                --------
                X ⊢ X
            mor :
                {X : Ty} →
                {A B : Node} →
                Edge A B →
                X ⊢ ∣ A ∣ →
                --------
                X ⊢ ∣ B ∣
            * :
                (X : Ty) →
                ----------
                X ⊢ one

            ⟨_,,_⟩ :
                {X A B : Ty} →
                X ⊢ A →
                X ⊢ B →
                -------
                X ⊢ (A ⊗ B)
            π₁ :        
                {X A B : Ty} →
                X ⊢ (A ⊗ B) →
                -------------
                X ⊢ A
            π₂ :        
                {X A B : Ty} →
                X ⊢ (A ⊗ B) →
                -------------
                X ⊢ B
            -- laws
            η* :
                {X : Ty} →
                (M : X ⊢ one) →
                ---------------
                * X ≡ M
                   
            β×₁ :
                {X A B : Ty} →
                (M : X ⊢ A) →
                (N : X ⊢ B) →
                ---------------
                π₁ ⟨ M ,, N ⟩ ≡ M
           
            β×₂ :
                {X A B : Ty} →
                (M : X ⊢ A) →
                (N : X ⊢ B) →
                ---------------
                π₂ ⟨ M ,, N ⟩ ≡ N

            η× :                
                {X A B : Ty} →
                (M : X ⊢ (A ⊗ B)) →
                ---------------
                ⟨ π₁ M ,, π₂ M ⟩ ≡ M

            squash : {A B : Ty} → isSet (A ⊢ B)

        sub : {A B C : Ty} → A ⊢ B → B ⊢ C → A ⊢ C
        sub m (id' X) = m
        sub m (mor x n) = mor x (sub m n)
        sub m (* X) = * _
        sub m ⟨ n ,, n₁ ⟩ = ⟨ sub m n ,, sub m n₁ ⟩
        sub m (π₁ n) = π₁ (sub m n)
        sub m (π₂ n) = π₂ (sub m n)
        sub m (η* n i) = η* (sub m n) i
        sub m (β×₁ n n₁ i) = β×₁ (sub m n) (sub m n₁) i
        sub m (β×₂ n n₁ i) = β×₂ (sub m n) (sub m n₁) i
        sub m (η× n i) = η× (sub m n) i
        sub m (squash d d₁ x y i i₁) = squash (sub m d) (sub m d₁) (cong₂ sub refl x) ((cong₂ sub refl y)) i i₁

        subAssoc : {A B C D : Ty} → (f : A ⊢ B)(g : B ⊢ C)(h : C ⊢ D) →
         sub f (sub g h) ≡ sub (sub f g) h
        subAssoc f g (id' X) = refl
        subAssoc f g (mor x h) = cong₂ mor refl (subAssoc f g h)
        subAssoc f g (* X) = refl
        subAssoc f g ⟨ h ,, h₁ ⟩ = cong₂ ⟨_,,_⟩ (subAssoc f g h) (subAssoc f g h₁)
        subAssoc f g (π₁ h) = cong π₁ (subAssoc f g h)
        subAssoc f g (π₂ h) = cong π₂ (subAssoc f g h)
        subAssoc f g (η* h i) = {! cong η* ?  !}
            --squash (sub f (sub g (η* h i))) (sub (sub f g) (η* h i)) {!   !} _ i
        subAssoc f g (β×₁ h h₁ i) = squash _ _ {!   !} _ i
            -- squash (sub f (sub g (β×₁ h h₁ i))) (sub (sub f g) (β×₁ h h₁ i)) _ _ i
        subAssoc f g (β×₂ h h₁ i) = {!   !} -- isProp→PathP (λ i → squash _ _) refl refl i
            --squash (sub f (sub g (β×₂ h h₁ i))) (sub (sub f g) (β×₂ h h₁ i)) _ _ i
        subAssoc f g (η× h i) = {!   !}
            --squash (sub f (sub g (η× h i))) (sub (sub f g) (η× h i)) _ _ i

        open import Cubical.Categories.Limits.Cartesian.Base
        open CartesianCategory hiding (π₁ ; π₂)
        open import Agda.Builtin.Unit

        cat : Category ℓ-zero ℓ-zero
        cat .ob = Ty
        cat .Hom[_,_] = _⊢_
        cat .id = id' _
        cat ._⋆_ = sub
        cat .⋆IdL = {!   !}
        cat .⋆IdR _ = refl
        cat .⋆Assoc f g h = sym (subAssoc f g h)
        cat .isSetHom = squash

        FreeCartCat : CartesianCategory ℓ-zero ℓ-zero
        FreeCartCat .C = cat
        FreeCartCat .term = record {
            vertex = one ;
            element = tt ;
            universal = λ A → record {
                equiv-proof = λ {tt → ((* A) , refl) , λ { (M , prf) → ΣPathP (η* M , refl) } }} }
        FreeCartCat .bp (A , B) = record {
            vertex = A ⊗ B ;
            element = π₁ (id' _) , π₂ (id' _) ;
            universal = λ C → record {
                equiv-proof = λ (m , n) → (⟨ m ,, n ⟩ , ΣPathP (β×₁ m n , β×₂ m n)) ,
                    λ{(p , q) → ΣPathP ( {!   !} ∙ η× p , {!   !}) }} }


        U : Functor {!   !} {!   !}
        U = {!   !}
-}
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct

module CBPVProf where
  module _ (V C : ob GRAPH) where
    module V = Graph V
    module C = Graph C
    VTy = V.Node
    CTy = C.Node

    open Unary
    𝓥 : Category ℓ-zero ℓ-zero
    𝓥 = FreeCat V

    𝓒 : Category ℓ-zero ℓ-zero
    𝓒 = FreeCat C

    data _⊢o_ : VTy → CTy → Type where
      -- want this to be admissible?
      appo : {A A' : VTy}{B B' : CTy} →
        𝓥 [ A' , A ] →
        𝓒 [ B , B' ] →
        A ⊢o B →
        --------
        A' ⊢o B'


    𝓞 : Functor ((𝓥 ^op) ×C 𝓒) (SET ℓ-zero)
    𝓞 .F-ob (A , B) = (A ⊢o B) , {!   !}
    𝓞 .F-hom {(A , B)}{(A' , B')}(f , g) = appo f g
    𝓞 .F-id = {!   !}
    𝓞 .F-seq = {!   !}
