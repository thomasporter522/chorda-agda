{-# OPTIONS --rewriting #-}

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

postulate 
    Constructor : Set
    Var : Set 
    L : Var -> Var 
    R : Var -> Var 
    L-inj : (x y : Var) -> (L x ≡ L y) -> x ≡ y
    R-inj : (x y : Var) -> (R x ≡ R y) -> x ≡ y
    L-R-disjoint : (x y : Var) -> (L x ≡ R y) -> ⊥

data Pattern : Set where 
    X : Var -> Pattern
    K : Constructor -> (n : ℕ) -> Vec Pattern n -> Pattern 

Sub : Set 
Sub = Var -> Pattern

{-# TERMINATING #-}
_[_] : Sub -> Pattern -> Pattern 
s [ X x ] = s x
s [ K k n ps ] = K k n (map (λ p -> (s [ p ])) ps)

infixr 30 _[_]

functional : Pattern -> Pattern -> Set
functional p1 p2 = (s1 s2 : Sub)
    -> s1 [ p1 ] ≡ s2 [ p1 ]
    -> s1 [ p2 ] ≡ s2 [ p2 ]

data Rule : Set where 
    _↦_[_] : (p1 p2 : Pattern) -> functional p1 p2 -> Rule

data _≡r_ : Rule -> Rule -> Set where
    REquiv : ∀{p1 p2 p3 p4 f1 f2}
        -> (s1 s2 : Sub)
        -> s1 [ p1 ] ≡ p3
        -> s1 [ p2 ] ≡ p4
        -> s2 [ p3 ] ≡ p1
        -> s2 [ p4 ] ≡ p2
        -> (p1 ↦ p2 [ f1 ]) ≡r (p3 ↦ p4 [ f2 ])

data _↦[_]_ : Pattern -> Rule -> Pattern -> Set where 
    Step : (t1 t2 p1 p2 : Pattern)
        -> (f : functional p1 p2)
        -> (s : Sub)
        -> t1 ≡ s [ p1 ]
        -> t2 ≡ s [ p2 ]
        -> t1 ↦[ p1 ↦ p2 [ f ] ] t2

_∘_ : Sub -> Sub -> Sub 
(s1 ∘ s2) x = s1 [ s2 x ]

data _⊑_ (s1 s2 : Sub) : Set where 
    Prec : (s : Sub) -> s1 ≡ s ∘ s2 -> s1 ⊑ s2

data _,_unifies_,_ (s1 s2 : Sub) (p1 p2 : Pattern) : Set where
    Unify : s1 [ p1 ] ≡ s2 [ p2 ]
        -> s1 , s2 unifies p1 , p2

data _,_mgu_,_ (s1 s2 : Sub) (p1 p2 : Pattern) : Set where
    MGU : s1 , s2 unifies p1 , p2
        -> ((s1' s2' : Sub) 
            -> s1' , s2' unifies p1 , p2
            -> (s1' ⊑ s1 × s2' ⊑ s2))
        -> s1 , s2 mgu p1 , p2

mutual 
    map-fusion : ∀{s1 s2 n} 
        -> {ps : Vec Pattern n}
        -> map (_[_] s1) (map (_[_] s2) ps) ≡ map (_[_] (s1 ∘ s2)) ps
    map-fusion {ps = []} = refl
    map-fusion {s1} {s2} {ps = p ∷ ps} 
        rewrite ∘-eq s1 s2 p 
        rewrite map-fusion {s1} {s2} {ps = ps} = refl

    ∘-eq : (s1 s2 : Sub)
        -> (p : Pattern)
        -> (s1 ∘ s2) [ p ] ≡ s1 [ s2 [ p ] ]
    ∘-eq _ _ (X x) = refl
    ∘-eq s1 s2 (K k n ps)
        rewrite map-fusion {s1} {s2} {ps = ps} = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ∘-eq #-}

∘r-functional : (p1 p2 p3 p4 : Pattern)
        -> (f1 : functional p1 p2) 
        -> (f2 : functional p3 p4) 
        -> (s1 s2 : Sub)
        -> (mgu : s1 , s2 mgu p2 , p3)
        -> functional (s1 [ p1 ]) (s2 [ p4 ])
∘r-functional p1 p2 p3 p4 f1 f2 s1 s2 (MGU (Unify u) _) s3 s4 eq1 with f1 (s3 ∘ s1) (s4 ∘ s1) eq1 
... | eq2 rewrite u = f2 (s3 ∘ s2) (s4 ∘ s2) eq2

data _∘r_≡_ : Rule -> Rule -> Rule -> Set where
    Comp : ∀{p1 p2 p3 p4}
        -> (f1 : functional p1 p2) 
        -> (f2 : functional p3 p4) 
        -> (s1 s2 : Sub)
        -> (mgu : s1 , s2 mgu p2 , p3)
        -> (p1 ↦ p2 [ f1 ]) ∘r (p3 ↦ p4 [ f2 ]) ≡ (s1 [ p1 ] ↦ s2 [ p4 ] [ ∘r-functional p1 p2 p3 p4 f1 f2 s1 s2 mgu ]) 

-- ∘r-compatible : (r1 r1' r2 r2' r r' : Rule)
--     -> (r1 ≡r r1')
--     -> (r2 ≡r r2')
--     -> r1 ∘r r2 ≡ r
--     -> r1' ∘r r2' ≡ r'
--     -> (r ≡r r')
-- ∘r-compatible 
--     (p1 ↦ p2 [ f1 ]) 
--     (p1' ↦ p2' [ f1' ]) 
--     (p3 ↦ p4 [ f2 ]) 
--     (p3' ↦ p4' [ f2' ])
--     (.(s3 [ p1 ]) ↦ .(s4 [ p4 ]) [ f3 ]) 
--     (.(s3' [ p1' ]) ↦ .(s4' [ p4' ]) [ f3' ]) 
--     (REquiv s1 s2 eq1 eq2 eq3 eq4) 
--     (REquiv s1' s2' eq5 eq6 eq7 eq8) 
--     (Comp .f1 .f2 s3 s4 (MGU (Unify u) mgu)) 
--     (Comp .f1' .f2' s3' s4' (MGU (Unify u') mgu')) 
--     with mgu (s3' ∘ s1) (s4' ∘ s1') (Unify helper1) | mgu' (s3 ∘ s2) (s4 ∘ s2') (Unify helper2)
--     where 
--     helper1 : (s3' ∘ s1) [ p2 ] ≡ (s4' ∘ s1') [ p3 ] 
--     helper1 rewrite eq2 rewrite eq5 = u'
--     helper2 : (s3 ∘ s2) [ p2' ] ≡ (s4 ∘ s2') [ p3' ]
--     helper2 rewrite eq4 rewrite eq7 = u
-- ... | Prec s6 eq9 , Prec s7 eq10 
--     | Prec s8 eq11 , Prec s9 eq12 = REquiv {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}

Ruleset : Set₁ 
Ruleset = Rule -> Set 

data _↦*[_]_ : Pattern -> Ruleset -> Pattern -> Set₁ where 
    Refl : (p : Pattern) 
        -> (R : Ruleset) 
        -> p ↦*[ R ] p
    Cons : ∀{p1 p2 p3 R r}
        -> R r
        -> p1 ↦[ r ] p2
        -> p2 ↦*[ R ] p3
        -> p1 ↦*[ R ] p3

data _↦+[_]_ : Pattern -> Ruleset -> Pattern -> Set₁ where 
    Step : ∀{p1 p2 R r}
        -> R r
        -> p1 ↦[ r ] p2
        -> p1 ↦+[ R ] p2
    Cons : ∀{p1 p2 p3 R r}
        -> R r
        -> p1 ↦[ r ] p2
        -> p2 ↦+[ R ] p3
        -> p1 ↦+[ R ] p3

_↦̸[_] : Pattern -> Ruleset -> Set
p ↦̸[ R ] = (p' : Pattern) 
    -> (r : Rule) 
    -> R r 
    -> p ↦[ r ] p'
    -> ⊥

data _=>[_]_ : Pattern -> Ruleset -> Pattern -> Set₁ where 
    Eval : ∀{p1 p2 R}
        -> p1 ↦*[ R ] p2 
        -> p2 ↦̸[ R ]
        -> p1 =>[ R ] p2

data _≅_ (R1 R2 : Ruleset) : Set₁ where 
    Equiv : (∀{p1 p2} 
            -> p1 =>[ R1 ] p2
            -> p1 =>[ R2 ] p2)
        -> (∀{p1 p2} 
            -> p1 =>[ R2 ] p2
            -> p1 =>[ R1 ] p2)
        -> R1 ≅ R2

_∪[_] : Ruleset -> Rule -> Ruleset 
(R ∪[ r ]) r' = R r' ⊎ r' ≡ r

infixr 30 _∪[_]

data pf : Set₁ where 
    PF : (graph : Pattern -> Pattern -> Set)
        -> (functional : (p1 p2 p3 : Pattern) -> graph p1 p2 -> graph p1 p3 -> p2 ≡ p3)
        -> pf

_≡pf_ : pf -> pf -> Set
PF g1 f1 ≡pf PF g2 f2 = (p1 p2 : Pattern) -> (g1 p1 p2 -> g2 p1 p2) × (g2 p1 p2 -> g1 p1 p2)

data ∘graph (g1 g2 : Pattern -> Pattern -> Set) (p1 p2 : Pattern) : Set where
        G : (p : Pattern)
            -> g1 p1 p
            -> g2 p p2
            -> (∘graph g1 g2) p1 p2

_∘pf_ : pf -> pf -> pf 
PF g1 f1 ∘pf PF g2 f2 = PF (∘graph g1 g2) graph-functional
    where 
    graph-functional : (p1 p2 p3 : Pattern) -> (∘graph g1 g2) p1 p2 -> (∘graph g1 g2) p1 p3 -> p2 ≡ p3
    graph-functional p1 p2 p3 (G p12 g112 g122) (G p13 g113 g133) 
        rewrite f1 p1 p12 p13 g112 g113 
        rewrite f2 p13 p2 p3 g122 g133 = refl
    
∘pf-≡pf : (f1 f2 f1' f2' : pf)
    -> (f1 ≡pf f1')
    -> (f2 ≡pf f2')
    -> ((f1 ∘pf f2) ≡pf (f1' ∘pf f2'))
∘pf-≡pf (PF g1 f1) (PF g2 f2) (PF g1' f1') (PF g2' f2') eq1 eq2 p1 p2 = helper1 , helper2
    where 
    helper1 : ∘graph g1 g2 p1 p2 → ∘graph g1' g2' p1 p2
    helper1 (G p in1 in2) = G p (eq1 p1 p .proj₁ in1) (eq2 p p2 .proj₁ in2)
    helper2 : ∘graph g1' g2' p1 p2 → ∘graph g1 g2 p1 p2
    helper2 (G p in1 in2) = G p (eq1 p1 p .proj₂ in1) (eq2 p p2 .proj₂ in2)


data ⟦⟧graph (p1 p2 p3 p4 : Pattern) : Set where
    G : (s : Sub)
        -> s [ p1 ] ≡ p3
        -> s [ p2 ] ≡ p4
        -> (⟦⟧graph p1 p2) p3 p4

⟦_⟧ : (r : Rule) -> pf 
⟦ p1 ↦ p2 [ f ] ⟧ = PF (⟦⟧graph p1 p2) graph-functional
    where
    graph-functional : (p3 p4 p5 : Pattern) → (⟦⟧graph p1 p2) p3 p4 → (⟦⟧graph p1 p2) p3 p5 → p4 ≡ p5
    graph-functional p3 p4 p5 (G s1 eq1 eq2) (G s2 eq3 eq4) with f s1 s2 (trans eq1 (sym eq3))
    ... | eq5 = trans (sym eq2) (trans eq5 eq4)

⟦⟧-compatible : 
    (r1 r2 : Rule)
    -> r1 ≡r r2 
    -> ⟦ r1 ⟧ ≡pf ⟦ r2 ⟧
⟦⟧-compatible (p1 ↦ p2 [ f1 ]) (p3 ↦ p4 [ f2 ]) (REquiv s1 s2 eq1 eq2 eq3 eq4) p5 p6 = helper1 , helper2
    where 
    helper1 : ⟦⟧graph p1 p2 p5 p6 → ⟦⟧graph p3 p4 p5 p6
    helper1 (G s eq5 eq6) = G (s ∘ s2) subhelper1 subhelper2
        where 
        subhelper1 : (s ∘ s2) [ p3 ] ≡ p5
        subhelper1 rewrite eq3 rewrite eq5 = refl
        subhelper2 : (s ∘ s2) [ p4 ] ≡ p6
        subhelper2 rewrite eq4 rewrite eq6 = refl
    helper2 : ⟦⟧graph p3 p4 p5 p6 → ⟦⟧graph p1 p2 p5 p6
    helper2 (G s eq5 eq6) = G (s ∘ s1) subhelper1 subhelper2
        where 
        subhelper1 : (s ∘ s1) [ p1 ] ≡ p5
        subhelper1 rewrite eq1 rewrite eq5 = refl
        subhelper2 : (s ∘ s1) [ p2 ] ≡ p6
        subhelper2 rewrite eq2 rewrite eq6 = refl