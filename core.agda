open import Data.Nat
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

data Rule : Set where 
    _↦_ : Pattern -> Pattern -> Rule

Sub : Set 
Sub = Var -> Pattern

{-# TERMINATING #-}
_[_] : Sub -> Pattern -> Pattern 
s [ X x ] = s x
s [ K k n ps ] = K k n (map (λ p -> (s [ p ])) ps)

infixr 30 _[_]

data _↦[_]_ : Pattern -> Rule -> Pattern -> Set where 
    Step : (t1 t2 p1 p2 : Pattern)
        -> (s : Sub)
        -> t1 ≡ s [ p1 ]
        -> t2 ≡ s [ p2 ]
        -> t1 ↦[ p1 ↦ p2 ] t2

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

data _∘r_≡_ : Rule -> Rule -> Rule -> Set where
    Comp : ∀{p1 p2 p3 p4}
        -> (s1 s2 : Sub)
        -> s1 , s2 mgu p2 , p3 
        -> (p1 ↦ p2) ∘r (p3 ↦ p4) ≡ (s1 [ p1 ] ↦ s2 [ p4 ])

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

