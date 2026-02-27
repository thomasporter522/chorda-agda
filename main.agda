open import Data.Nat
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Product hiding (map)
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
    Step : (p1 p2 : Pattern)
        -> (s : Sub)
        -> s [ p1 ] ↦[ p1 ↦ p2 ] s [ p2 ]

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

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2) 
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r 
existence {t1} {.(s1 [ p2 ])} {.(s2 [ p4 ])} {p1 ↦ p2} {p3 ↦ p4} (Step .p1 .p2 s1) (Step .p3 .p4 s2) = {! step2  !}

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization u = {!   !}