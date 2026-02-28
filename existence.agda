open import Data.Nat
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import core

{-# TERMINATING #-}
size : Pattern -> ℕ 
size (X x) = 0
size (K k n ps) = 1 + sum (map size ps)

{-# TERMINATING #-}
size-diff : (s : Sub) -> (p : Pattern) -> ℕ
size-diff s (X x) = size (s x)
size-diff s (K k n ps) = sum (map (size-diff s) ps)

metric : (s1 s2 : Sub) -> (p1 p2 : Pattern) -> ℕ
metric s1 s2 p1 p2 = size-diff s1 p2 + size-diff s2 p2

mutual 
    equiv-constructors : ∀{n} 
        -> (ps1 ps2 : Vec Pattern n) 
        -> Set
    equiv-constructors [] [] = ⊤
    equiv-constructors (p1 ∷ ps1) (p2 ∷ ps2) = equiv-constructor p1 p2 × equiv-constructors ps1 ps2

    data equiv-constructor : (p1 p2 : Pattern) -> Set where 
        ECX : ∀{x1 x2} 
            -> equiv-constructor (X x1) (X x2)
        ECK : ∀{k n ps1 ps2} 
            -> equiv-constructors ps1 ps2
            -> equiv-constructor (K k n ps1) (K k n ps2)

generalization-sized : ∀{s1 s2 p1 p2}
    -> (n : ℕ)
    -> metric s1 s2 p1 p2 ≡ n
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization-sized {s1} {s2} {p1} {p2} zero eq uni with size-diff s1 p2 in eq1 | size-diff s2 p2 in eq2
generalization-sized zero eq uni | zero | zero = {!   !}
generalization-sized (suc n) eq uni = {!   !}

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization = generalization-sized _ refl

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2) 
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r 
existence (Step t1 t2 p1 p2 s1 refl refl) (Step .t2 t3 p3 p4 s2 eq refl) with generalization (Unify {s1} {s2} {p2} {p3} eq)
... | s1' , s2' , mgu = ((s1' [ p1 ]) ↦ (s2' [ p4 ])) , (Comp s1' s2' mgu)
