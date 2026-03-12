{-# OPTIONS --rewriting #-}


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
metric s1 s2 p1 p2 = size-diff s1 p1 + size-diff s2 p2

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

mutual 
    equiv-constructors-sym : ∀{n} 
        -> {ps1 ps2 : Vec Pattern n}
        -> equiv-constructors ps1 ps2
        -> equiv-constructors ps2 ps1
    equiv-constructors-sym {zero} {[]} {[]} ecs = tt
    equiv-constructors-sym {suc _} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) = equiv-constructor-sym ec , equiv-constructors-sym ecs

    equiv-constructor-sym : ∀{p1 p2}
        -> equiv-constructor p1 p2 
        -> equiv-constructor p2 p1
    equiv-constructor-sym ECX = ECX
    equiv-constructor-sym (ECK ecs) = ECK (equiv-constructors-sym ecs)

mutual 
    equiv-constructors-trans : ∀{n} 
        -> {ps1 ps2 ps3 : Vec Pattern n}
        -> equiv-constructors ps1 ps2
        -> equiv-constructors ps2 ps3
        -> equiv-constructors ps1 ps3
    equiv-constructors-trans {zero} {[]} {[]} {[]} _ _ = tt
    equiv-constructors-trans {suc _} {p1 ∷ ps1} {p2 ∷ ps2} {p3 ∷ ps3} (ec1 , ecs1) (ec2 , ecs2) = (equiv-constructor-trans ec1 ec2) , equiv-constructors-trans ecs1 ecs2

    equiv-constructor-trans : ∀{p1 p2 p3}
        -> equiv-constructor p1 p2 
        -> equiv-constructor p2 p3
        -> equiv-constructor p1 p3
    equiv-constructor-trans ECX ECX = ECX
    equiv-constructor-trans (ECK ecs1) (ECK ecs2) = ECK (equiv-constructors-trans ecs1 ecs2)

mutual 
    size-diff-zero-map : ∀{n}
        -> (s : Sub)
        -> (ps : Vec Pattern n)
        -> sum (map (size-diff s) ps) ≡ zero
        -> equiv-constructors ps (map (_[_] s) ps)
    size-diff-zero-map s [] eq = tt
    size-diff-zero-map s (p ∷ ps) eq1 with size-diff s p in eq2
    ... | zero = size-diff-zero s p eq2 , size-diff-zero-map s ps eq1

    size-diff-zero : (s : Sub)
        -> (p : Pattern)
        -> size-diff s p ≡ zero
        -> equiv-constructor p (s [ p ]) 
    size-diff-zero s (X x) eq with s x 
    size-diff-zero s (X x) eq | X _ = ECX
    size-diff-zero s (K k n ps) eq = ECK (size-diff-zero-map s ps eq)


generalization-equiv-constructor : ∀{p1 p2}
    -> equiv-constructor p1 p2
    -> ∃[ s1 ] ∃[ s2 ] s1 , s2 mgu p1 , p2
generalization-equiv-constructor = {!   !}

data SplitResult (p1 p2 : Pattern) : Set where
    SplitEC : equiv-constructor p1 p2
        -> SplitResult p1 p2
    SplitXK : (x : Var)
        -> (k : Constructor)
        -> (n : ℕ)
        -> (ps : Vec Pattern n) 
        -- -> and more things, as needed
        -> SplitResult p1 p2

mutual 

    splitters : ∀{s1 s2 p1 p2}
            -- -> s1 , s2 unifies p1 , p2
            -> SplitResults p1 p2 

    splitter : ∀{s1 s2 p1 p2}
            -> s1 , s2 unifies p1 , p2
            -> SplitResult p1 p2 
    splitter {s1} {s2} {X _} {X _} u = SplitEC ECX
    splitter {s1} {s2} {K k1 n1 ps1} {K k2 n2 ps2} u = {!   !}
    splitter {s1} {s2} {X x} {K x₁ n x₂} u = {!   !}
    splitter {s1} {s2} {K x n x₁} {X x₂} u = {!   !}

generalization-sized : ∀{s1 s2 p1 p2}
    -> (n : ℕ)
    -> metric s1 s2 p1 p2 ≡ n
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization-sized {s1} {s2} {p1} {p2} zero eq uni with size-diff s1 p1 in eq1 | size-diff s2 p2 in eq2
generalization-sized {s1} {s2} {p1} {p2} zero eq uni | zero | zero with size-diff-zero s1 p1 eq1 | size-diff-zero s2 p2 eq2
generalization-sized zero eq (Unify u) | zero | zero | ec1 | ec2 rewrite u = generalization-equiv-constructor (equiv-constructor-trans ec1 (equiv-constructor-sym ec2))
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq uni = {!   !}

--     generalization-equiv-constructor ECX
-- generalization-sized {s1} {s2} {K k1 n1 ps1} {K k2 n2 ps2} (suc n) eq (Unify u) = {! n2  !}
-- generalization-sized {s1} {s2} {X x} {K x₁ n₁ x₂} (suc n) eq uni = {!   !}
-- generalization-sized {s1} {s2} {K x n₁ x₁} {X x₂} (suc n) eq uni = {!   !}

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization = generalization-sized _ refl

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2)
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r
existence (Step t1 t2 p1 p2 f1 s1 refl refl) (Step .t2 t3 p3 p4 f2 s2 eq refl) with generalization (Unify {s1} {s2} {p2} {p3} eq)
... | s1' , s2' , mgu = ((s1' [ p1 ]) ↦ (s2' [ p4 ]) [ ∘r-functional p1 p2 p3 p4 f1 f2 s1' s2' mgu ]) , (Comp f1 f2 s1' s2' mgu)