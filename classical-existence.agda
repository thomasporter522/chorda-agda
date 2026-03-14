{-# OPTIONS --rewriting #-}


open import Data.Nat
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable hiding (map)

open import core

postulate 
    aem : (A : Set) -> A ⊎ (A -> ⊥) 


-- can I prove this nonconstructively?
-- check if the unifier is most general 
-- if so, done
-- otherwise, take a counterexample unifier' 
-- find a place of disagreement between the two 
-- generalize accordingly, and repeat
-- ?

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2

generalization {p1} {p2} {s1} {s2} (Unify u) with aem 
    ((s1' s2' : Sub) 
    -> s1' , s2' unifies p1 , p2
    -> (s1' ⊑ s1 × s2' ⊑ s2))
generalization {p1} {p2} {s1} {s2} (Unify u) | inj₁ mgu = s1 , s2 , MGU (Unify u) mgu
generalization {p1} {p2} {s1} {s2} (Unify u) | inj₂ counter with aem 
    (∃[ s1' ] ∃[ s2' ] s1' , s2' unifies p1 , p2 × ((s1' ⊑ s1) × (s2' ⊑ s2) -> ⊥))
... | inj₁ x = {!   !}
... | inj₂ y = {!   !} -- abort somehow

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2)
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r
existence (Step t1 t2 p1 p2 f1 s1 refl refl) (Step .t2 t3 p3 p4 f2 s2 eq refl) with generalization (Unify {s1} {s2} {p2} {p3} eq)
... | s1' , s2' , mgu = ((s1' [ p1 ]) ↦ (s2' [ p4 ]) [ ∘r-functional p1 p2 p3 p4 f1 f2 s1' s2' mgu ]) , (Comp f1 f2 s1' s2' mgu)