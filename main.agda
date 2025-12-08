
open import Data.Product
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)

postulate 
    -- type of term constructors of a certain arity
    K : nat -> Set

-- type of term patterns of a certain number of metavariables
data pat (metas : nat) : Set where
    T : {arity : nat} -> (k : K arity) -> Vec (pat metas) arity -> pat metas 
    X : Fin metas -> pat metas

data index-eq {A : Set} : ∀{n} -> Vec A n -> Fin n -> A -> Set where 
    zero-index-eq : ∀{a n} -> {v : Vec A n} -> index-eq (a ∷ v) zero a
    suc-index-eq : ∀{a a' n} -> {v : Vec A (suc n)} -> {x : Fin (suc n)} -> 
        index-eq v x a ->
        index-eq (a' ∷ v) (suc x) a
        
mutual

    multicompose-eq : ∀{arity metas metas'} ->
        Vec (pat metas') metas -> 
        Vec (pat metas) arity -> 
        Vec (pat metas') arity -> 
        Set
    multicompose-eq {arity} {metas} {metas'} ps cs cs' = (i : Fin arity) -> (c : pat metas) -> (c' : pat metas') -> index-eq cs i c -> index-eq cs' i c' -> compose-eq ps c c'

    data compose-eq {metas metas' : nat} (ps : Vec (pat metas') metas) : (p : pat metas) -> (pat metas') -> Set where 
        X-compose-eq : ∀{x p} ->
            index-eq ps x p -> 
            compose-eq ps (X x) p
        T-compose-eq : ∀{arity} -> {k : K arity} -> {cs : Vec (pat metas) arity} -> {cs' : Vec (pat metas') arity} ->
            multicompose-eq ps cs cs' ->
            compose-eq ps (T k cs) (T k cs')

postulate 
    -- basis single steps
    _b⇒1_ : {metas : nat} -> (p1 p2 : pat metas) -> Set 

-- single steps
data _⇒1_ {metas : nat} (p1 p2 : pat metas) : Set where
    c⇒1 : {metas' : nat} -> 
        (p1' p2' : pat metas') -> 
        (ps : Vec (pat metas) metas') -> 
        (compose-eq ps p2' p2) -> 
        (compose-eq ps p1' p1) -> 
        p1' b⇒1 p2' -> 
        p1 ⇒1 p2

-- steps
data _⇒_ {metas : nat} : (p1 p2 : pat metas) -> Set where
    id⇒ : {p : pat metas} -> p ⇒ p
    step⇒ : {p1 p2 p3 : pat metas} -> p1 ⇒ p2 -> p2 ⇒1 p3 -> p1 ⇒ p3

data unifies {metas metas' : nat} (p1 p2 : pat metas) (p : pat metas') (ps1 ps2 : Vec (pat metas') metas) : Set where 
    c-unifies : 
        (compose-eq ps1 p1 p) -> 
        (compose-eq ps2 p2 p) -> 
        unifies p1 p2 p ps1 ps2