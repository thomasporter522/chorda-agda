
open import Data.Product
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)

postulate 
    -- type of term constructors of a certain arity
    K : nat -> Set

data term : Set where 
    T : {arity : nat} -> (k : K arity) -> Vec term arity -> term

-- type of term patterns of a certain number of metavariables
data pat (metas : nat) : Set where
    T : {arity : nat} -> (k : K arity) -> Vec (pat metas) arity -> pat metas 
    X : Fin metas -> pat metas

data index-eq {A : Set} : ∀{n} -> Vec A n -> Fin n -> A -> Set where 
    zero-index-eq : ∀{a n} -> {v : Vec A n} -> index-eq (a ∷ v) zero a
    suc-index-eq : ∀{a a' n} -> {v : Vec A (suc n)} -> {x : Fin (suc n)} -> 
        index-eq v x a ->
        index-eq (a' ∷ v) (suc x) a

data sub-eq {metas : nat} (ts : Vec term metas) : (p : pat metas) -> term -> Set where 
    X-sub-eq : ∀{x t} ->
        index-eq ts x t -> 
        sub-eq ts (X x) t
    T-sub-eq : ∀{arity} -> {k : K arity} -> {ps : Vec (pat metas) arity} -> {ts' : Vec term arity} ->
        ((i : Fin arity) -> ∃[ p ] ∃[ t ] index-eq ps i p × index-eq ts' i t × (sub-eq ts p t)) ->
        sub-eq ts (T k ps) (T k ts')

postulate 
    -- basis single pattern steps
    _⇒1_ : {metas : nat} -> (p1 p2 : pat metas) -> Set 

-- single term steps
data _⇒1t_ (t1 t2 : term) : Set where
    c⇒t : {metas : nat} -> 
        (p1 p2 : pat metas) -> 
        (ts1 ts2 : Vec term metas) -> 
        (sub-eq ts1 p1 t1) -> 
        (sub-eq ts2 p2 t2) -> 
        p1 ⇒1 p2 -> 
        t1 ⇒1t t2

-- term steps
data _⇒t_ : (t1 t2 : term) -> Set where
    id⇒t : {t : term} -> t ⇒t t
    step⇒t : {t1 t2 t3 : term} -> t1 ⇒t t2 -> t2 ⇒1t t3 -> t1 ⇒t t3

-- sound pattern steps
data _⇒∘_ {metas : nat} (p1 p2 : pat metas) : Set where
    c⇒∘ : ((ts : Vec term metas) -> 
            (t1 t2 : term) -> 
            sub-eq ts p1 t1 ->
            sub-eq ts p2 t2 -> 
            (t1 ⇒t t2)
        ) -> p1 ⇒∘ p2

data compose-eq {metas metas' : nat} (ps : Vec (pat metas) metas') : (p : pat metas') -> (pat metas) -> Set where 

data unifies {metas metas' : nat} (p1 p2 : pat metas) (p : pat metas') (ps1 ps2 : Vec (pat metas') metas) : Set where 
    c-unifies : 
        (compose-eq ps1 p1 p) -> 
        (compose-eq ps2 p2 p) -> 
        unifies p1 p2 p ps1 ps2

data unification {metas : nat} (p1 p2 : pat metas) : Set where 
    c-unification : {metas' : nat} ->
        (p : pat metas') ->
        (ps1 ps2 : Vec (pat metas') metas) -> 
        unifies p1 p2 p ps1 ps2 -> 
        unification p1 p2