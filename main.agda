
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)
-- open import Relation.Nullary
open import Data.Product
-- open import Data.Sum renaming (_⊎_ to _+_)
-- open import Data.Empty
-- open import Data.Maybe
-- open import Data.String renaming (_++_ to _++s_)
-- open import Data.Nat.Properties
open import Data.Nat hiding (_≟_) renaming (_+_ to _nat+_) renaming (ℕ to nat)
-- open import Data.Unit hiding (_≟_)
-- open import Data.List hiding (lookup)
open import Data.Fin
open import Data.Vec

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

-- basis pattern steps
data _⇒_ : {metas : nat} -> (p1 p2 : pat metas) -> Set where
    id⇒ : ∀{metas} -> {p : pat metas} -> p ⇒ p
    step⇒ : ∀{metas} -> {p1 p2 p3 : pat metas} -> p1 ⇒ p2 -> p2 ⇒1 p3 -> p1 ⇒ p3

-- term steps
data _⇒t_ (t1 t2 : term) : Set where
    c⇒t : {metas : nat} -> 
        (p1 p2 : pat metas) -> 
        (ts1 ts2 : Vec term metas) -> 
        (sub-eq ts1 p1 t1) -> 
        (sub-eq ts2 p2 t2) -> 
        p1 ⇒ p2 -> 
        t1 ⇒t t2

-- sound pattern steps
data _⇒∘_ {metas : nat} (p1 p2 : pat metas) : Set where
    c⇒∘ : ((ts1 ts2 : Vec term metas) -> 
            ∃[ t1 ] ∃[ t2 ] 
            sub-eq ts1 p1 t1 × 
            sub-eq ts2 p2 t2 × 
            (t1 ⇒t t2)
        ) -> p1 ⇒∘ p2

data compose-eq {metas metas' : nat} (ps : Vec (pat metas) metas') : (p : pat metas') -> (pat metas) -> Set where 

data antiunifies {metas metas' : nat} (p1 p2 : pat metas) (p : pat metas') (ps1 ps2 : Vec (pat metas) metas') : Set where 
    c-antiunifies : 
        (compose-eq ps1 p p1) -> 
        (compose-eq ps2 p p2) -> 
        antiunifies p1 p2 p ps1 ps2

data antiunification {metas : nat} (p1 p2 : pat metas) : Set where 
    c-antiunification : {metas' : nat} ->
        (p : pat metas') ->
        (ps1 ps2 : Vec (pat metas) metas') -> 
        antiunifies p1 p2 p ps1 ps2 -> 
        antiunification p1 p2