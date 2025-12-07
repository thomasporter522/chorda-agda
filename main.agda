
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)
-- open import Relation.Nullary
-- open import Data.Product
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
    T : (arity : nat) -> (k : K arity) -> Vec term arity -> term

-- type of term patterns of a certain number of metavariables
data pat (metas : nat) : Set where
    T : (arity : nat) -> (k : K arity) -> Vec (pat metas) arity -> pat metas 
    X : Fin metas -> pat metas

postulate 
    _⇒_ : {metas : nat} -> (p1 p2 : pat metas) -> Set 


