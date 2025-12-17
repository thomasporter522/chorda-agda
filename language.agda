open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec

module Language where

    -- type of term patterns of a certain number of metavariables
    data kpat (K : nat → Set) (metas : nat) : Set where
        T : {arity : nat} → (k : K arity) → Vec (kpat K metas) arity → kpat K metas
        X : Fin metas → kpat K metas

    record language : Set₁ where 
        constructor Language
        field 
            K : nat -> Set -- type of term constructors of a certain arity
            _b⇒1_ : {metas : nat} -> (p1 p2 : kpat K metas) -> Set -- basis single steps