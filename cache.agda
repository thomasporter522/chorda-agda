
open import Data.Product
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)

open import Language

module Cache ((Language K _b⇒1_) : language) where

    -- open import Pattern (Language K _b⇒1_)

    pat : nat -> Set 
    pat = kpat K

    record cache : Set₁ where 
        field
            -- learned rules
            _⇒_ : {metas : nat} -> (p1 p2 : pat metas) -> Set
            