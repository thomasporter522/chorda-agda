
open import Data.Product hiding (map)
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Language

module Composition2 ((Language K _b⇒1_) : language) where

open import Pattern (Language K _b⇒1_)

data composition-result : Set where 


composition :
    {t1 t2 t3 : pat zero} -> 
    (t1 ⇒ t2) -> 
    (t2 ⇒ t3) -> 
    ∃[ metas ]
    Σ[ p1 ∈ pat metas ]
    Σ[ p3 ∈ pat metas ]
    Σ[ ts ∈ Vec (pat zero) metas ]
    (compose-eq ts p1 t1) ×
    (compose-eq ts p3 t3) ×
    (p1 ⇒ p3)

composition = {!   !}