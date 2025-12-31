open import Data.Product hiding (map)
open import Data.Nat renaming (ℕ to nat) hiding (_⊓_)
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Language

module Composition ((Language K _b⇒1_) : language) where

open import Pattern (Language K _b⇒1_)










-- data CompositionResult {metasL metasR : nat} (p1 p2 : pat metasL) (p3 p4 : pat metasR) : Set where 
--     CR : {metas' : nat} ->
--         (p' : pat metas') -> 
--         (pL : pat metas') -> 
--         (pR : pat metas') -> 
--         (sL : sub metasL metas') -> 
--         (sR : sub metasR metas') ->
--         p2 ⊓ p3 ≡ p' -> 
--         subst-eq sL p2 p' -> 
--         subst-eq sR p3 p' -> 
--         subst-eq sL p1 pL -> 
--         subst-eq sR p4 pR -> 
--         pL ⇒ pR -> 
--         CompositionResult p1 p2 p3 p4


-- composition : ∀{metasL metasR metas} -> 
--     (p1 p2 : pat metasL) -> 
--     (p3 p4 : pat metasR) -> 
--     (p : pat metas) -> 
--     lb p2 p3 p -> 
--     p1 ⇒ p2 ->
--     p3 ⇒ p4 ->
--     CompositionResult p1 p2 p3 p4
-- composition p1 p2 p3 p4 p l step1 step2 = {!   !}