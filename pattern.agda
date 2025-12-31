
open import Data.Product
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
-- open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary using (Decidable)

open import Language

module Pattern ((Language K _b⇒1_) : language) where

    pat : nat -> Set 
    pat = kpat K

    sub : nat -> nat -> Set
    sub metas metas' = Vec (pat metas') metas

    term : Set 
    term = pat zero

    data index-eq {A : Set} : ∀{n} -> Vec A n -> Fin n -> A -> Set where 
        zero-index-eq : ∀{a n} -> {v : Vec A n} -> index-eq (a ∷ v) zero a
        suc-index-eq : ∀{a a' n} -> {v : Vec A (suc n)} -> {x : Fin (suc n)} -> 
            index-eq v x a ->
            index-eq (a' ∷ v) (suc x) a
            
    mutual

        multisubst-eq : ∀{arity metas metas'} ->
            sub metas metas' -> 
            Vec (pat metas) arity -> 
            Vec (pat metas') arity -> 
            Set
        multisubst-eq {arity} {metas} {metas'} s ps ps' = 
            (i : Fin arity) -> 
            (c : pat metas) -> 
            (c' : pat metas') -> 
            index-eq ps i c -> 
            index-eq ps' i c' -> 
            subst-eq s c c'

        data subst-eq {metas metas' : nat} (s : sub metas metas') : (p : pat metas) -> (pat metas') -> Set where 
            X-subst-eq : ∀{x p} ->
                index-eq s x p -> 
                subst-eq s (X x) p
            T-subst-eq : ∀{arity} -> {k : K arity} -> {ps : Vec (pat metas) arity} -> {ps' : Vec (pat metas') arity} ->
                multisubst-eq s ps ps' ->
                subst-eq s (T k ps) (T k ps')

    data _⊒_ {metas metas' : nat} (p1 : pat metas) (p2 : pat metas') : Set where
        Refine : (s : sub metas metas') -> subst-eq s p1 p2 -> p1 ⊒ p2
    
    data lb {metas1 metas2 metas : nat} (p1 : pat metas1) (p2 : pat metas2) (p : pat metas) : Set where
        LB : p1 ⊒ p -> p2 ⊒ p -> lb p1 p2 p
    
    data _⊓_≡_ {metas1 metas2 metas : nat} (p1 : pat metas1) (p2 : pat metas2) (p : pat metas) : Set where 
        GLB : lb p1 p2 p -> 
            (∀{metas'} -> (p' : pat metas') -> lb p1 p2 p' -> p ⊒ p') ->
            p1 ⊓ p2 ≡ p

    -- single steps
    data _⇒1_ {metas : nat} (p1 p2 : pat metas) : Set where
        c⇒1 : {metas' : nat} -> 
            (p1' p2' : pat metas') -> 
            (s : sub metas' metas) -> 
            (subst-eq s p2' p2) -> 
            (subst-eq s p1' p1) -> 
            p1' b⇒1 p2' -> 
            p1 ⇒1 p2

    -- steps
    data _⇒_ {metas : nat} : (p1 p2 : pat metas) -> Set where
        id⇒ : {p : pat metas} -> p ⇒ p
        step⇒ : {p1 p2 p3 : pat metas} -> p1 ⇒ p2 -> p2 ⇒1 p3 -> p1 ⇒ p3

    -- data unifies {metas metas' : nat} (p1 p2 : pat metas) (p : pat metas') (ps1 ps2 : Vec (pat metas') metas) : Set where 
    --     c-unifies : 
    --         (subst-eq ps1 p1 p) -> 
    --         (subst-eq ps2 p2 p) -> 
    --         unifies p1 p2 p ps1 ps2