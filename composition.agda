open import Data.Product hiding (map)
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import main

⇒-trans : ∀{metas} -> {p1 p2 p3 : pat metas} -> p1 ⇒ p2 -> p2 ⇒ p3 -> p1 ⇒ p3
⇒-trans h1 id⇒ = h1
⇒-trans h1 (step⇒ h2 step) = step⇒ (⇒-trans h1 h2) step

compose-dec : {metas metas' : nat} -> (ps : Vec (pat metas) metas') -> (p : pat metas') -> Σ[ p' ∈ pat metas ] compose-eq ps p p' 
compose-dec = {!   !}

compose-unicity : ∀{metas metas'} -> {p : pat metas} -> {ps : Vec (pat metas') metas} -> {p1 p2 : pat metas'} ->
    compose-eq ps p p1 ->
    compose-eq ps p p2 ->
    p1 ≡ p2
compose-unicity = {!   !}

comp⇒1 : ∀{metas metas'} -> {p1 p2 : pat metas} -> {ps : Vec (pat metas') metas} -> {p1' p2' : pat metas'} ->
    p1 ⇒1 p2 -> 
    compose-eq ps p1 p1' -> 
    compose-eq ps p2 p2' -> 
    p1' ⇒1 p2'
comp⇒1 {ps = ps} (c⇒1 p1'' p2'' ps' comp1' comp2' step) comp1 comp2 with multicompose-dec ps' ps
... | thing = c⇒1 p1'' p2'' {!   !} {!   !} {!   !} step

comp⇒ : ∀{metas metas'} -> {p1 p2 : pat metas} -> {ps : Vec (pat metas') metas} -> {p1' p2' : pat metas'} ->
    p1 ⇒ p2 -> 
    compose-eq ps p1 p1' -> 
    compose-eq ps p2 p2' -> 
    p1' ⇒ p2'
comp⇒ id⇒ comp1 comp3 rewrite (compose-unicity comp1 comp3) = id⇒
comp⇒ {ps = ps} (step⇒ {p1} {p2} steps step) comp1 comp3 with compose-dec ps p2
... | _ , comp2 = step⇒ (comp⇒ steps comp1 comp2) (comp⇒1 step comp2 comp3)

composition : ∀{metas} -> 
    {p1 p2 p3 p4 : pat metas} -> 
    ∀{metas'} -> 
    {p : pat metas'} -> 
    {ps2 ps3 : Vec (pat metas') metas} ->
    {p1' p4' : pat metas'} ->
    (p1 ⇒ p2) ->
    (p3 ⇒ p4) -> 
    (unifies p2 p3 p ps2 ps3) -> 
    (compose-eq ps2 p1 p1') -> 
    (compose-eq ps3 p4 p4') -> 
    (p1' ⇒ p4')
composition {p1' = p1'} {p4' = p4'} ⇒12 ⇒34 (c-unifies comp2 comp3) comp1 comp4 = ⇒-trans (comp⇒ ⇒12 comp1 comp2) (comp⇒ ⇒34 comp3 comp4)