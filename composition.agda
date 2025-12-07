open import Data.Product
open import Data.Nat renaming (ℕ to nat)
open import Data.Vec

open import main

sub-dec : {metas : nat} -> (ts : Vec term metas) -> (p : pat metas) -> Σ[ t ∈ term ] sub-eq ts p t
sub-dec = {!   !}

-- compose-dec : {metas metas' : nat} -> (ps : Vec (pat metas) metas') -> (p : pat metas') -> Σ[ p' ∈ pat metas ] compose-eq ps p p' 
-- compose-dec = {!   !}

⇒t-trans : ∀{t1 t2 t3} -> t1 ⇒t t2 -> t2 ⇒t t3 -> t1 ⇒t t3
⇒t-trans h1 id⇒t = h1
⇒t-trans h1 (step⇒t h2 step) = step⇒t (⇒t-trans h1 h2) step

⇒∘-trans : ∀{metas} -> {p1 p2 p3 : pat metas} -> p1 ⇒∘ p2 -> p2 ⇒∘ p3 -> p1 ⇒∘ p3
⇒∘-trans {metas} {p1} {p2} {p3} (c⇒∘ h1) (c⇒∘ h2) = c⇒∘ body
    where 
    body : (ts : Vec term metas) (t1 t2 : term) → sub-eq ts p1 t1 → sub-eq ts p3 t2 → t1 ⇒t t2
    body ts t1 t3 sub1 sub3 with sub-dec ts p2 
    ... | t2 , sub2 = ⇒t-trans (h1 ts t1 t2 sub1 sub2) (h2 ts t2 t3 sub2 sub3)

comp⇒∘ : ∀{metas metas'} -> {p1 p2 : pat metas} -> {ps : Vec (pat metas') metas} -> {p1' p2' : pat metas'} ->
    p1 ⇒∘ p2 -> 
    compose-eq ps p1 p1' -> 
    compose-eq ps p2 p2' -> 
    p1' ⇒∘ p2'
comp⇒∘ h comp1 comp2 = {!   !}

composition : ∀{metas} -> 
    {p1 p2 p3 p4 : pat metas} -> 
    ∀{metas'} -> 
    {p : pat metas'} -> 
    {ps2 ps3 : Vec (pat metas') metas} ->
    {p1' p4' : pat metas'} ->
    (p1 ⇒∘ p2) ->
    (p3 ⇒∘ p4) -> 
    (unifies p2 p3 p ps2 ps3) -> 
    (compose-eq ps2 p1 p1') -> 
    (compose-eq ps3 p4 p4') -> 
    (p1' ⇒∘ p4')
composition  {p1' = p1'} {p4' = p4'} ⇒∘12 ⇒∘34 (c-unifies comp2 comp3) comp1 comp4 = ⇒∘-trans (comp⇒∘ ⇒∘12 comp1 comp2) (comp⇒∘ ⇒∘34 comp3 comp4)