open import Data.Vec

open import main

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
composition = {!   !}