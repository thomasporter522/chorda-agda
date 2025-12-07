open import Data.Product hiding (map)
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
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

multisub : ∀{metas metas'} ->
    Vec (pat metas') metas -> 
    Vec term metas' -> 
    Vec term metas
multisub ps ts = map (λ p → proj₁ (sub-dec ts p)) ps


index-map : ∀{n B} -> {A : Set} -> {a : A} -> {x : Fin n} -> {as : Vec A n} ->
    (f : A -> B) -> 
    index-eq as x a -> 
    index-eq (map f as) x (f a)
index-map = {!   !}

sub-multisub : ∀{metas metas' t ts} -> {p : pat metas} -> {ps : Vec (pat metas') metas} -> {p' : pat metas'} ->
    compose-eq ps p p' -> 
    sub-eq ts p' t -> 
    sub-eq (multisub ps ts) p t
sub-multisub (X-compose-eq i) sub = X-sub-eq (index-map ((λ p → proj₁ (sub-dec {!   !} p))) i)
sub-multisub (T-compose-eq x) sub = {!   !}

comp⇒∘ : ∀{metas metas'} -> {p1 p2 : pat metas} -> {ps : Vec (pat metas') metas} -> {p1' p2' : pat metas'} ->
    p1 ⇒∘ p2 -> 
    compose-eq ps p1 p1' -> 
    compose-eq ps p2 p2' -> 
    p1' ⇒∘ p2'
comp⇒∘ {ps = ps} (c⇒∘ h) comp1 comp2 = c⇒∘ body
    where 
    body : _
    body ts t1 t2 sub1 sub2 with sub-multisub comp1 sub1 | sub-multisub comp2 sub2 
    ... | sub1' | sub2' = h (multisub ps ts) t1 t2 sub1' sub2'

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