{-# OPTIONS --rewriting #-}


open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Unit
open import Data.Fin hiding (_+_; _<_; _≤_; _>_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable hiding (map)

open import core

{-# TERMINATING #-}
size : Pattern -> ℕ 
size (X x) = 0
size (K k n ps) = 1 + sum (map size ps)

{-# TERMINATING #-}
size-diff : (s : Sub) -> (p : Pattern) -> ℕ
size-diff s (X x) = size (s x)
size-diff s (K k n ps) = sum (map (size-diff s) ps)

metric : (s1 s2 : Sub) -> (p1 p2 : Pattern) -> ℕ
metric s1 s2 p1 p2 = size-diff s1 p1 + size-diff s2 p2

mutual 
    equiv-constructors : ∀{n} 
        -> (ps1 ps2 : Vec Pattern n) 
        -> Set
    equiv-constructors [] [] = ⊤
    equiv-constructors (p1 ∷ ps1) (p2 ∷ ps2) = equiv-constructor p1 p2 × equiv-constructors ps1 ps2

    data equiv-constructor : (p1 p2 : Pattern) -> Set where 
        ECX : ∀{x1 x2} 
            -> equiv-constructor (X x1) (X x2)
        ECK : ∀{k n ps1 ps2} 
            -> equiv-constructors ps1 ps2
            -> equiv-constructor (K k n ps1) (K k n ps2)

mutual 
    equiv-constructors-sym : ∀{n} 
        -> {ps1 ps2 : Vec Pattern n}
        -> equiv-constructors ps1 ps2
        -> equiv-constructors ps2 ps1
    equiv-constructors-sym {zero} {[]} {[]} ecs = tt
    equiv-constructors-sym {suc _} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) = equiv-constructor-sym ec , equiv-constructors-sym ecs

    equiv-constructor-sym : ∀{p1 p2}
        -> equiv-constructor p1 p2 
        -> equiv-constructor p2 p1
    equiv-constructor-sym ECX = ECX
    equiv-constructor-sym (ECK ecs) = ECK (equiv-constructors-sym ecs)

mutual 
    equiv-constructors-trans : ∀{n} 
        -> {ps1 ps2 ps3 : Vec Pattern n}
        -> equiv-constructors ps1 ps2
        -> equiv-constructors ps2 ps3
        -> equiv-constructors ps1 ps3
    equiv-constructors-trans {zero} {[]} {[]} {[]} _ _ = tt
    equiv-constructors-trans {suc _} {p1 ∷ ps1} {p2 ∷ ps2} {p3 ∷ ps3} (ec1 , ecs1) (ec2 , ecs2) = (equiv-constructor-trans ec1 ec2) , equiv-constructors-trans ecs1 ecs2

    equiv-constructor-trans : ∀{p1 p2 p3}
        -> equiv-constructor p1 p2 
        -> equiv-constructor p2 p3
        -> equiv-constructor p1 p3
    equiv-constructor-trans ECX ECX = ECX
    equiv-constructor-trans (ECK ecs1) (ECK ecs2) = ECK (equiv-constructors-trans ecs1 ecs2)

mutual 
    size-diff-zero-map : ∀{n}
        -> (s : Sub)
        -> (ps : Vec Pattern n)
        -> sum (map (size-diff s) ps) ≡ zero
        -> equiv-constructors ps (map (_[_] s) ps)
    size-diff-zero-map s [] eq = tt
    size-diff-zero-map s (p ∷ ps) eq1 with size-diff s p in eq2
    ... | zero = size-diff-zero s p eq2 , size-diff-zero-map s ps eq1

    size-diff-zero : (s : Sub)
        -> (p : Pattern)
        -> size-diff s p ≡ zero
        -> equiv-constructor p (s [ p ]) 
    size-diff-zero s (X x) eq with s x 
    size-diff-zero s (X x) eq | X _ = ECX
    size-diff-zero s (K k n ps) eq = ECK (size-diff-zero-map s ps eq)

mutual 
    locations : ∀{n} 
        -> {ps1 ps2 : Vec Pattern n}
        -> (ecs : equiv-constructors ps1 ps2)
        -> Set
    locations {n} {[]} ecs = ⊥
    locations {n} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) = location ec ⊎ locations ecs

    location : {p1 p2 : Pattern} -> (ec : equiv-constructor p1 p2) -> Set
    location ECX = ⊤
    location (ECK ecs) = locations ecs

mutual 
    gets-xs : ∀{n} 
        -> {ps1 ps2 : Vec Pattern n}
        -> (ecs : equiv-constructors ps1 ps2)
        -> (l : locations ecs)
        -> Var × Var
    gets-xs {n} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) (inj₁ l) = get-xs ec l
    gets-xs {n} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) (inj₂ ls) = gets-xs ecs ls

    get-xs : {p1 p2 : Pattern} 
        -> (ec : equiv-constructor p1 p2)
        -> (l : location ec)
        -> Var × Var
    get-xs {X x1} {X x2} ECX tt = x1 , x2
    get-xs {K k n ps1} {K k n ps2} (ECK ecs) ls = gets-xs ecs ls


-- two locations are equivalent if they either agree on the left pattern or agree on the right pattern
≡l1 : {p1 p2 : Pattern} 
    -> (ec : equiv-constructor p1 p2)
    -> (l1 l2 : location ec)
    -> Set 
≡l1 ec l1 l2 with get-xs ec l1 | get-xs ec l2 
≡l1 ec l1 l2 | x11 , x12 | x21 , x22 = (x11 ≡ x21) ⊎ (x12 ≡ x22)

data ≡l : {p1 p2 : Pattern} 
    -> (ec : equiv-constructor p1 p2)
    -> (l1 l2 : location ec)
    -> Set where 

    ≡l-refl : {p1 p2 : Pattern} 
        -> (ec : equiv-constructor p1 p2)
        -> (l1 : location ec)
        -> ≡l ec l1 l1  

    ≡l-cons : {p1 p2 : Pattern} 
        -> (ec : equiv-constructor p1 p2)
        -> (l1 l2 l3 : location ec)
        -> ≡l ec l1 l2  
        -> ≡l1 ec l2 l3
        -> ≡l ec l1 l3

surjection : {A B : Set} -> (f : A -> B) -> Set 
surjection {A} {B} f = (b : B) -> ∃[ a ] (f a ≡ b)

postulate
    sum-fin : (n1 n2 : ℕ)
        -> (Fin (n1 + n2)) ≅ (Fin n1 ⊎ Fin n2)
    -- _≅_.to (sum-fin zero n2) a = inj₂ a
    -- _≅_.from (sum-fin zero n2) (inj₂ y) = y
    -- _≅_.fromto (sum-fin zero n2) = refl
    -- _≅_.tofrom (sum-fin zero n2) {inj₂ y} = refl
    -- _≅_.to (sum-fin (suc n1) n2) zero = inj₁ zero
    -- _≅_.to (sum-fin (suc n1) n2) (suc a) with _≅_.to (sum-fin n1 n2) a
    -- ... | inj₁ x = inj₁ (suc x)
    -- ... | inj₂ y = inj₂ y
    -- _≅_.from (sum-fin (suc n1) n2) (inj₁ zero) = zero
    -- _≅_.from (sum-fin (suc n1) n2) (inj₁ (suc x)) = suc (_≅_.from (sum-fin n1 n2) (inj₁ x))
    -- _≅_.from (sum-fin (suc n1) n2) (inj₂ y) = suc (_≅_.from (sum-fin n1 n2) (inj₂ y))
    -- _≅_.fromto (sum-fin (suc n1) n2) {zero} = refl
    -- _≅_.fromto (sum-fin (suc n1) n2) {suc a} with _≅_.to (sum-fin n1 n2) a
    -- ... | inj₁ x = {!   !}
    -- ... | inj₂ y = {!   !}
    -- _≅_.tofrom (sum-fin (suc n1) n2) {a} = {!   !}

mutual 
    finite-locations : ∀{n} 
        -> {ps1 ps2 : Vec Pattern n}
        -> (ecs : equiv-constructors ps1 ps2)
        -> ∃[ n ]
            Σ[ f ∈ (Fin n -> locations ecs) ]
            (surjection f)
    finite-locations {n} {[]} {[]} tt = zero , (λ ()) , λ ()
    finite-locations {n} {p1 ∷ ps1} {p2 ∷ ps2} (ec , ecs) with finite-location ec | finite-locations ecs
    ... | n1 , f1 , s1 | n2 , f2 , s2 = n1 + n2 , (λ x → f (_≅_.to (sum-fin n1 n2) x)) , s
        where 
        f : Fin n1 ⊎ Fin n2 → location ec ⊎ locations ecs 
        f (inj₁ n) = inj₁ (f1 n)
        f (inj₂ n) = inj₂ (f2 n)

        s : (b : location ec ⊎ locations ecs) 
            -> Σ (Fin (n1 + n2)) (λ a → f (_≅_.to (sum-fin n1 n2) a) ≡ b)
        s (inj₁ l) with s1 l
        s (inj₁ l) | n , eq = (_≅_.from (sum-fin n1 n2) (inj₁ n)) , eq'
            where 
            eq' : f (_≅_.to (sum-fin n1 n2) (_≅_.from (sum-fin n1 n2) (inj₁ n))) ≡ inj₁ l
            eq' rewrite _≅_.tofrom (sum-fin n1 n2) {inj₁ n} = cong inj₁ eq
        s (inj₂ l) with s2 l
        s (inj₂ l) | n , eq = (_≅_.from (sum-fin n1 n2) (inj₂ n)) , eq'
            where 
            eq' : f (_≅_.to (sum-fin n1 n2) (_≅_.from (sum-fin n1 n2) (inj₂ n))) ≡ inj₂ l
            eq' rewrite _≅_.tofrom (sum-fin n1 n2) {inj₂ n} = cong inj₂ eq

    finite-location :  {p1 p2 : Pattern} 
        -> (ec : equiv-constructor p1 p2)
        -> ∃[ n ]
            Σ[ f ∈ (Fin n -> location ec) ]
            (surjection f)
    finite-location ECX = 1 , (λ _ → tt) , (λ b → zero , refl)
    finite-location (ECK ecs) = finite-locations ecs


-- partition : {p1 p2 : Pattern} 
--     -> (ec : equiv-constructor p1 p2)

generalization-equiv-constructor : ∀{p1 p2}
    -> equiv-constructor p1 p2
    -> ∃[ s1 ] ∃[ s2 ] s1 , s2 mgu p1 , p2
generalization-equiv-constructor ec = {!   !} , {!   !} , {!   !}












data _,_preunifies_,_ (s1 s2 : Sub) (p1 p2 : Pattern) : Set where
    PU : ((s1' s2' : Sub) 
            -> s1' , s2' unifies p1 , p2
            -> (s1' ⊑ s1 × s2' ⊑ s2))
        -> s1 , s2 preunifies p1 , p2

freshesL : (n : ℕ) -> Vec Pattern n 
freshesL zero = []
freshesL (suc n) = X (L (Fresh n)) ∷ freshesL n

freshesL-ex : freshesL 3 ≡ (X (L (Fresh 2))) ∷ (X (L (Fresh 1)) ∷ (X (L (Fresh 0))) ∷ [])
freshesL-ex = refl

childfold : {n : ℕ} -> (s : Sub) -> (ps : Vec Pattern n) -> Sub
childfold s [] x = X x
childfold {suc n} s (p ∷ ps) x with x ≟v (Fresh n)
... | yes refl = s [ p ]
... | no neq = childfold s ps x

data prefix {n : ℕ} (ps : Vec Pattern n) : {n' : ℕ} -> (ps' : Vec Pattern n') -> Set where 
    PrefixSelf : prefix ps ps
    PrefixCons : ∀{p' n'}
        -> {ps' : Vec Pattern n'}
        -> prefix ps (p' ∷ ps')
        -> prefix ps ps'

data indexof : {n : ℕ} -> (ps : Vec Pattern n) -> (n' : ℕ) -> (p : Pattern) -> Set where 
    IndexOfHead : ∀{n p}
        -> {ps : Vec Pattern n}
        -> indexof (p ∷ ps) n p
    IndexOfCons : ∀{n n' p p'}
        -> {ps : Vec Pattern n'}
        -> indexof ps n p
        -> indexof (p' ∷ ps) n p

prefix-to-index : ∀{n1 n1' n p}
    -> {ps : Vec Pattern n1}
    -> {ps' : Vec Pattern n1'}
    -> prefix ps ps'
    -> indexof ps' n p
    -> indexof ps n p
prefix-to-index PrefixSelf i = i
prefix-to-index (PrefixCons p) i = prefix-to-index p (IndexOfCons i)

index-lt-length : ∀{n n' p}
    -> {ps : Vec Pattern n'}
    -> indexof ps n p
    -> n < n'
index-lt-length IndexOfHead = s≤s (≤-reflexive refl)
index-lt-length (IndexOfCons i) = helper (index-lt-length i)
    where 
    helper : ∀{n n'} -> n ≤ n' -> n ≤ suc n'
    helper z≤n = z≤n
    helper (s≤s leq) = s≤s (helper leq)

lt-not-eq : ∀{n n'} -> n < n' -> n ≡ n' -> ⊥ 
lt-not-eq (s≤s l) refl = lt-not-eq l refl

cons-inj : ∀{n x1 x2}
    -> {xs1 xs2 : Vec Pattern n}
    -> x1 ∷ xs1 ≡ x2 ∷ xs2 
    -> x1 ≡ x2
cons-inj refl = refl

cons-inj-tl : ∀{n x1 x2}
    -> {xs1 xs2 : Vec Pattern n}
    -> x1 ∷ xs1 ≡ x2 ∷ xs2 
    -> xs1 ≡ xs2
cons-inj-tl refl = refl

K-inj-kn : ∀{n1 n2 k1 k2}
    -> {ps1 : Vec Pattern n1}
    -> {ps2 : Vec Pattern n2}
    -> K k1 n1 ps1 ≡ K k2 n2 ps2 
    -> k1 ≡ k2 × n1 ≡ n2
K-inj-kn refl = refl , refl

K-inj-ps : ∀{n k1 k2}
    -> {ps1 ps2 : Vec Pattern n}
    -> K k1 n ps1 ≡ K k2 n ps2 
    -> ps1 ≡ ps2
K-inj-ps refl = refl

cons-preunify : ∀{s1 s2 p1 p2 k n} 
    -> {ps1 ps2 : Vec Pattern n}
    -> s1 , s2 preunifies p1 , p2
    -> s1 , s2 preunifies K k (suc n) (p1 ∷ ps1) , K k (suc n) (p2 ∷ ps2)
cons-preunify {s1} {s2} {p1} {p2} {k} {n} {ps1} {ps2} (PU pu) = PU pu'
    where 
    pu' : (s1' s2' : Sub)
      -> s1' , s2' unifies K k (suc n) (p1 ∷ ps1) , K k (suc n) (p2 ∷ ps2) 
      -> (s1' ⊑ s1) × (s2' ⊑ s2) 
    pu' s1' s2' (Unify u) = pu s1' s2' (Unify (cons-inj (K-inj-ps u)))

cons-preunify-tl :  ∀{s1 s2 p1 p2 k n} 
    -> {ps1 ps2 : Vec Pattern n}
    -> s1 , s2 preunifies K k n ps1 , K k n ps2
    -> s1 , s2 preunifies K k (suc n) (p1 ∷ ps1) , K k (suc n) (p2 ∷ ps2)
cons-preunify-tl {s1} {s2} {p1} {p2} {k} {n} {ps1} {ps2} (PU pu) = PU pu'
    where 
    pu' : (s1' s2' : Sub)
      -> s1' , s2' unifies K k (suc n) (p1 ∷ ps1) , K k (suc n) (p2 ∷ ps2) 
      -> (s1' ⊑ s1) × (s2' ⊑ s2) 
    pu' s1' s2' (Unify u) = pu s1' s2' (Unify (cong (K k n) (cons-inj-tl (K-inj-ps u))))

-- split-leq : (p1 p2 : Pattern) -> (s1 s2 : Sub) -> (pu : s1 , s2 preunifies p1 , p2) -> Set 
-- split-leq p1 p2 s1 s2 (PU pu) = (s1' s2' : Sub) -> (u : s1' , s2' unifies p1 , p2) -> helper s1' s2' u
--     where 
--     helper : (s1' s2' : Sub) -> (u : s1' , s2' unifies p1 , p2) -> Set 
--     helper s1' s2' u with pu s1' s2' u 
--     ... | Prec sp1 eq1 , Prec sp2 eq2 = metric sp1 sp2 (s1 [ p1 ]) (s2 [ p2 ]) < metric s1' s2' p1 p2

-- split-leq-cons-preunify : ∀{s1 s2 p1 p2 k n pu}
--     -> {ps1 ps2 : Vec Pattern n}
--     -> split-leq p1 p2 s1 s2 pu
--     -> split-leq (K k (suc n) (p1 ∷ ps1))
--       (K k (suc n) (p2 ∷ ps2)) s1 s2 (cons-preunify pu)
-- split-leq-cons-preunify {s1} {s2} {p1} {p2} {k} {n} {PU pu} {ps1} {ps2} leq s1' s2' (Unify u) with pu s1' s2' ((Unify (cons-inj (K-inj-ps u)))) in eq
-- ... | Prec sp1 eq1 , Prec sp2 eq2 = {!   !}

{-# REWRITE +-suc #-}

metric-lemma-1 : ∀{s3 s4 p1 p2 k1 n1}
    -> {ps1 ps2 : Vec Pattern n1}
    -> metric s3 s4 p1 p2 > 0
    -> metric s3 s4 (K k1 (suc n1) (p1 ∷ ps1)) (K k1 (suc n1) (p2 ∷ ps2)) > 0
metric-lemma-1 {s3} {s4} {p1} {p2} l with size-diff s3 p1 | size-diff s4 p2
... | zero | suc _ = s≤s z≤n
... | suc _ | _ = s≤s z≤n

metric-lemma-2 : ∀{s3 s4 p1 p2 k1 n1}
    -> {ps1 ps2 : Vec Pattern n1}
    -> metric s3 s4 (K k1 n1 ps1) (K k1 n1 ps2) > 0
    -> metric s3 s4 (K k1 (suc n1) (p1 ∷ ps1)) (K k1 (suc n1) (p2 ∷ ps2)) > 0
metric-lemma-2 {s3} {s4} {p1} {p2} {k1} {n1} {ps1} {ps2} l with size-diff s3 (K k1 n1 ps1) | size-diff s4 (K k1 n1 ps2)
... | zero | suc _ = s≤s z≤n
... | suc _ | _ = s≤s z≤n

-- begin Claude's work
-- Helper: (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange : ∀ a b c d -> (a + b) + (c + d) ≡ (a + c) + (b + d)
+-interchange a b c d = begin
    (a + b) + (c + d)   ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))    ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)    ≡⟨ cong (λ x → a + (x + d)) (+-comm b c) ⟩
    a + ((c + b) + d)    ≡⟨ cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d))    ≡⟨ sym (+-assoc a c (b + d)) ⟩
    (a + c) + (b + d)    ∎
    where open ≡-Reasoning

-- Lemma 1: size-diff s p + size p ≡ size (s [ p ])

mutual
    size-sub-vec : ∀{n}
        -> (s : Sub)
        -> (ps : Vec Pattern n)
        -> sum (map (size-diff s) ps) + sum (map size ps) ≡ sum (map size (map (_[_] s) ps))
    size-sub-vec s [] = refl
    size-sub-vec s (p ∷ ps)
        rewrite sym (size-sub s p)
        rewrite sym (size-sub-vec s ps)
        = +-interchange (size-diff s p) (sum (map (size-diff s) ps)) (size p) (sum (map size ps))

    size-sub : (s : Sub)
        -> (p : Pattern)
        -> size-diff s p + size p ≡ size (s [ p ])
    size-sub s (X x) = +-identityʳ (size (s x))
    size-sub s (K k n ps) rewrite sym (size-sub-vec s ps) = refl

-- Lemma 2: size-diff decomposes over composition
mutual
    size-diff-comp-vec : ∀{n}
        -> (sp s : Sub)
        -> (ps : Vec Pattern n)
        -> sum (map (size-diff (sp ∘ s)) ps) ≡ sum (map (size-diff sp) (map (_[_] s) ps)) + sum (map (size-diff s) ps)
    size-diff-comp-vec sp s [] = refl
    size-diff-comp-vec sp s (p ∷ ps)
        rewrite size-diff-comp sp s p
        rewrite size-diff-comp-vec sp s ps
        = sym (+-interchange (size-diff sp (s [ p ])) (sum (map (size-diff sp) (map (_[_] s) ps))) (size-diff s p) (sum (map (size-diff s) ps)))

    size-diff-comp : (sp s : Sub)
        -> (p : Pattern)
        -> size-diff (sp ∘ s) p ≡ size-diff sp (s [ p ]) + size-diff s p
    size-diff-comp sp s (X x) = sym (size-sub sp (s x))
    size-diff-comp sp s (K k n ps) = size-diff-comp-vec sp s ps

-- Lemma 3: metric decomposes over composition
metric-comp : (sp1 sp2 s1' s2' : Sub) (p1 p2 : Pattern)
    -> metric (sp1 ∘ s1') (sp2 ∘ s2') p1 p2
       ≡ metric sp1 sp2 (s1' [ p1 ]) (s2' [ p2 ]) + metric s1' s2' p1 p2
metric-comp sp1 sp2 s1' s2' p1 p2
    rewrite size-diff-comp sp1 s1' p1
    rewrite size-diff-comp sp2 s2' p2
    = +-interchange (size-diff sp1 (s1' [ p1 ])) (size-diff s1' p1) (size-diff sp2 (s2' [ p2 ])) (size-diff s2' p2)

-- Lemma 4: arithmetic helper
-- if a + b ≤ suc n and 1 ≤ b then a ≤ n
arith-helper : ∀{a b n} -> a + b ≤ suc n -> 1 ≤ b -> a ≤ n
arith-helper {zero} _ _ = z≤n
arith-helper {suc a} {suc b} {suc n} (s≤s h) (s≤s _) = s≤s (arith-helper {a} {suc b} {n} h (s≤s z≤n))

-- The final result
metric-inequality : ∀{s1 s2 s1' s2' sp1 sp2 p1 p2 n}
    -> metric s1 s2 p1 p2 ≤ suc n
    -> s1 ≡ sp1 ∘ s1'
    -> s2 ≡ sp2 ∘ s2'
    -> metric s1' s2' p1 p2 > 0
    -> metric sp1 sp2 (s1' [ p1 ]) (s2' [ p2 ]) ≤ n
metric-inequality {s1} {s2} {s1'} {s2'} {sp1} {sp2} {p1} {p2} {n} eq eq1 eq2 lt
    rewrite eq1 rewrite eq2
    rewrite metric-comp sp1 sp2 s1' s2' p1 p2
    = arith-helper {metric sp1 sp2 (s1' [ p1 ]) (s2' [ p2 ])} {metric s1' s2' p1 p2} {n} eq lt
-- end Claude's work

data SplitResult (p1 p2 : Pattern) : Set where
    SplitEC : equiv-constructor p1 p2
        -> SplitResult p1 p2
    SplitPU : (s1 s2 : Sub)
        -> (pu : s1 , s2 preunifies p1 , p2)
        -> metric s1 s2 p1 p2 > 0
        -> SplitResult p1 p2

{-# TERMINATING #-}
splitter : ∀{s1 s2 p1 p2}
        -> s1 , s2 unifies p1 , p2
        -> SplitResult p1 p2 
splitter {s1} {s2} {X _} {X _} u = SplitEC ECX

splitter {s1} {s2} {K k1 zero ps1} {K k2 (suc n2) ps2} (Unify ())
splitter {s1} {s2} {K k1 (suc n1) ps1} {K k2 zero ps2} (Unify ())
splitter {s1} {s2} {K k1 zero []} {K k2 zero []} (Unify refl) = SplitEC (ECK tt)
splitter {s1} {s2} {K k1 (suc n1) (p1 ∷ ps1)} {K k2 (suc n2) (p2 ∷ ps2)} (Unify u) with K-inj-kn u
splitter {s1} {s2} {K k1 (suc n1) (p1 ∷ ps1)} {K .(k1) (suc n2) (p2 ∷ ps2)} (Unify u) | refl , refl with splitter {s1} {s2} {p1} {p2} (Unify (cons-inj (K-inj-ps u))) 
... | SplitPU s3 s4 pu lt = SplitPU s3 s4 (cons-preunify pu) (metric-lemma-1 {s3} {s4} {p1} {p2} {k1} {n1} {ps1} {ps2} lt)
... | SplitEC ec with splitter {s1} {s2} {K k1 (n1) (ps1)} {K k1 (n2) (ps2)} (Unify (cong (K k1 n1) (cons-inj-tl (K-inj-ps u))))
... | SplitEC (ECK ecs) = SplitEC (ECK (ec , ecs))
... | SplitPU s3 s4 pu lt = SplitPU s3 s4 (cons-preunify-tl pu) (metric-lemma-2 {s3} {s4} {p1} {p2} {k1} {n1} {ps1} {ps2} lt)

splitter {s1} {s2} {X x} {K k n ps} u = SplitPU s1' sid (PU pu) ineq
    where
    s1' : Sub
    s1' x' with x ≟v x' 
    ... | yes refl = K k n (freshesL n)
    ... | no _ = X (R x')

    ineq : metric s1' sid (X x) (K k n ps) > 0
    ineq with x ≟v x
    ... | yes refl = s≤s z≤n
    ... | no neq = ⊥-elim (neq refl)

    pu : (s1'' s2'' : Sub)
        -> s1'' , s2'' unifies X x , K k n ps
        -> (s1'' ⊑ s1') × (s2'' ⊑ sid)
    pu s1'' s2'' (Unify eq) = (Prec (sp ps) (funext equiv)) , (Prec s2'' refl)
        where 
        sp : ∀{n} -> (ps : Vec Pattern n) -> Sub 
        sp ps' y with cleave y 
        ... | inj₁ x' = childfold s2'' ps' x'
        ... | inj₂ x' = s1'' x'

        equiv : (x' : Var) → s1'' x' ≡ ((sp ps) ∘ s1') x'
        equiv x' with x ≟v x' 
        equiv x' | no _ with cleave (R x') in eq'
        equiv x' | no _ | inj₁ _ = refl
        equiv x' | no _ | inj₂ _ with eq' 
        equiv x' | no _ | inj₂ _ | refl = refl
        equiv x' | yes refl = trans eq (cong (K k n) (equiv-children ps PrefixSelf))
            where
            equiv-child2 : ∀{n' n'' p' }
                -> {ps' : Vec Pattern n''}
                -> indexof ps' n' p'
                -> s2'' [ p' ] ≡ childfold s2'' ps' (Fresh n')
            equiv-child2 {n'} {n'' = n''} IndexOfHead with Fresh n' ≟v Fresh n'
            equiv-child2 {n'} IndexOfHead | yes refl  = refl
            equiv-child2 {n'} IndexOfHead | no neq = ⊥-elim (neq refl)
            equiv-child2 {n'} {n'' = n''} (IndexOfCons i) with Fresh n' ≟v Fresh n''
            equiv-child2 {n'} (IndexOfCons i) | yes eq' with Fresh-inj eq'
            equiv-child2 {n'} {n'' = suc n''} (IndexOfCons i) | yes _ | refl with Fresh (suc n'') ≟v Fresh n''
            equiv-child2 {n'} (IndexOfCons i) | yes _ | refl | yes eq' with Fresh-inj eq'
            equiv-child2 {n'} (IndexOfCons i) | yes _ | refl | yes _ | ()
            equiv-child2 {n'} (IndexOfCons i) | yes _ | refl | no _ = equiv-child2 i
            equiv-child2 {n'} {n'' = suc n''} (IndexOfCons i) | no neq with Fresh n' ≟v Fresh n''
            equiv-child2 {n'} (IndexOfCons i) | no neq | yes eq' rewrite eq' = ⊥-elim (lt-not-eq (index-lt-length i) (Fresh-inj eq'))
            equiv-child2 {n'} (IndexOfCons i) | no neq | no neq' = equiv-child2 i

            equiv-child1 : ∀{n' n'' p'}
                -> {ps' : Vec Pattern n''}
                -> indexof ps' n' p'
                -> s2'' [ p' ] ≡ sp ps' (L (Fresh n'))
            equiv-child1 {n'} i with cleave (L (Fresh n')) in eq''
            equiv-child1 {n'} i | inj₁ x = equiv-child2 i 
            equiv-child1 {n'} i | inj₂ _ with eq'' 
            equiv-child1 {n'} i | inj₂ _ | () 

            equiv-children : {n' : ℕ} -> (ps' : Vec Pattern n') -> prefix ps ps' -> map (_[_] s2'') ps' ≡ map (_[_] (sp ps)) (freshesL n')
            equiv-children [] pref = refl
            equiv-children  {suc n'} (p' ∷ ps') pref = cong₂ _∷_ (equiv-child1 (prefix-to-index pref IndexOfHead)) (equiv-children ps' (PrefixCons pref))
        

splitter {s1} {s2} {K x n x₁} {X x₂} u = {!   !} -- symmetrical
    

generalization-sized : ∀{s1 s2 p1 p2}
    -> (n : ℕ)
    -> metric s1 s2 p1 p2 ≤ n
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization-sized {s1} {s2} {p1} {p2} zero eq u with size-diff s1 p1 in eq1 | size-diff s2 p2 in eq2
generalization-sized {s1} {s2} {p1} {p2} zero eq u | zero | zero with size-diff-zero s1 p1 eq1 | size-diff-zero s2 p2 eq2
generalization-sized zero eq (Unify u) | zero | zero | ec1 | ec2 rewrite u = generalization-equiv-constructor (equiv-constructor-trans ec1 (equiv-constructor-sym ec2))
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq u with splitter u 
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq u | SplitEC ec = generalization-equiv-constructor ec
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq (Unify u) | SplitPU s1' s2' (PU pu) lt with pu s1 s2 (Unify u) in pu-eq
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq (Unify u) | SplitPU s1' s2' (PU pu) lt | Prec sp1 eq1 , Prec sp2 eq2 with generalization-sized {sp1} {sp2} {s1' [ p1 ]} {s2' [ p2 ]} n inequation (Unify equation)
    where 
    equation : (sp1 ∘ s1') [ p1 ] ≡ (sp2 ∘ s2') [ p2 ]
    equation rewrite eq1 rewrite eq2 = u

    inequation : metric sp1 sp2 (s1' [ p1 ]) (s2' [ p2 ]) ≤ n
    inequation = metric-inequality {s1} {s2} {s1'} {s2'} {sp1} {sp2} {p1} {p2} {n} eq eq1 eq2 lt  
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq u | SplitPU s1' s2' (PU pu) lt | Prec sp1 eq1 , Prec sp2 eq2 | s1'' , s2'' , MGU (Unify u') mgu = (s1'' ∘ s1') , (s2'' ∘ s2') , MGU (Unify u') mgu'
    where 
    mgu' : (sl sr : Sub) →
      sl , sr unifies p1 , p2 →
      (sl ⊑ (s1'' ∘ s1')) × (sr ⊑ (s2'' ∘ s2'))
    mgu' sl sr (Unify u'') with pu sl sr (Unify u'')
    ... | Prec sp1' eq1' , Prec sp2' eq2' with mgu sp1' sp2' (Unify equation) 
        where 
        equation : (sp1' ∘ s1') [ p1 ] ≡ (sp2' ∘ s2') [ p2 ]
        equation rewrite eq1' rewrite eq2' = u''
    ... | Prec slp eql , Prec srp eqr = (Prec slp equation1) , Prec srp equation2
        where 
        equation1 : sl ≡ (slp ∘ s1'') ∘ s1'
        equation1 rewrite eql rewrite eq1' = refl
        equation2 : sr ≡ (srp ∘ s2'') ∘ s2'
        equation2 rewrite eqr rewrite eq2' = refl

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization = generalization-sized _ (≤-reflexive refl)

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2)
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r
existence (Step t1 t2 p1 p2 f1 s1 refl refl) (Step .t2 t3 p3 p4 f2 s2 eq refl) with generalization (Unify {s1} {s2} {p2} {p3} eq)
... | s1' , s2' , mgu = ((s1' [ p1 ]) ↦ (s2' [ p4 ]) [ ∘r-functional p1 p2 p3 p4 f1 f2 s1' s2' mgu ]) , (Comp f1 f2 s1' s2' mgu)