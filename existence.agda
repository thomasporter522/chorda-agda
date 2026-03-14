{-# OPTIONS --rewriting #-}


open import Data.Nat
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Unit
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


generalization-equiv-constructor : ∀{p1 p2}
    -> equiv-constructor p1 p2
    -> ∃[ s1 ] ∃[ s2 ] s1 , s2 mgu p1 , p2
generalization-equiv-constructor = {!   !}

data _,_preunifies_,_ (s1 s2 : Sub) (p1 p2 : Pattern) : Set where
    PU : ((s1' s2' : Sub) 
            -> s1' , s2' unifies p1 , p2
            -> (s1' ⊑ s1 × s2' ⊑ s2))
        -> s1 , s2 preunifies p1 , p2

data SplitResult (p1 p2 : Pattern) : Set where
    SplitEC : equiv-constructor p1 p2
        -> SplitResult p1 p2
    SplitPU : (s1 s2 : Sub)
        -> s1 , s2 preunifies p1 , p2
        -> SplitResult p1 p2

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
index-lt-length IndexOfHead = s≤s ≤-reflexive
    where 
    ≤-reflexive : ∀{x} -> x ≤ x 
    ≤-reflexive {zero} = z≤n
    ≤-reflexive {suc x} = s≤s ≤-reflexive
index-lt-length (IndexOfCons i) = helper (index-lt-length i)
    where 
    helper : ∀{n n'} -> n ≤ n' -> n ≤ suc n'
    helper z≤n = z≤n
    helper (s≤s leq) = s≤s (helper leq)

lt-not-eq : ∀{n n'} -> n < n' -> n ≡ n' -> ⊥ 
lt-not-eq (s≤s l) refl = lt-not-eq l refl

mutual 

    -- splitters : ∀{s1 s2 p1 p2}
    --         -- -> s1 , s2 unifies p1 , p2
    --         -> SplitResults p1 p2 

    splitter : ∀{s1 s2 p1 p2}
            -> s1 , s2 unifies p1 , p2
            -> SplitResult p1 p2 
    splitter {s1} {s2} {X _} {X _} u = SplitEC ECX
    splitter {s1} {s2} {K k1 n1 ps1} {K k2 n2 ps2} u = {!   !}
    splitter {s1} {s2} {X x} {K k n ps} u = SplitPU s1' sid (PU pu)
        where
        s1' : Sub
        s1' x' with x ≟v x' 
        ... | yes refl = K k n (freshesL n)
        ... | no _ = X (R x')

        pu : (s1'' s2'' : Sub)
            -> s1'' , s2'' unifies X x , K k n ps
            -> (s1'' ⊑ s1') × (s2'' ⊑ sid)
        pu s1'' s2'' (Unify eq) = (Prec (sp ps) (funext equiv)) , (Prec s2'' refl)
            where 
            sp : ∀{n} -> (ps : Vec Pattern n) -> Sub 
            sp ps' y with cleave y 
            ... | inj₁ x' = childfold s2'' ps' x'
            ... | inj₂ x' = s1'' x'

            dumm : ∀{p' n' n''}
                -> {ps' : Vec Pattern n''}
                -> indexof ps' n' p'
                -> s2'' [ p' ] ≡ childfold s2'' ps' (Fresh n')
            dumm {n' = n'} {n'' = n''} IndexOfHead with Fresh n' ≟v Fresh n'
            dumm {n' = n'} IndexOfHead | yes refl  = refl
            dumm {n' = n'} IndexOfHead | no neq = ⊥-elim (neq refl)
            dumm {n' = n'} {n'' = n''} (IndexOfCons i) with Fresh n' ≟v Fresh n''
            dumm {n' = n'} (IndexOfCons i) | yes eq''' with Fresh-inj _ _ eq''' 
            dumm {n' = n'} {n'' = suc n''} (IndexOfCons i) | yes eq''' | refl with Fresh (suc n'') ≟v Fresh n'' in eq''''''''''
            dumm {n' = n'} (IndexOfCons i) | yes eq''' | refl | yes eq'''''' with Fresh-inj _ _ eq''''''
            dumm {n' = n'} (IndexOfCons i) | yes eq''' | refl | yes eq'''''' | ()
            dumm {n' = n'} (IndexOfCons i) | yes eq''' | refl | no neq'''' = dumm i
            dumm {n' = n'} {n'' = suc n''} (IndexOfCons i) | no neq with Fresh n' ≟v Fresh n''
            dumm {n' = n'} {n'' = suc n''} (IndexOfCons i) | no neq | yes eq'''' rewrite eq'''' = ⊥-elim (lt-not-eq (index-lt-length i) (Fresh-inj _ _ eq''''))
            dumm {n' = n'} {n'' = suc n''} (IndexOfCons i) | no neq | no neq' = dumm i

            durr : ∀{p' n' n''}
                -> {ps' : Vec Pattern n''}
                -> indexof ps' n' p'
                -> s2'' [ p' ] ≡ sp ps' (L (Fresh n'))
            durr {n' = n'} i with cleave (L (Fresh n')) in eq''
            durr {n' = n'} i | inj₁ x = dumm i 
            durr {n' = n'} i | inj₂ _ with eq'' 
            durr {n' = n'} i | inj₂ _ | () 

            thing2 : {n' : ℕ} -> (ps' : Vec Pattern n') -> prefix ps ps' -> map (_[_] s2'') ps' ≡ map (_[_] (sp ps)) (freshesL n')
            thing2 [] pref = refl
            thing2 {suc n'} (p' ∷ ps') pref = cong₂ _∷_ (durr (prefix-to-index pref IndexOfHead)) (thing2 ps' (PrefixCons pref))
            
            equiv : (x' : Var) → s1'' x' ≡ ((sp ps) ∘ s1') x'
            equiv x' with x ≟v x' 
            ... | yes refl = trans eq (cong (K k n) (thing2 ps PrefixSelf))
            ... | no _ with cleave (R x') in eq'
            ... | inj₁ _ = refl
            ... | inj₂ _ with eq' 
            ... | refl = refl

    splitter {s1} {s2} {K x n x₁} {X x₂} u = {!   !} -- symmetrical
    

generalization-sized : ∀{s1 s2 p1 p2}
    -> (n : ℕ)
    -> metric s1 s2 p1 p2 ≡ n
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization-sized {s1} {s2} {p1} {p2} zero eq uni with size-diff s1 p1 in eq1 | size-diff s2 p2 in eq2
generalization-sized {s1} {s2} {p1} {p2} zero eq uni | zero | zero with size-diff-zero s1 p1 eq1 | size-diff-zero s2 p2 eq2
generalization-sized zero eq (Unify u) | zero | zero | ec1 | ec2 rewrite u = generalization-equiv-constructor (equiv-constructor-trans ec1 (equiv-constructor-sym ec2))
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq uni with splitter uni 
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq uni | SplitEC ec = generalization-equiv-constructor ec
generalization-sized {s1} {s2} {p1} {p2} (suc n) eq uni | SplitPU s1' s2' pu = {!   !}
-- with generalization-sized {{!   !}} {{!   !}} {(step-sub x) [ p1 ]} {p2} {!   !} {!   !} {!   !}
-- generalization-sized {s1} {s2} {p1} {p2} (suc n) eq uni | SplitXK s1' s2' pu | s1'' , s2'' , (MGU (Unify u') mgu) = (s1' ∘ (step-sub x)) , s2' , MGU (Unify u') mgu'
    -- where 
    -- mgu' : (s1'' s2'' : Sub)
    --   -> s1'' , s2'' unifies p1 , p2
    --   -> (s1'' ⊑ (s1' ∘ step-sub x)) × (s2'' ⊑ s2')
    -- mgu' s1'' s2'' (Unify u'') = {!   !} --Prec {!   !} {!   !} , Prec {!   !} {!   !}

--     generalization-equiv-constructor ECX
-- generalization-sized {s1} {s2} {K k1 n1 ps1} {K k2 n2 ps2} (suc n) eq (Unify u) = {! n2  !}
-- generalization-sized {s1} {s2} {X x} {K x₁ n₁ x₂} (suc n) eq uni = {!   !}
-- generalization-sized {s1} {s2} {K x n₁ x₁} {X x₂} (suc n) eq uni = {!   !}

generalization : ∀{p1 p2 s1 s2}
    -> s1 , s2 unifies p1 , p2
    -> ∃[ s1' ] ∃[ s2' ] s1' , s2' mgu p1 , p2
generalization = generalization-sized _ refl

existence : ∀{t1 t2 t3 r1 r2}
    -> (t1 ↦[ r1 ] t2)
    -> (t2 ↦[ r2 ] t3)
    -> ∃[ r ] r1 ∘r r2 ≡ r
existence (Step t1 t2 p1 p2 f1 s1 refl refl) (Step .t2 t3 p3 p4 f2 s2 eq refl) with generalization (Unify {s1} {s2} {p2} {p3} eq)
... | s1' , s2' , mgu = ((s1' [ p1 ]) ↦ (s2' [ p4 ]) [ ∘r-functional p1 p2 p3 p4 f1 f2 s1' s2' mgu ]) , (Comp f1 f2 s1' s2' mgu)