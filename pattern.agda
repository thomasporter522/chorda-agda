
open import Data.Product hiding (map)
open import Data.Nat renaming (ℕ to nat)
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality
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
        suc-index-eq : ∀{a a' n} -> {v : Vec A n} -> {x : Fin n} -> 
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
    
    data _m⊒_ {arity metas metas' : nat} (p1 : Vec (kpat K metas) arity) (p2 : Vec (kpat K metas') arity) : Set where
        MRefine : (s : sub metas metas') -> multisubst-eq s p1 p2 -> p1 m⊒ p2
    
    data lb {metas1 metas2 metas : nat} (p1 : pat metas1) (p2 : pat metas2) (p : pat metas) : Set where
        LB : p1 ⊒ p -> p2 ⊒ p -> lb p1 p2 p

    data mlb {arity metas1 metas2 metas : nat} (p1 : Vec (kpat K metas1) arity) (p2 : Vec (kpat K metas2) arity) (p : Vec (kpat K metas) arity) : Set where
        MLB : p1 m⊒ p -> p2 m⊒ p -> mlb p1 p2 p
    
    data _⊓_＝_ {metas1 metas2 metas : nat} (p1 : pat metas1) (p2 : pat metas2) (p : pat metas) : Set where 
        GLB : lb p1 p2 p -> 
            (∀{metas'} -> (p' : pat metas') -> lb p1 p2 p' -> p ⊒ p') ->
            p1 ⊓ p2 ＝ p

    data _m⊓_＝_ {arity metas1 metas2 metas : nat} (p1 : Vec (kpat K metas1) arity) (p2 : Vec (kpat K metas2) arity) (p : Vec (kpat K metas) arity) : Set where 
        MGLB : mlb p1 p2 p -> 
            (∀{metas'} -> (p' : Vec (kpat K metas') arity) -> mlb p1 p2 p' -> p m⊒ p') ->
            p1 m⊓ p2 ＝ p

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









    vec-const : ∀{metas metas'} -> 
        (p : pat metas') -> 
        sub metas metas'
    vec-const {zero} p = []
    vec-const {suc metas} p = p ∷ vec-const p

    var-gt : ∀{metas metas'} -> 
        (x : Fin metas) -> 
        (p : pat metas') -> 
        (X x) ⊒ p
    var-gt zero p = Refine (p ∷ vec-const p) (X-subst-eq zero-index-eq)
    var-gt (suc x) p with var-gt x p 
    ... | Refine s (X-subst-eq i) = Refine (p ∷ s) (X-subst-eq (suc-index-eq i))

    range : (n : nat) -> Vec (Fin n) n
    range zero = []
    range (suc n) = zero ∷ map suc (range n)

    id-sub : (metas : nat) -> sub metas metas
    id-sub metas = map X (range metas)

    index-eq-unicity : ∀{metas arity} -> 
        {i : Fin arity} ->
        {ps : Vec (pat metas) arity} -> 
        {p p' : pat metas} -> 
        index-eq ps i p -> 
        index-eq ps i p' -> 
        p ≡ p' 
    index-eq-unicity zero-index-eq zero-index-eq = refl
    index-eq-unicity (suc-index-eq ie) (suc-index-eq ie') = index-eq-unicity ie ie'

    map-index-eq : ∀{A B a n} -> {v : Vec A n} -> {x : Fin n} -> {f : A -> B} ->
        index-eq v x a -> 
        index-eq (map f v) x (f a)
    map-index-eq zero-index-eq = zero-index-eq
    map-index-eq (suc-index-eq ie) = suc-index-eq (map-index-eq ie)

    range-index-eq : ∀{n} ->
        (x : Fin n) -> 
        index-eq (range n) x x
    range-index-eq zero = zero-index-eq
    range-index-eq (suc x) = suc-index-eq (map-index-eq (range-index-eq x))

    id-index-eq : ∀{metas} ->
        (x : Fin metas) -> 
        index-eq (id-sub metas) x (X x)
    id-index-eq x = map-index-eq (range-index-eq x)

    mutual
        {-# TERMINATING #-}
        id-multisubst-eq : ∀{metas arity} -> 
            (ps : Vec (pat metas) arity) -> 
            multisubst-eq (id-sub metas) ps ps
        id-multisubst-eq ps i p p' ie ie' rewrite index-eq-unicity ie ie' = id-subst-eq p'

        id-subst-eq : ∀{metas} ->
            (p : pat metas) -> 
            subst-eq (id-sub metas) p p
        id-subst-eq (T k ps) = T-subst-eq (id-multisubst-eq ps)
        id-subst-eq (X x) = X-subst-eq (id-index-eq x)

    gt-refl : ∀{metas} -> 
        (p : pat metas) -> 
        p ⊒ p
    gt-refl {metas} p = Refine (id-sub metas) (id-subst-eq p)

    m⊒-T⊒ : ∀{arity metasL metasR k} -> 
        {psL : Vec (kpat K metasL) arity} -> 
        {psR : Vec (kpat K metasR) arity} -> 
        psL m⊒ psR -> 
        T k psL ⊒ T k psR
    m⊒-T⊒ (MRefine s x) = Refine s (T-subst-eq x)

    T⊒-m⊒ : ∀{arity metasL metasR k} -> 
        {psL : Vec (kpat K metasL) arity} -> 
        {psR : Vec (kpat K metasR) arity} -> 
        T k psL ⊒ T k psR ->
        psL m⊒ psR
    T⊒-m⊒ (Refine s (T-subst-eq x)) = (MRefine s x)

    mlb-Tlb : ∀{arity metas metasL metasR k} -> 
        {psL : Vec (kpat K metasL) arity} -> 
        {psR : Vec (kpat K metasR) arity} -> 
        {ps : Vec (kpat K metas) arity} -> 
        mlb psL psR ps -> 
        lb (T k psL) (T k psR) (T k ps)
    mlb-Tlb (MLB L R) = LB (m⊒-T⊒ L) (m⊒-T⊒ R)

    Tlb-mlb : ∀{arity metas metasL metasR k} -> 
        {psL : Vec (kpat K metasL) arity} -> 
        {psR : Vec (kpat K metasR) arity} -> 
        {ps : Vec (kpat K metas) arity} -> 
        lb (T k psL) (T k psR) (T k ps) ->
        mlb psL psR ps
    Tlb-mlb (LB L R) = MLB (T⊒-m⊒ L) (T⊒-m⊒ R)

    m⊓-T⊓ : ∀{arity metas metasL metasR k} -> 
        {psL : Vec (kpat K metasL) arity} -> 
        {psR : Vec (kpat K metasR) arity} -> 
        {ps : Vec (kpat K metas) arity} -> 
        psL m⊓ psR ＝ ps -> 
        T k psL ⊓ T k psR ＝ T k ps
    m⊓-T⊓ {k = k} {psL = psL} {psR = psR} {ps = ps} (MGLB l limit) = GLB (mlb-Tlb l) helper
        where 
        helper : ∀{metas'} ->
            (p' : pat metas') → 
            lb (T k psL) (T k psR) p' → 
            T k ps ⊒ p'
        helper (T k ps') (LB (Refine s (T-subst-eq x)) r) = m⊒-T⊒ (limit ps' (Tlb-mlb (LB (Refine s (T-subst-eq x)) r))) 

    data GLBResult {metasL metasR : nat} (pL : pat metasL) (pR : pat metasR) : Set where 
        CR : {metas' : nat} ->
            (p' : pat metas') -> 
            pL ⊓ pR ＝ p' ->
            GLBResult pL pR

    data MultiGLBResult {arity metasL metasR : nat} (psL : Vec (kpat K metasL) arity) (psR : Vec (kpat K metasR) arity) : Set where 
        MCR : {metas' : nat} ->
            (ps' : Vec (kpat K metas') arity) -> 
            psL m⊓ psR ＝ ps' ->
            MultiGLBResult psL psR

    mutual 
        multi-glb : ∀{arity metasL metasR metas} -> 
            (psL : Vec (kpat K metasL) arity) -> 
            (psR : Vec (kpat K metasR) arity) -> 
            (ps : Vec (kpat K metas) arity) -> 
            MultiGLBResult psL psR
        multi-glb psL psR ps = {!   !}

        glb : ∀{metasL metasR metas} -> 
            (pL : pat metasL) -> 
            (pR : pat metasR) -> 
            (p : pat metas) -> 
            lb pL pR p -> 
            GLBResult pL pR

        glb (X xL) (X xR) p (LB (Refine sL (X-subst-eq x₂)) (Refine sR (X-subst-eq x₃))) = 
            CR {metas' = suc zero} (X zero) (GLB (LB (var-gt xL (X zero)) (var-gt xR (X zero))) gt)
                where 
                gt : {metas' : nat} (p' : pat metas') -> lb (X xL) (X xR) p' -> X zero ⊒ p'
                gt p' z = Refine (p' ∷ []) (X-subst-eq zero-index-eq)

        glb (T k psL) (X x) p (LB (Refine sL (T-subst-eq mse)) (Refine sR (X-subst-eq ie))) =
            CR (T k psL) (GLB (LB (gt-refl (T k psL)) (var-gt x (T k psL))) gt)
                where 
                gt : {metas' : nat} (p' : pat metas') -> lb (T k psL) (X x) p' → T k psL ⊒ p'
                gt p' (LB g _) = g

        glb (X x) (T k psR) p (LB (Refine sL (X-subst-eq ie)) (Refine sR (T-subst-eq mse))) = 
            CR (T k psR) (GLB (LB (var-gt x (T k psR)) (gt-refl (T k psR))) gt)
                where 
                gt : {metas' : nat} (p' : pat metas') -> lb (X x) (T k psR) p' → T k psR ⊒ p'
                gt p' (LB _ g) = g

        glb (T k psL) (T .k psR) (T .k ps) (LB (Refine sL (T-subst-eq mseL)) (Refine sR (T-subst-eq mseR))) 
            with multi-glb psL psR ps
        ... | MCR ps' x = CR (T k ps') (m⊓-T⊓ x)