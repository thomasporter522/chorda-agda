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
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.List using (List; []; _∷_)

open import core

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

VarSub : Set
VarSub = Var -> Var

toSub : VarSub -> Sub
toSub f x = X (f x)

_∘v_ : VarSub -> VarSub -> VarSub
(f ∘v g) x = f (g x)

rename2 : Var -> Var -> Var -> VarSub
rename2 a b c v with a ≟v v
... | yes _ = c
... | no _ with b ≟v v
... | yes _ = c
... | no _ = v

rename2-a : (a b c : Var) -> rename2 a b c a ≡ c
rename2-a a b c with a ≟v a
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

rename2-b : (a b c : Var) -> rename2 a b c b ≡ c
rename2-b a b c with a ≟v b
... | yes _ = refl
... | no _ with b ≟v b
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

X-inj : ∀{a b} -> _≡_ {_} {Pattern} (X a) (X b) -> a ≡ b
X-inj refl = refl

-- L-injectivity from Cleft isomorphism
L-inj : {x y : Var} -> L x ≡ L y -> x ≡ y
L-inj eq with cong (_≅_.to Cleft) eq
... | ceq = inj₁-inj ceq
    where
    inj₁-inj : ∀{A B : Set}{a b : A} -> _≡_ {_} {A ⊎ B} (inj₁ a) (inj₁ b) -> a ≡ b
    inj₁-inj refl = refl

-- Informative case analysis on rename2
rename2-cases : (a b c v : Var)
    -> ((a ≡ v) × (rename2 a b c v ≡ c))
     ⊎ ((a ≢ v) × (b ≡ v) × (rename2 a b c v ≡ c))
     ⊎ ((a ≢ v) × (b ≢ v) × (rename2 a b c v ≡ v))
rename2-cases a b c v with a ≟v v
... | yes eq = inj₁ (eq , refl)
... | no neqa with b ≟v v
... | yes eq = inj₂ (inj₁ (neqa , eq , refl))
... | no neqb = inj₂ (inj₂ (neqa , neqb , refl))

K-inj-ps : ∀{k1 k2 n} {ps1 ps2 : Vec Pattern n}
    -> _≡_ {_} {Pattern} (K k1 n ps1) (K k2 n ps2) -> ps1 ≡ ps2
K-inj-ps refl = refl

cons-inj-hd : ∀{n}{a b : Pattern}{as bs : Vec Pattern n} -> a ∷ as ≡ b ∷ bs -> a ≡ b
cons-inj-hd refl = refl

cons-inj-tl : ∀{n}{a b : Pattern}{as bs : Vec Pattern n} -> a ∷ as ≡ b ∷ bs -> as ≡ bs
cons-inj-tl refl = refl

{-# TERMINATING #-}
sub-cong : (f g : Sub) -> (∀ v -> f v ≡ g v) -> (p : Pattern) -> f [ p ] ≡ g [ p ]
sub-cong f g eq (X x) = eq x
sub-cong f g eq (K k n ps) = cong (K k n) (go ps)
    where
    go : ∀{n} -> (ps : Vec Pattern n) -> map (_[_] f) ps ≡ map (_[_] g) ps
    go [] = refl
    go (p ∷ ps) = cong₂ _∷_ (sub-cong f g eq p) (go ps)

mutual
    lift-ec-vec : ∀{n} {ps1 ps2 : Vec Pattern n}
        -> (h : VarSub) (f g : VarSub)
        -> (ecs : equiv-constructors ps1 ps2)
        -> map (_[_] (toSub f)) ps1 ≡ map (_[_] (toSub g)) ps2
        -> map (_[_] (toSub (h ∘v f))) ps1 ≡ map (_[_] (toSub (h ∘v g))) ps2
    lift-ec-vec {ps1 = []} {[]} h f g _ _ = refl
    lift-ec-vec {ps1 = _ ∷ _} {_ ∷ _} h f g (ec , ecs) eq =
        cong₂ _∷_ (lift-ec h f g ec (cons-inj-hd eq)) (lift-ec-vec h f g ecs (cons-inj-tl eq))

    lift-ec : ∀{p1 p2}
        -> (h : VarSub) (f g : VarSub)
        -> (ec : equiv-constructor p1 p2)
        -> toSub f [ p1 ] ≡ toSub g [ p2 ]
        -> toSub (h ∘v f) [ p1 ] ≡ toSub (h ∘v g) [ p2 ]
    lift-ec h f g ECX eq = cong (λ v → X (h v)) (X-inj eq)
    lift-ec h f g (ECK {k} {n} ecs) eq =
        cong (K k n) (lift-ec-vec h f g ecs (K-inj-ps eq))

-- Lookup and sp
LookupEntry : Set
LookupEntry = Var × Var

lookup-search : List LookupEntry -> Var -> Var
lookup-search [] w = w
lookup-search ((fv , xv) ∷ rest) w with fv ≟v w
... | yes _ = xv
... | no _ = lookup-search rest w

sp-of : List LookupEntry -> Sub -> Sub -> Sub
sp-of entries s1' s2' v with cleave v
... | inj₁ w = s1' (lookup-search entries w)
... | inj₂ w = s2' w

lookup-hit : (fv xv : Var) (rest : List LookupEntry)
    -> lookup-search ((fv , xv) ∷ rest) fv ≡ xv
lookup-hit fv xv rest with fv ≟v fv
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

lookup-miss : (fv xv w : Var) (rest : List LookupEntry)
    -> fv ≢ w -> lookup-search ((fv , xv) ∷ rest) w ≡ lookup-search rest w
lookup-miss fv xv w rest neq with fv ≟v w
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

-- Freshness: L(Fresh j) not in range of f or g for j ≥ k
FreshFrom : VarSub -> VarSub -> ℕ -> Set
FreshFrom f g k = (j : ℕ) -> k ≤ j -> (v : Var) -> f v ≢ L (Fresh j) × g v ≢ L (Fresh j)

rename2-fresh-lem : (a b : Var) (f g : VarSub) (k : ℕ)
    -> FreshFrom f g k
    -> FreshFrom (rename2 a b (L (Fresh k)) ∘v f) (rename2 a b (L (Fresh k)) ∘v g) (suc k)
rename2-fresh-lem a b f g k fr j le v = left-part , right-part
    where
    k≠j : k ≢ j
    k≠j eq = 1+n≰n (subst (suc k ≤_) (sym eq) le)
    LFk≠LFj : L (Fresh k) ≢ L (Fresh j)
    LFk≠LFj eq = k≠j (Fresh-inj (L-inj eq))
    k≤j : k ≤ j
    k≤j = ≤-trans (n≤1+n k) le
    left-part : rename2 a b (L (Fresh k)) (f v) ≢ L (Fresh j)
    left-part eq with rename2-cases a b (L (Fresh k)) (f v)
    ... | inj₁ (_ , is-c) = LFk≠LFj (trans (sym is-c) eq)
    ... | inj₂ (inj₁ (_ , _ , is-c)) = LFk≠LFj (trans (sym is-c) eq)
    ... | inj₂ (inj₂ (_ , _ , is-v)) = proj₁ (fr j k≤j v) (trans (sym is-v) eq)
    right-part : rename2 a b (L (Fresh k)) (g v) ≢ L (Fresh j)
    right-part eq with rename2-cases a b (L (Fresh k)) (g v)
    ... | inj₁ (_ , is-c) = LFk≠LFj (trans (sym is-c) eq)
    ... | inj₂ (inj₁ (_ , _ , is-c)) = LFk≠LFj (trans (sym is-c) eq)
    ... | inj₂ (inj₂ (_ , _ , is-v)) = proj₂ (fr j k≤j v) (trans (sym is-v) eq)

postulate
    initial-fresh : FreshFrom L R 0

-- Now: for the sp-of miss case, I need: if FreshFrom f g k and f v ≠ a and f v ≠ b,
-- then f v ≠ L(Fresh k). This follows from FreshFrom.
-- Specifically: rename2 a b (L(Fresh k)) (f v) = f v when f v ≠ a and f v ≠ b.
-- And we need sp-of ((Fresh k, x1) ∷ ent) to agree with sp-of ent on (f v).
-- That is: lookup-search ((Fresh k, x1) ∷ ent) w = lookup-search ent w
-- where f v = L w. We need Fresh k ≢ w, i.e., L(Fresh k) ≢ L(w) = f(v).
-- Which is fr k ≤-refl v (first component).

-- Helper to extract: if f v is in L-namespace, get the inner var
-- Actually we know f v = L(something) or R(something) since f = h ∘v L initially.
-- But we don't track this. We just need: from FreshFrom, Fresh k ≠ L-component of f v.

-- Key lemma: if f v ≠ L(Fresh k), then sp-of with extra (Fresh k, x1) agrees with old
sp-of-extend-miss-L : (fk : ℕ) (x1 : Var) (ent : List LookupEntry) (s1' s2' : Sub) (w : Var)
    -> L w ≢ L (Fresh fk)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (L w) ≡ sp-of ent s1' s2' (L w)
sp-of-extend-miss-L fk x1 ent s1' s2' w neq =
    cong s1' (lookup-miss (Fresh fk) x1 w ent (λ eq → neq (cong L (sym eq))))

sp-of-extend-miss-R : (fk : ℕ) (x1 : Var) (ent : List LookupEntry) (s1' s2' : Sub) (w : Var)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (R w) ≡ sp-of ent s1' s2' (R w)
sp-of-extend-miss-R fk x1 ent s1' s2' w = refl

sp-of-extend-miss : (fk : ℕ) (x1 : Var) (ent : List LookupEntry) (s1' s2' : Sub) (v : Var)
    -> v ≢ L (Fresh fk)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' v ≡ sp-of ent s1' s2' v
sp-of-extend-miss fk x1 ent s1' s2' v neq with cleave v in cv
... | inj₁ w = cong s1' (lookup-miss (Fresh fk) x1 w ent w≠Fk)
    where
    v≡Lw : v ≡ L w
    v≡Lw = trans (sym fromto) (cong (_≅_.from Cleft) cv)
    w≠Fk : Fresh fk ≢ w
    w≠Fk eq = neq (trans v≡Lw (cong L (sym eq)))
... | inj₂ w = refl

-- sp-of on a hit
sp-of-extend-hit : (fk : ℕ) (x1 : Var) (ent : List LookupEntry) (s1' s2' : Sub)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (L (Fresh fk)) ≡ s1' x1
sp-of-extend-hit fk x1 ent s1' s2' = cong s1' (lookup-hit (Fresh fk) x1 ent)

-- Result records
record Solved {p1 p2 : Pattern} (ec : equiv-constructor p1 p2)
    (f g : VarSub) (ent : List LookupEntry) (k : ℕ) : Set where
    constructor MkSolved
    field
        f' g' : VarSub
        ent' : List LookupEntry
        k' : ℕ
        h : VarSub
        f'-def : ∀ v -> f' v ≡ h (f v)
        g'-def : ∀ v -> g' v ≡ h (g v)
        unifies : toSub f' [ p1 ] ≡ toSub g' [ p2 ]
        fresh-inv : FreshFrom f' g' k'
        mgu-inv : (s1' s2' : Sub) -> (_,_unifies_,_ s1' s2' p1 p2)
            -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
            -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
            -> ((v : Var) -> sp-of ent' s1' s2' (f' v) ≡ s1' v)
             × ((v : Var) -> sp-of ent' s1' s2' (g' v) ≡ s2' v)

record SolvedVec {n : ℕ} {ps1 ps2 : Vec Pattern n}
    (ecs : equiv-constructors ps1 ps2)
    (f g : VarSub) (ent : List LookupEntry) (k : ℕ) : Set where
    constructor MkSolvedVec
    field
        f' g' : VarSub
        ent' : List LookupEntry
        k' : ℕ
        h : VarSub
        f'-def : ∀ v -> f' v ≡ h (f v)
        g'-def : ∀ v -> g' v ≡ h (g v)
        unifies : map (_[_] (toSub f')) ps1 ≡ map (_[_] (toSub g')) ps2
        fresh-inv : FreshFrom f' g' k'
        mgu-inv : (s1' s2' : Sub)
            -> map (_[_] s1') ps1 ≡ map (_[_] s2') ps2
            -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
            -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
            -> ((v : Var) -> sp-of ent' s1' s2' (f' v) ≡ s1' v)
             × ((v : Var) -> sp-of ent' s1' s2' (g' v) ≡ s2' v)

mutual
    solve-vec : ∀{n} {ps1 ps2 : Vec Pattern n}
        -> (ecs : equiv-constructors ps1 ps2)
        -> (f g : VarSub) -> (ent : List LookupEntry) -> (k : ℕ)
        -> FreshFrom f g k
        -> SolvedVec ecs f g ent k
    solve-vec {ps1 = []} {[]} _ f g ent k fr =
        MkSolvedVec f g ent k (λ v → v) (λ _ → refl) (λ _ → refl) refl fr
            (λ s1' s2' _ fi gi → fi , gi)
    solve-vec {ps1 = p1 ∷ _} {p2 ∷ _} (ec , ecs) f g ent k fr with solve ec f g ent k fr
    ... | MkSolved f1 g1 ent1 k1 h1 f1d g1d u1 fr1 m1 with solve-vec ecs f1 g1 ent1 k1 fr1
    ... | MkSolvedVec f2 g2 ent2 k2 h2 f2d g2d u2 fr2 m2 = MkSolvedVec f2 g2 ent2 k2 (h2 ∘v h1)
        (λ v → trans (f2d v) (cong h2 (f1d v)))
        (λ v → trans (g2d v) (cong h2 (g1d v)))
        (cong₂ _∷_ head-eq u2)
        fr2
        mgu-combined
        where
        f2≡ : toSub f2 ≡ toSub (h2 ∘v f1)
        f2≡ = funext (λ v → cong X (f2d v))
        g2≡ : toSub g2 ≡ toSub (h2 ∘v g1)
        g2≡ = funext (λ v → cong X (g2d v))
        head-eq : toSub f2 [ p1 ] ≡ toSub g2 [ p2 ]
        head-eq rewrite f2≡ | g2≡ = lift-ec h2 f1 g1 ec u1

        mgu-combined : (s1' s2' : Sub)
            -> map (_[_] s1') (p1 ∷ _) ≡ map (_[_] s2') (p2 ∷ _)
            -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
            -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
            -> ((v : Var) -> sp-of ent2 s1' s2' (f2 v) ≡ s1' v)
             × ((v : Var) -> sp-of ent2 s1' s2' (g2 v) ≡ s2' v)
        mgu-combined s1' s2' u' fi gi with m1 s1' s2' (Unify (cons-inj-hd u')) fi gi
        ... | fi1 , gi1 = m2 s1' s2' (cons-inj-tl u') fi1 gi1

    solve : ∀{p1 p2}
        -> (ec : equiv-constructor p1 p2)
        -> (f g : VarSub) -> (ent : List LookupEntry) -> (k : ℕ)
        -> FreshFrom f g k
        -> Solved ec f g ent k
    solve (ECX {x1} {x2}) f g ent k fr with f x1 ≟v g x2
    ... | yes veq = MkSolved f g ent k (λ v → v)
        (λ _ → refl) (λ _ → refl) (cong X veq) fr
        (λ s1' s2' _ fi gi → fi , gi)
    ... | no neq = MkSolved
        (rename2 (f x1) (g x2) (L (Fresh k)) ∘v f)
        (rename2 (f x1) (g x2) (L (Fresh k)) ∘v g)
        ((Fresh k , x1) ∷ ent)
        (suc k)
        (rename2 (f x1) (g x2) (L (Fresh k)))
        (λ _ → refl) (λ _ → refl)
        (cong X (trans (rename2-a (f x1) (g x2) (L (Fresh k)))
                       (sym (rename2-b (f x1) (g x2) (L (Fresh k))))))
        (rename2-fresh-lem (f x1) (g x2) f g k fr)
        mgu-leaf-wrap
        where
        ren : VarSub
        ren = rename2 (f x1) (g x2) (L (Fresh k))

        sp-of-ren : (a b : Var) (fk : ℕ) (x₁ : Var) (ent₁ : List LookupEntry) (s1' s2' : Sub) (w : Var)
            -> sp-of ent₁ s1' s2' a ≡ s1' x₁
            -> sp-of ent₁ s1' s2' b ≡ s1' x₁
            -> w ≢ L (Fresh fk)
            -> sp-of ((Fresh fk , x₁) ∷ ent₁) s1' s2' (rename2 a b (L (Fresh fk)) w) ≡ sp-of ent₁ s1' s2' w
        sp-of-ren a b fk x₁ ent₁ s1' s2' w spa spb wfr with rename2-cases a b (L (Fresh fk)) w
        ... | inj₁ (a≡w , ren≡c) rewrite ren≡c =
            trans (sp-of-extend-hit fk x₁ ent₁ s1' s2')
                  (trans (sym spa) (cong (sp-of ent₁ s1' s2') a≡w))
        ... | inj₂ (inj₁ (_ , b≡w , ren≡c)) rewrite ren≡c =
            trans (sp-of-extend-hit fk x₁ ent₁ s1' s2')
                  (trans (sym spb) (cong (sp-of ent₁ s1' s2') b≡w))
        ... | inj₂ (inj₂ (_ , _ , ren≡v)) rewrite ren≡v =
            sp-of-extend-miss fk x₁ ent₁ s1' s2' w wfr

        mgu-leaf-wrap : (s1' s2' : Sub) -> (_,_unifies_,_ s1' s2' (X x1) (X x2))
            -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
            -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
            -> ((v : Var) -> sp-of ((Fresh k , x1) ∷ ent) s1' s2' (ren (f v)) ≡ s1' v)
             × ((v : Var) -> sp-of ((Fresh k , x1) ∷ ent) s1' s2' (ren (g v)) ≡ s2' v)
        mgu-leaf-wrap s1' s2' (Unify u') fi gi = left-inv , right-inv
            where
            left-inv : (v : Var) -> sp-of ((Fresh k , x1) ∷ ent) s1' s2' (ren (f v)) ≡ s1' v
            left-inv v = trans (sp-of-ren (f x1) (g x2) k x1 ent s1' s2' (f v)
                (fi x1) (trans (gi x2) (sym u')) (proj₁ (fr k ≤-refl v))) (fi v)
            right-inv : (v : Var) -> sp-of ((Fresh k , x1) ∷ ent) s1' s2' (ren (g v)) ≡ s2' v
            right-inv v = trans (sp-of-ren (f x1) (g x2) k x1 ent s1' s2' (g v)
                (fi x1) (trans (gi x2) (sym u')) (proj₂ (fr k ≤-refl v))) (gi v)

    solve (ECK {kk} {n} ecs) f g ent k fr with solve-vec ecs f g ent k fr
    ... | MkSolvedVec f' g' ent' k' h fd gd u fr' m = MkSolved f' g' ent' k' h fd gd (cong (K kk n) u) fr' mgu-k
        where
        mgu-k : (s1' s2' : Sub) -> (_,_unifies_,_ s1' s2' (K kk n _) (K kk n _))
            -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
            -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
            -> ((v : Var) -> sp-of ent' s1' s2' (f' v) ≡ s1' v)
             × ((v : Var) -> sp-of ent' s1' s2' (g' v) ≡ s2' v)
        mgu-k s1' s2' (Unify u') fi gi = m s1' s2' (K-inj-ps u') fi gi

build-mgu : ∀{p1 p2}
    -> equiv-constructor p1 p2
    -> ∃[ s1 ] ∃[ s2 ] s1 , s2 mgu p1 , p2
build-mgu ec with solve ec L R [] 0 initial-fresh
... | MkSolved f g ent' k' h fd gd u fr m = toSub f , toSub g , MGU (Unify u) mgu'
    where
    mgu' : (s1' s2' : Sub) -> (_,_unifies_,_ s1' s2' _ _)
        -> s1' ⊑ toSub f × s2' ⊑ toSub g
    mgu' s1' s2' u' with m s1' s2' u' (λ v → refl) (λ v → refl)
    ... | fi , gi = Prec (sp-of ent' s1' s2') (funext (λ v → sym (fi v)))
                  , Prec (sp-of ent' s1' s2') (funext (λ v → sym (gi v)))
