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

VarSub : Set
VarSub = Var -> Var

_∘v_ : VarSub -> VarSub -> VarSub
(f ∘v g) x = f (g x)

rename2 : Var -> Var -> Var -> VarSub
rename2 a b c v with a ≟v v
... | yes _ = c
... | no _ with b ≟v v
... | yes _ = c
... | no _ = v

rename2-cases : (a b c v : Var)
    -> ((a ≡ v) × (rename2 a b c v ≡ c))
     ⊎ ((a ≢ v) × (b ≡ v) × (rename2 a b c v ≡ c))
     ⊎ ((a ≢ v) × (b ≢ v) × (rename2 a b c v ≡ v))
rename2-cases a b c v with a ≟v v
... | yes eq = inj₁ (eq , refl)
... | no neqa with b ≟v v
... | yes eq = inj₂ (inj₁ (neqa , eq , refl))
... | no neqb = inj₂ (inj₂ (neqa , neqb , refl))

-- L-injectivity
L-inj : {x y : Var} -> L x ≡ L y -> x ≡ y
L-inj eq with cong (_≅_.to Cleft) eq
... | ceq = inj₁-inj ceq
    where
    inj₁-inj : ∀{A B : Set}{a b : A} -> _≡_ {_} {A ⊎ B} (inj₁ a) (inj₁ b) -> a ≡ b
    inj₁-inj refl = refl

-- Freshness
FreshFrom : VarSub -> VarSub -> ℕ -> Set
FreshFrom f g k = (j : ℕ) -> k ≤ j -> (v : Var) -> f v ≢ L (Fresh j) × g v ≢ L (Fresh j)

-- rename2-fresh-lem
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

-- initial-fresh
postulate
    initial-fresh : FreshFrom L R 0

-- Lookup
lookup-search : List (Var × Var) -> Var -> Var
lookup-search [] w = w
lookup-search ((fv , xv) ∷ rest) w with fv ≟v w
... | yes _ = xv
... | no _ = lookup-search rest w

sp-of : List (Var × Var) -> Sub -> Sub -> Sub
sp-of entries s1' s2' v with cleave v
... | inj₁ w = s1' (lookup-search entries w)
... | inj₂ w = s2' w

lookup-hit : (fv xv : Var) (rest : List (Var × Var))
    -> lookup-search ((fv , xv) ∷ rest) fv ≡ xv
lookup-hit fv xv rest with fv ≟v fv
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

lookup-miss : (fv xv w : Var) (rest : List (Var × Var))
    -> fv ≢ w -> lookup-search ((fv , xv) ∷ rest) w ≡ lookup-search rest w
lookup-miss fv xv w rest neq with fv ≟v w
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

sp-of-extend-miss : (fk : ℕ) (x1 : Var) (ent : List (Var × Var)) (s1' s2' : Sub) (v : Var)
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

sp-of-extend-hit : (fk : ℕ) (x1 : Var) (ent : List (Var × Var)) (s1' s2' : Sub)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (L (Fresh fk)) ≡ s1' x1
sp-of-extend-hit fk x1 ent s1' s2' = cong s1' (lookup-hit (Fresh fk) x1 ent)

-- The key lemma for left-inv/right-inv.
-- For any w: sp-of new (rename2 a b (L(Fresh k)) w) = sp-of old w
-- when spa and spb hold and w is fresh-unused.
sp-of-rename2 : (a b : Var) (fk : ℕ) (x1 : Var) (ent : List (Var × Var)) (s1' s2' : Sub) (w : Var)
    -> sp-of ent s1' s2' a ≡ s1' x1
    -> sp-of ent s1' s2' b ≡ s1' x1
    -> w ≢ L (Fresh fk)
    -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (rename2 a b (L (Fresh fk)) w) ≡ sp-of ent s1' s2' w
sp-of-rename2 a b fk x1 ent s1' s2' w spa spb wfr with rename2-cases a b (L (Fresh fk)) w
... | inj₁ (a≡w , ren≡c) rewrite ren≡c =
    -- result is L(Fresh fk), sp-of new = s1' x1
    -- sp-of old w = sp-of old a = s1' x1 (since a ≡ w)
    trans (sp-of-extend-hit fk x1 ent s1' s2')
          (trans (sym spa) (cong (sp-of ent s1' s2') a≡w))
... | inj₂ (inj₁ (_ , b≡w , ren≡c)) rewrite ren≡c =
    trans (sp-of-extend-hit fk x1 ent s1' s2')
          (trans (sym spb) (cong (sp-of ent s1' s2') b≡w))
... | inj₂ (inj₂ (_ , _ , ren≡v)) rewrite ren≡v =
    sp-of-extend-miss fk x1 ent s1' s2' w wfr

-- Now derive left-inv and right-inv from sp-of-rename2
-- left-inv: sp-of new (ren (f v)) ≡ s1' v
-- = sp-of new (rename2 (f x1) (g x2) (L(Fresh k)) (f v)) ≡ s1' v
-- By sp-of-rename2 with a=(f x1), b=(g x2), w=(f v):
--   = sp-of old (f v)  [when spa = sp-of old (f x1) = s1' x1, spb = sp-of old (g x2) = s2' x2 = s1' x1 (by u')]
--   = s1' v (by fi v)
-- The spa is fi x1. The spb needs: sp-of old (g x2) = s1' x1.
-- We have gi x2 : sp-of old (g x2) = s2' x2. And u' : s1' x1 = s2' x2.
-- So sp-of old (g x2) = s2' x2 = s1' x1 (by sym u'). Actually we need s1' x1 not s2' x2.
-- spb should be: sp-of old (g x2) ≡ s1' x1 = trans (gi x2) (sym u').

left-inv-lem : (f g : VarSub) (x1 x2 : Var) (fk : ℕ)
    (ent : List (Var × Var)) (s1' s2' : Sub)
    -> s1' x1 ≡ s2' x2
    -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
    -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
    -> FreshFrom f g fk
    -> (v : Var) -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (rename2 (f x1) (g x2) (L (Fresh fk)) (f v)) ≡ s1' v
left-inv-lem f g x1 x2 fk ent s1' s2' u' fi gi fr v =
    trans (sp-of-rename2 (f x1) (g x2) fk x1 ent s1' s2' (f v)
            (fi x1)
            (trans (gi x2) (sym u'))
            (proj₁ (fr fk ≤-refl v)))
          (fi v)

right-inv-lem : (f g : VarSub) (x1 x2 : Var) (fk : ℕ)
    (ent : List (Var × Var)) (s1' s2' : Sub)
    -> s1' x1 ≡ s2' x2
    -> ((v : Var) -> sp-of ent s1' s2' (f v) ≡ s1' v)
    -> ((v : Var) -> sp-of ent s1' s2' (g v) ≡ s2' v)
    -> FreshFrom f g fk
    -> (v : Var) -> sp-of ((Fresh fk , x1) ∷ ent) s1' s2' (rename2 (f x1) (g x2) (L (Fresh fk)) (g v)) ≡ s2' v
right-inv-lem f g x1 x2 fk ent s1' s2' u' fi gi fr v =
    trans (sp-of-rename2 (f x1) (g x2) fk x1 ent s1' s2' (g v)
            (fi x1)
            (trans (gi x2) (sym u'))
            (proj₂ (fr fk ≤-refl v)))
          (gi v)
