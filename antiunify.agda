open import main

-- constructive proof of that antiunifications always exist
antiunify : {metas : nat} -> 
    (p1 p2 : pat metas) -> 
    antiunification p1 p2
antiunify (T {a1} k1 ts1) (T {a2} k2 ts2) = {!   !}
antiunify (T k ts) (X x) = {!   !}
antiunify (X x) (T k ts) = {!   !}
antiunify (X x1) (X x2) = {!   !}
