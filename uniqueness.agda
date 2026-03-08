open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import core
open import lemmas

uniqueness : ∀{r1 r2 r r'}
    -> r1 ∘r r2 ≡ r
    -> r1 ∘r r2 ≡ r' 
    -> r ≡r r'
uniqueness 
    (Comp s1 s2 (MGU (Unify u1) mgu1)) 
    (Comp s3 s4 (MGU (Unify u2) mgu2)) with mgu1 s3 s4 (Unify u2) | mgu2 s1 s2 (Unify u1)
... | Prec a e1 , Prec b e2 | Prec c e3 , Prec d e4 = REquiv {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}