open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import core
open import lemmas

associativity : ∀{r1 r2 r3 r12 r23 r123 r123'}
    -> r1 ∘r r2 ≡ r12 
    -> r2 ∘r r3 ≡ r23 
    -> r1 ∘r r23 ≡ r123
    -> r12 ∘r r3 ≡ r123'
    -> r123 ≡r r123'
associativity 
    {r1 = p1 ↦ p2}
    {r2 = p3 ↦ p4}
    {r3 = p5 ↦ p6}
    (Comp s1 s2 (MGU (Unify u1) mgu1)) 
    (Comp s3 s4 (MGU (Unify u2) mgu2))
    (Comp s5 s6 (MGU (Unify u3) mgu3)) 
    (Comp s7 s8 (MGU (Unify u4) mgu4)) 
    with 
    mgu1 s5 (s6 ∘ s3) (Unify (trans u3 (∘-eq s6 s3 p3))) 
    | mgu2 (s7 ∘ s2) s8 (Unify (trans (sym (∘-eq s7 s2 p4)) u4))
... | Prec s15 e15 , Prec s236 e236 
    | Prec s327 e327 , Prec s48 e48 
    with mgu3 (s7 ∘ s1) s327 (Unify helper1) | mgu4 s236 (s6 ∘ s4) (Unify helper2)
        where 
        helper1 : (s7 ∘ s1) [ p2 ] ≡ s327 [ s3 [ p3 ] ]
        helper1 
            rewrite sym (∘-eq s7 s1 p2)
            rewrite u1 
            rewrite ∘-eq s7 s2 p3 
            rewrite e327 
            rewrite sym (∘-eq s327 s3 p3) = refl
        helper2 : s236 [ s2 [ p4 ] ] ≡ (s6 ∘ s4) [ p5 ]
        helper2 
            rewrite sym (∘-eq s6 s4 p5)
            rewrite sym u2
            rewrite ∘-eq s236 s2 p4
            rewrite ∘-eq s6 s3 p4
            rewrite e236 = refl
... | Prec s517 e517 , Prec s6327 e6327 
    | Prec s7236 e7236 , Prec s846 e846
    = REquiv s517 s846 helper1 {!   !} {!   !} helper2
        where 
        helper1 : s517 [ s5 [ p1 ] ] ≡ s7 [ s1 [ p1 ] ] 
        helper1 x
            rewrite ∘-eq s517 s5 p1
            rewrite sym e517 
            rewrite sym (∘-eq s7 s1 p1) = refl
        helper2 : s846 [ s8 [ p6 ] ] ≡ s6 [ s4 [ p6 ] ]
        helper2 
            rewrite ∘-eq s846 s8 p6
            rewrite sym e846
            rewrite sym (∘-eq s6 s4 p6) = refl
        -- potentially useful fact:
        -- s6327 ∘ s6 ∘ s3 = s7 ∘ s2 
        -- s7236 ∘ s7 ∘ s2 = s6 ∘ s3 
        -- therefore s6 ∘ s3 ≡ s7 ∘ s2 

        -- I can only prove A(s7(s1(p1))) = s5(p1)
        -- by proving that A ∘ s7 ∘ s1 = s5.
        -- Why? 
        -- Because I have no assumptions that refer to p1. 