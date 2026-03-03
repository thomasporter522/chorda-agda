open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])

open import core

mutual 
    map-fusion : ∀{s1 s2 n} 
        -> {ps : Vec Pattern n}
        -> map (_[_] s1) (map (_[_] s2) ps) ≡ map (_[_] (s1 ∘ s2)) ps
    map-fusion {ps = []} = refl
    map-fusion {s1} {s2} {ps = p ∷ ps} 
        rewrite ∘-eq s1 s2 p 
        rewrite map-fusion {s1} {s2} {ps = ps} = refl

    ∘-eq : (s1 s2 : Sub)
        -> (p : Pattern)
        -> s1 [ s2 [ p ] ] ≡ (s1 ∘ s2) [ p ]
    ∘-eq _ _ (X x) = refl
    ∘-eq s1 s2 (K k n ps)
        rewrite map-fusion {s1} {s2} {ps = ps} = refl