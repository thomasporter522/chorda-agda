open import Data.Nat
open import Data.Vec hiding ([_])
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import core

validity : ∀{r1 r2 r R}
    -> r1 ∘r r2 ≡ r 
    -> R r1 
    -> R r2 
    -> R ≅ R ∪[ r ]
validity = {!   !}