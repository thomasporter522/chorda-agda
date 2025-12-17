open import Data.Nat renaming (ℕ to nat)
open import Data.Vec
open import Data.Fin

open import Language 

data K : nat -> Set where 
    -- expressions
    Var : K 1 -- : index -> exp
    Fun : K 1 -- : exp -> exp 
    Ap : K 2 -- : exp -> exp -> exp
    -- indices
    Zero : K 0 -- index -> index
    Suc : K 1 -- index -> index 
    -- environment
    EnvNil : K 0 -- : env
    EnvSnoc : K 2 -- : env -> clos -> env 
    -- Closures
    Clos : K 2 -- : env -> exp -> clos 
    -- stack 
    StackNil : K 0 -- : stack
    StackCons : K 2 -- : frame -> stack -> stack 
    ApFun : K 1 -- : clos -> frame
    ApArg : K 1 -- : clos -> frame 
    -- state
    Machine : K 2 -- : clos -> stack -> state
    Crash : K 0 -- : state

meta0 : (kpat K 4)
meta0 = X zero
meta1 : (kpat K 4)
meta1 = X (suc zero)
meta2 : (kpat K 4)
meta2 = X (suc (suc zero))
meta3 : (kpat K 4)
meta3 = X (suc (suc (suc zero)))

data _b⇒1_ : {metas : nat} → kpat K metas → kpat K metas → Set where 
    StepVarCrash : 
        _b⇒1_ {metas = 1} 
        (T Machine (T Clos (T EnvNil [] ∷ T Var ((T Zero []) ∷ []) ∷ []) ∷ (X zero) ∷ [])) 
        (T Crash [])
    StepVarFind : 
        _b⇒1_ {metas = 4} 
        (T Machine (T Clos (T EnvSnoc (meta0 ∷ meta1 ∷ []) ∷ T Var ((T Zero []) ∷ []) ∷ []) ∷ meta2 ∷ [])) 
        (T Machine (meta1 ∷ meta2 ∷ []))
    StepVarSkip : 
        _b⇒1_ {metas = 4} 
        (T Machine (T Clos (T EnvSnoc (meta0 ∷ meta1 ∷ []) ∷ T Var (((T Suc (meta2 ∷ [])) ∷ [])) ∷ []) ∷ meta3 ∷ [])) 
        (T Machine (T Clos (meta0 ∷ T Var (meta2 ∷ []) ∷ []) ∷ meta3 ∷ [])) 
    StepAp : 
        _b⇒1_ {metas = 4} 
        (T Machine (T Clos (meta0 ∷ T Ap (meta1 ∷ meta2 ∷ []) ∷ []) ∷ meta3 ∷ [])) 
        (T Machine (T Clos (meta0 ∷ meta2 ∷ []) ∷ T StackCons ((T ApFun ((T Clos (meta0 ∷ meta1 ∷ [])) ∷ [])) ∷ meta3 ∷ []) ∷ []))
    StepApFun :
        _b⇒1_ {metas = 4} 
        (T Machine (T Clos (meta0 ∷ T Fun (meta1 ∷ []) ∷ []) ∷ T StackCons ((T ApFun (meta2 ∷ [])) ∷ meta3 ∷ []) ∷ []))
        (T Machine (meta2 ∷ T StackCons ((T ApArg ((T Clos (meta0 ∷ T Fun (meta1 ∷ []) ∷ [])) ∷ [])) ∷ meta3 ∷ []) ∷ []))
    StepApArg :
        _b⇒1_ {metas = 4} 
        (T Machine (T Clos (meta0 ∷ T Fun (meta1 ∷ []) ∷ []) ∷ T StackCons ((T ApArg (meta2 ∷ [])) ∷ meta3 ∷ []) ∷ []))
        (T Machine (T Clos (T EnvSnoc (meta0 ∷ meta2 ∷ []) ∷ meta1 ∷ []) ∷ meta3 ∷ []))

lambda-language : language
lambda-language = Language K _b⇒1_
