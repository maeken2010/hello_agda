module level1 where

open import Level

ex1 : { A B : Set} → Set
ex1 {A} {B} =  A → B

ex2 : { A B : Set} →  ( A → B ) → Set
ex2 {A} {B}  A→B  =  ex1 {A} {B}


-- record FuncBad (A B : Set) : Set where
--   field
--      func : A → B → Set

record Func {n : Level} (A B : Set n ) : Set (suc n) where
  field
    func :  A → B  → Set n

record Func2 {n : Level} (A B : Set n ) : Set (suc n)  where
  field
    func : A → B  → Func A B
