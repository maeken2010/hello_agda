module lambda where

record _∧_ A B : Set where
  field
    pi1 : A
    pi2 : B

open _∧_

lemma : {A B C : Set } → (( A → B ) ∧  ( B → C )) → ( A → C  )
lemma {A} {B} {C} f∧g a = {!!}

data _∨_ (A B : Set) : Set where
  p1 : A → A ∨ B
  p2 : B → A ∨ B

ex3 : {A B : Set} → ( A ∨ A ) → A
ex3 (p1 x) = {!!}
ex3 (p2 x) = {!!}
