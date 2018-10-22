module data1 where

data _∨_ (A B : Set) : Set where
  p1 : A → A ∨ B
  p2 : B → A ∨ B

ex1 : {A B : Set} → A → ( A ∨ B ) 
ex1 a = p1 a

ex2 : {A B : Set} → B → ( A ∨ B ) 
ex2 b = p2 b

ex3 : {A B : Set} → ( A ∨ A ) → A 
ex3 (p1 x) = x
ex3 (p2 x) = x

ex4 : {A B C : Set} →  A ∨ ( B ∨ C ) → ( A ∨ B ) ∨ C 
ex4 (p1 x) = p1 (p1 x)
ex4 (p2 (p1 x)) = p1 (p2 x)
ex4 (p2 (p2 x)) = p2 x

record _∧_ A B : Set where
  field
     pi1 : A
     pi2 : B

open _∧_

--- ex5 :  {A B C : Set} →  (( A → C ) ∨ ( B  → C ) ) → ( ( A ∨  B ) → C ) is wrong
ex5 :  {A B C : Set} →  (( A → C ) ∨ ( B  → C ) ) → ( ( A ∧  B ) → C )
ex5 (p1 x) x1 = x (pi1 x1)
ex5 (p2 x) x1 = x (pi2 x1)

data Three : Set where
  t1 : Three
  t2 : Three
  t3 : Three

open Three

infixl 110 _∨_ 

data 3Ring : (dom cod : Three) → Set where
   r1 : 3Ring t1 t2
   r2 : 3Ring t2 t3
   r3 : 3Ring t3 t1


data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

add : ( a b : Nat ) → Nat
add zero x = x
add (suc x) y = suc ( add x y )

mul : ( a b : Nat ) → Nat
mul zero x = zero
mul (suc x) y = add (mul x y) y

ex6 : Nat
ex6 = mul ( suc ( suc zero)) (suc ( suc ( suc zero)) )
