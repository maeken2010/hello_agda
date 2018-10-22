module equality where


data _==_ {A : Set} : A → A → Set where
   refl :  {x : A} → x == x

ex1 : {A : Set} {x : A} → x == x
ex1 = refl

ex2 : {A : Set} {x y : A } → x == y → y == x
ex2 refl = refl

ex3 : {A : Set} {x y z : A } → x == y → y == z → x == z
ex3 x1 refl = x1

ex4 : {A B : Set} {x y : A} {f : A → B} → x == y → f x == f y
ex4 refl = refl
