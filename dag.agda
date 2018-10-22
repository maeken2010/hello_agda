module dag where

--         f0
--       -----→
--    t0         t1
--       -----→
--         f1


data  TwoObject   : Set  where
       t0 : TwoObject
       t1 : TwoObject


data TwoArrow  : TwoObject → TwoObject → Set  where
       f0 :  TwoArrow t0 t1
       f1 :  TwoArrow t0 t1


--         r0
--       -----→
--    t0         t1
--       ←-----
--         r1

data Circle  : TwoObject → TwoObject → Set  where
       r0 :  Circle t0 t1
       r1 :  Circle t1 t0

data ⊥ : Set where

⊥-elim : {A : Set } -> ⊥ -> A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

data Bool  : Set  where
       true :  Bool
       false :  Bool

data connected { V : Set } ( E : V -> V -> Set ) ( x y : V ) : Set  where
    direct :   E x y -> connected E x y 
    indirect :  { z : V  } -> E x z  ->  connected {V} E z y -> connected E x y

lemma1 : connected TwoArrow t0 t1
lemma1 = direct f0

lemma2 : ¬ ( connected TwoArrow t1 t0 )
lemma2 (direct ())
lemma2 (indirect () (direct x1))
lemma2 (indirect () (indirect x1 x2))

-- lemma2 (direct ())
-- lemma2 (indirect () (direct _))
-- lemma2 (indirect () (indirect _ _ ))

lemma3 : connected Circle t0 t0
lemma3 = indirect r0 ( direct r1 )

data Dec (P : Set) : Set where
   yes :   P → Dec P
   no  : ¬ P → Dec P

reachable :  { V : Set } ( E : V -> V -> Set ) ( x y : V ) -> Set
reachable {V} E x y = Dec ( connected {V} E x y )

dag :  { V : Set } ( E : V -> V -> Set ) ->  Set
dag {V} E =  ∀ (n : V)  →  ¬ ( connected E n n )

lemma4 : dag TwoArrow
lemma4 t0 (direct ())
lemma4 t0 (indirect _ (direct ()))
lemma4 t0 (indirect f0 (indirect () _))
lemma4 t0 (indirect f1 (indirect () _))
lemma4 t1 (direct ())
lemma4 t1 (indirect () _)

lemma5 :  ¬ ( dag Circle )
lemma5 x = ⊥-elim (x t0 lemma3)
