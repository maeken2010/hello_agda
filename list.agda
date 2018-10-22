module list where
                                                                        
postulate A : Set

postulate a : A
postulate b : A
postulate c : A


infixr 40 _::_
data  List  (A : Set ) : Set  where
   [] : List A
   _::_ : A → List A → List A


infixl 30 _++_
_++_ :   {A : Set } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

l1 = a :: []
l2 = a :: b :: a :: c ::  []

l3 = l1 ++ l2

data Node  ( A : Set  ) : Set  where
   leaf  : A → Node A
   node  : Node A → Node A → Node A

flatten :  { A : Set } → Node A → List A
flatten ( leaf a )   = a :: []
flatten ( node a b ) = flatten a ++ flatten b

n1 = node ( leaf a ) ( node ( leaf b ) ( leaf c ))

open  import  Relation.Binary.PropositionalEquality

++-assoc :  (L : Set ) ( xs ys zs : List L ) → (xs ++ ys) ++ zs  ≡ xs ++ (ys ++ zs)
++-assoc A [] ys zs = let open ≡-Reasoning in
  begin -- to prove ([] ++ ys) ++ zs  ≡ [] ++ (ys ++ zs)
   ( [] ++ ys ) ++ zs
  ≡⟨ refl ⟩
    ys ++ zs
  ≡⟨ refl ⟩
    [] ++ ( ys ++ zs )
  ∎
  
++-assoc A (x :: xs) ys zs = let open  ≡-Reasoning in
  begin -- to prove ((x :: xs) ++ ys) ++ zs == (x :: xs) ++ (ys ++ zs)
    ((x :: xs) ++ ys) ++ zs
  ≡⟨ refl ⟩
     (x :: (xs ++ ys)) ++ zs
  ≡⟨ refl ⟩
    x :: ((xs ++ ys) ++ zs)
  ≡⟨ cong (_::_ x) (++-assoc A xs ys zs) ⟩ 
    x :: (xs ++ (ys ++ zs))
  ≡⟨ refl ⟩
    (x :: xs) ++ (ys ++ zs)
  ∎


open import Data.Nat

length : {L : Set} → List L → ℕ
length [] = zero
length (_ :: T ) = suc ( length T )

lemma : {L : Set} → (x y : List L ) → ( length x + length y ) ≡ length ( x ++ y )
lemma [] [] = refl
lemma [] (_ :: _) = refl
lemma (H :: T) L =  let open  ≡-Reasoning in
  begin
    (length (H :: T)) + length L
  ≡⟨ cong (_+_ 1) (lemma T L) ⟩
    1 + length (T ++ L)
  ∎
