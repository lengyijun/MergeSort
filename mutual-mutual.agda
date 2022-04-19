open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_;  _<′_; _≤′_)
open import Data.Nat.Properties  
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   hiding (merge; partition)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Product          using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; map)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Data.Unit             using (⊤; tt)
open import Data.Empty            using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary      using (¬_; Dec; yes; no)
open import Induction.WellFounded
open import Relation.Binary
open import Data.Nat.Induction

data _≤_ : ℕ  -> ℕ -> Set where
  ≤-reflex : {n : ℕ } -> n ≤ n
  s≤s : {n m : ℕ } -> ( n ≤ m ) -> (  n  ≤  suc m )

zero≤n : ( n : ℕ )  -> zero ≤ n
zero≤n zero = ≤-reflex
zero≤n (suc n) = s≤s (zero≤n n)

transitive : { n m o : ℕ } -> n ≤ m -> m ≤ o -> n ≤ o
transitive {n} {.n} {o} ≤-reflex x₁ = x₁
transitive {n} {.(suc _)} {.(suc _)} (s≤s x) ≤-reflex = s≤s x
transitive {n} {.(suc _)} {.(suc _)} (s≤s x) (s≤s x₁) = s≤s (transitive x (transitive (s≤s ≤-reflex) x₁))

sucsuc : (n m : ℕ ) -> n ≤ m -> (suc n ) ≤ (suc m )
sucsuc n .n ≤-reflex = ≤-reflex
sucsuc n .(suc m) (s≤s {m = m} x) = transitive (sucsuc _ _ x) (s≤s ≤-reflex)

em : ( m n : ℕ ) -> ( m ≤ n ) ⊎ ( n ≤ m )
em zero n = inj₁ (zero≤n n)
em (suc m) zero = inj₂ (zero≤n (suc m))
em (suc m) (suc n) with em m n
em (suc m) (suc n) | inj₁ x = inj₁ (sucsuc _ _ x)
em (suc m) (suc n) | inj₂ y = inj₂ (sucsuc _ _ y)

≤reflrefl : {m n : ℕ} -> m ≤ n -> n ≤ m -> m ≡ n
≤reflrefl {m} {.m} ≤-reflex x₁ = refl
≤reflrefl {.(suc _)} {.(suc _)} (s≤s x) ≤-reflex = refl
≤reflrefl {.(suc m)} {.(suc _)} (s≤s x) (s≤s {m = m} x₁) with transitive (s≤s ≤-reflex) x₁ |  transitive (s≤s ≤-reflex) x
≤reflrefl {.(suc m)} {.(suc _)} (s≤s x) (s≤s {m = m} x₁) | a | b = cong suc (≤reflrefl b a)
  
data issorted : List ℕ -> Set where
  nil : issorted []
  one : {x : ℕ } -> issorted ( x ∷ [] )
  two : (x y : ℕ ) -> (L : List ℕ ) -> x ≤ y -> issorted ( y ∷ L ) -> issorted ( x ∷ y ∷ L )

extractorder : (x : ℕ) -> (l : List ℕ ) -> issorted ( x ∷ l ) -> issorted l
extractorder x .[] one = nil
extractorder x .(y ∷ L) (two .x y L x₁ x₂) = x₂

{-
{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c 
-}


{- Another way to define merge -}
mutual
  merge : List ℕ -> List ℕ -> List ℕ
  merge [] x₁ = x₁
  merge (x ∷ x₂) [] = x ∷ x₂ 
  merge (x ∷ xs) (y ∷ ys) with em x y
  merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ = x ∷ merge xs ( y ∷ ys ) 
  merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ = y ∷ merge' x xs ys 

  merge' : ℕ -> List ℕ -> List ℕ -> List ℕ
  merge' x x₁ [] = x ∷ x₁
  merge' x x₁ (x₂ ∷ x₃) with em x x₂
  merge' x x₁ (x₂ ∷ x₃) | inj₁ x₄ = x ∷ merge x₁ (x₂ ∷ x₃)
  merge' x x₁ (x₂ ∷ x₃) | inj₂ y = x₂ ∷ merge' x x₁ x₃



coqlemma : {x : ℕ}{L1 L2 : List ℕ} -> issorted (x ∷ L1) -> issorted (x ∷ L2) -> issorted (merge L1 L2) -> issorted (x ∷ merge L1 L2)
coqlemma {x} {[]} {L2} x₁ x₂ x₃ = x₂
coqlemma {x} {x₄ ∷ L1} {[]} x₁ x₂ x₃ = x₁
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ x₂ x₃ with em x₄ x₅
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} (two .x .x₄ .L1 x₁ x₇) x₂ x₃ | inj₁ x₆ = two x x₄ (merge L1 (x₅ ∷ L2)) x₁ x₃
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ (two .x .x₅ .L2 x₂ x₆) x₃ | inj₂ y = two x x₅ _ x₂ x₃


merge-refl : {x : ℕ}{xs ys : List ℕ} -> merge' x xs ys ≡ merge ( x ∷ xs) ys
merge-refl {x} {xs} {[]} = refl
merge-refl {x} {xs} {x₁ ∷ ys} with em x x₁
merge-refl {x} {xs} {x₁ ∷ ys} | inj₁ x₂ = refl
merge-refl {x} {xs} {x₁ ∷ ys} | inj₂ y = refl


narrow : {x y : ℕ}{l : List ℕ} -> x ≤ y -> issorted (y ∷ l) -> issorted (x ∷ l)
narrow {x} {y} {[]} x₁ x₂ = one
narrow {x} {y} {x₃ ∷ l} x₁ (two .y .x₃ .l x₂ x₄) = two x x₃ l (transitive x₁ x₂) x₄

mutual
  correctness : { xs ys : List ℕ } -> issorted xs -> issorted ys -> issorted ( merge xs ys )
  correctness {[]} {ys} x x₁ = x₁
  correctness {(x₂ ∷ xs)} {[]} x x₁ = x
  correctness {(x₂ ∷ xs)} {(x₃ ∷ ys)} x x₁ with em x₂ x₃
  correctness {(x₂ ∷ xs)} {(x₃ ∷ ys)} x x₁ | inj₁ x₄  = coqlemma x (two x₂ x₃ ys x₄ x₁) (correctness {xs} {x₃ ∷ ys} (extractorder _ _ x) x₁)
  correctness {(x₂ ∷ xs)} {(x₃ ∷ ys)} x x₁ | inj₂ y rewrite merge-refl {x₂} {xs} {ys} = coqlemma (two x₃ x₂ xs y x) x₁ (correctness-aux {x₂} {xs} {ys} x (extractorder _ _ x₁))

  correctness-aux : {x : ℕ}{ xs ys : List ℕ } -> issorted (x ∷ xs) -> issorted ys -> issorted ( merge (x ∷ xs) ys )
  correctness-aux {x} {xs} {[]} x₁ x₂ = x₁
  correctness-aux {x} {xs} {x₃ ∷ ys} x₁ x₂ with em x x₃
  correctness-aux {x} {xs} {x₃ ∷ ys} x₁ x₂ | inj₁ x₄ = coqlemma x₁ (two x x₃ ys x₄ x₂) ( (correctness {xs} {x₃ ∷ ys} (extractorder _ _ x₁) x₂ ))
  correctness-aux {x} {xs} {x₃ ∷ ys} x₁ x₂ | inj₂ y rewrite merge-refl {x} {xs} {ys}  = coqlemma (two x₃ x xs y x₁) x₂ (correctness-aux {x} {xs} {ys} x₁ (extractorder _ _ x₂))
