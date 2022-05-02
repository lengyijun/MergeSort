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


data sorted : List ℕ -> Set where
  nil : sorted []
  one : {x : ℕ } -> sorted ( x ∷ [] )
  two : (x y : ℕ ) -> (L : List ℕ ) -> x ≤ y -> sorted ( y ∷ L ) -> sorted ( x ∷ y ∷ L )

sorted-inv : {x : ℕ}{l : List ℕ } -> sorted ( x ∷ l ) -> sorted l
sorted-inv {x} {.[]} one = nil
sorted-inv {x} {.(y ∷ L)} (two .x y L x₁ x₂) = x₂

{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c 



coqlemma : {x : ℕ}{L1 L2 : List ℕ} -> sorted (x ∷ L1) -> sorted (x ∷ L2) -> sorted (merge L1 L2) -> sorted (x ∷ merge L1 L2)
coqlemma {x} {[]} {L2} x₁ x₂ x₃ = x₂
coqlemma {x} {x₄ ∷ L1} {[]} x₁ x₂ x₃ = x₁
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ x₂ x₃ with em x₄ x₅
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} (two .x .x₄ .L1 x₁ x₇) x₂ x₃ | inj₁ x₆ = two x x₄ (merge L1 (x₅ ∷ L2)) x₁ x₃
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ (two .x .x₅ .L2 x₂ x₆) x₃ | inj₂ y = two x x₅ (merge (x₄ ∷ L1) L2) x₂ x₃


sorted-merge' : { xs ys : List ℕ } -> sorted xs -> sorted ys -> Acc  _<′_ (length xs + length ys) -> sorted ( merge xs ys )
sorted-merge' {[]} {ys} x x₁ x₂ = x₁
sorted-merge' {x₃ ∷ xs} {[]} x x₁ x₂ = x
sorted-merge' {x₃ ∷ xs} {x₄ ∷ ys} x x₁ (acc rs) with em x₃ x₄
sorted-merge' {x₃ ∷ xs} {x₄ ∷ ys} x x₁ (acc rs) | inj₁ x₂ = coqlemma x (two x₃ x₄ ys x₂ x₁) ((sorted-merge' (sorted-inv x) x₁ (rs _ (  _≤′_.≤′-refl))))
sorted-merge' {x₃ ∷ xs} {x₄ ∷ ys} x x₁ (acc rs) | inj₂ y = coqlemma (two x₄ x₃ xs y x ) x₁ (sorted-merge' x (sorted-inv x₁) (rs _ lemma)) where
  lemma :  suc (suc (foldr (λ _ → suc) 0 xs + length ys)) ≤′ suc (foldr (λ _ → suc) 0 xs + suc (foldr (λ _ → suc) 0 ys))
  lemma rewrite +-comm (foldr (λ _ → suc) 0 xs)  (suc (foldr (λ _ → suc) 0 ys)) | +-comm (foldr (λ _ → suc) 0 ys) (foldr (λ _ → suc) 0 xs) = _≤′_.≤′-refl

sorted-merge : { xs ys : List ℕ } -> sorted xs -> sorted ys -> sorted ( merge xs ys )
sorted-merge {xs} {ys} x x₁ =  sorted-merge' x x₁ (<′-wellFounded (length xs + length ys)) 
