open import Data.Nat              using (ℕ; zero; suc; _+_; _*_; _<′_; _≤′_)
open import Data.Nat.Properties  
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   hiding (merge; partition)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Relation.Nullary      using (¬_; Dec; yes; no)


mutual
  merge : List ℕ -> List ℕ -> List ℕ
  merge [] x₁ = x₁
  merge (x ∷ x₂) [] = x ∷ x₂  
  merge (x ∷ xs) (y ∷ ys) with x ≤? y
  merge (x ∷ xs) (y ∷ ys) | yes _ = x ∷ merge xs (y ∷ ys)
  merge (x ∷ xs) (y ∷ ys) | no _ = y ∷ merge' x xs ys
  
  merge' : ℕ -> List ℕ -> List ℕ -> List ℕ
  merge' x x₁ [] = x ∷ x₁
  merge' x xs (y ∷ ys) with  x ≤? y
  merge' x xs (y ∷ ys)  | yes _ = x ∷ merge xs (y ∷ ys)
  merge' x xs (y ∷ ys)  | no _ = y ∷ merge' x xs ys
