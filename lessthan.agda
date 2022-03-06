open import Category.Applicative  using (RawApplicative)
open import Data.Char             using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_;  _<′_; _≤′_)
open import Data.Nat.Properties   -- you can use it all!
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   hiding (merge; partition)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Product          using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; map)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Data.Unit             using (⊤; tt)
open import Data.Empty            using (⊥; ⊥-elim)
open import Function   as F       using (_∘′_; id)
open import IO.Primitive          using (IO)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning 
open import Relation.Nullary      using (¬_; Dec; yes; no)
open import Induction.WellFounded
open import Relation.Unary
open import Relation.Binary
open import Data.Nat.Induction

data _≤_ : ℕ -> ℕ -> Set where
  z≤n : {n : ℕ} -> zero  ≤ n
  s≤s : {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

transitive : {a b c : ℕ} -> a ≤ b -> b ≤ c -> a ≤ c
transitive {.zero} {b} {c} z≤n x₁ = z≤n
transitive {.(suc _)} {.(suc _)} {.(suc _)} (s≤s x) (s≤s x₁) = s≤s (transitive x x₁)

em : ( m n : ℕ ) -> ( m ≤ n ) ⊎ ( n ≤ m )      
em zero zero = inj₁ z≤n
em zero (suc n) = inj₁ z≤n
em (suc m) zero = inj₂ z≤n
em (suc m) (suc n) with em m n
em (suc m) (suc n) | inj₁ x = inj₁ (s≤s x)
em (suc m) (suc n) | inj₂ y = inj₂ (s≤s y)


≤reflrefl : {m n : ℕ} -> m ≤ n -> n ≤ m -> m ≡ n
≤reflrefl {.zero} {.zero} z≤n z≤n = refl
≤reflrefl {.(suc _)} {.(suc _)} (s≤s x) (s≤s x₁) = cong suc (≤reflrefl x x₁)
