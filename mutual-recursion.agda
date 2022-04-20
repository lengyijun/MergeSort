open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_; _<′_; _≤′_)
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

zero≤n : ( n : ℕ )  -> zero ≤′ n
zero≤n zero = _≤′_.≤′-refl
zero≤n (suc n) = _≤′_.≤′-step (zero≤n n)


sucsuc : (n m : ℕ ) -> n ≤′ m -> (suc n ) ≤′ (suc m )
sucsuc n .n _≤′_.≤′-refl = _≤′_.≤′-refl
sucsuc n .(suc n₁) (_≤′_.≤′-step {n₁} x) = _≤′_.≤′-step (sucsuc n n₁ x)


em : ( m n : ℕ ) -> ( m ≤′ n ) ⊎ ( n ≤′ m )
em zero n = inj₁ (zero≤n n)
em (suc m) zero = inj₂ (zero≤n (suc m))
em (suc m) (suc n) with em m n
em (suc m) (suc n) | inj₁ x = inj₁ (sucsuc _ _ x)
em (suc m) (suc n) | inj₂ y = inj₂ (sucsuc _ _ y)


{- ok -}
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

{-
{- A ok -}
mutual
  jiting : List ℕ -> List ℕ
  jiting [] = []
  jiting (x ∷ x₁) = x ∷ jiqian x₁ 

  jiqian : List ℕ -> List ℕ
  jiqian x = jiting x
-}

{-
{- B wrong -}
mutual
  jiting : List ℕ -> List ℕ
  jiting [] = []
  jiting (x ∷ x₁) = x ∷ jiqian ( 0 ∷ x₁ ) 

  jiqian : List ℕ -> List ℕ
  jiqian x = jiting x
-}


{- C ok -}
mutual
  jiting : List ℕ -> List ℕ
  jiting [] = []
  jiting (x ∷ x₁) = x ∷ jiqian ( 0 ∷ x₁ ) 

  jiqian : List ℕ -> List ℕ
  jiqian [] = []
  jiqian (x ∷ x₁) = x ∷ jiting x₁


{- D wrong -}
mutual
  jiting : List ℕ -> List ℕ
  jiting [] = []
  jiting (x ∷ x₁) = x ∷ jiqian ( 0 ∷ 0 ∷ x₁ ) 

  jiqian : List ℕ -> List ℕ
  jiqian [] = []
  jiqian (x ∷ x₁) = x ∷ jiting x₁


{-
{- E wrong -}
  jiting : List ℕ -> List ℕ
  jiting x = jiqian x
  
  jiqian : List ℕ -> List ℕ
  jiqian x = jiting x
-}
