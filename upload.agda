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


data issorted : List ℕ -> Set where
  nil : issorted []
  one : {x : ℕ } -> issorted ( x ∷ [] )
  two : (x y : ℕ ) -> (L : List ℕ ) -> x ≤′ y -> issorted ( y ∷ L ) -> issorted ( x ∷ y ∷ L )



{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c 


mutual
  lemma3 : { y y₁ : ℕ } -> ( L L₁ : List ℕ ) -> y ≤′ y₁ ->  issorted (y₁ ∷ L₁) ->  issorted (y ∷ L) ->  issorted (y ∷ merge L (y₁ ∷ L₁))
  lemma3 {y} {y₁} .[] L₁ x x₁ one = two y y₁ L₁ x x₁
  lemma3 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) with em y₂ y₁
  lemma3 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₁ x₄ = two y y₂ (merge L (y₁ ∷ L₁)) x₂  (lemma3  L L₁ x₄  x₁ x₃)
  lemma3 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₂ y₃ = two y y₁ (merge (y₂ ∷ L) L₁) x (lemma4 L₁ L y₃ x₃ x₁ )

  lemma4 : { y y₁ : ℕ } -> ( L L₁ : List ℕ ) -> y ≤′ y₁ ->  issorted (y₁ ∷ L₁) ->  issorted (y ∷ L) ->  issorted (y ∷ merge (y₁ ∷ L₁) L)
  lemma4 {y} {y₁} .[] L₁ x x₁ one = two y y₁ L₁ x x₁
  lemma4 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) with em y₁ y₂
  lemma4 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₁ x₄ = two y y₁ (merge L₁ (y₂ ∷ L)) x (lemma3 L₁ L x₄ x₃ x₁)
  lemma4 {y} {y₁} .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₂ y₃ = two y y₂ (merge (y₁ ∷ L₁) L) x₂ (lemma4 L L₁ y₃ x₁ x₃ )
