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

{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c 

{-
{- Another way to define merge -}
mutual
  merge : List ℕ -> List ℕ -> List ℕ
  merge [] x₁ = x₁
  merge (x ∷ x₂) [] = x ∷ x₂ 
  merge (x ∷ xs) (y ∷ ys) with em x y
  merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ = x ∷ merge xs ( y ∷ ys ) 
  merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ = y ∷ merge' x xs ys 

  merge' : ℕ -> List ℕ -> List ℕ -> List ℕ
  merge' x [] ys = x ∷ ys
  merge' x (x₁ ∷ xs) [] = x ∷ x₁ ∷ xs
  merge' x (x₁ ∷ xs) (y ∷ ys) with em x₁ y
  merge' x (x₁ ∷ xs) (y ∷ ys) | inj₁ x₂ = x ∷ x₁ ∷ merge xs (y ∷ ys)
  merge' x (x₁ ∷ xs) (y ∷ ys) | inj₂ y₁ = x ∷ y ∷ merge' x₁ xs ys
-}

{- Don't try to prove `merge x y ≡ merge y x` -}
{-
merge[] : ( x : List ℕ ) -> x ≡ merge x []
merge[] [] = refl
merge[] (x ∷ x₁) = refl

mergelemma1 : ( x : ℕ ) -> (xs : List ℕ ) -> issorted (x ∷ xs ) -> merge xs (x ∷ []) ≡ x ∷ xs
mergelemma1 x .[] one = refl
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) with em y x
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) | inj₁ x₃ with ≤reflrefl x₁ x₃
mergelemma1 x .(x ∷ L) (two .x .x L x₁ x₂) | inj₁ x₃ | refl = cong (_∷_ x) (mergelemma1 x L x₂)
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) | inj₂ y₁ = refl

mergelemma2 : ( x : ℕ ) -> (xs : List ℕ ) -> issorted (x ∷ xs ) -> merge (x ∷ []) xs ≡ x ∷ xs
mergelemma2 x .[] one = refl
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) with em x y
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) | inj₁ x₃ = refl
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) | inj₂ y₁ with ≤reflrefl x₁ y₁
mergelemma2 x .(x ∷ L) (two .x .x L x₁ x₂) | inj₂ y₁ | refl = cong (_∷_ x) (mergelemma2 x L x₂)

mergelemma3 : ( x : ℕ ) ->  ( ys : List ℕ ) -> issorted ys ->  merge ys (x ∷ []) ≡ merge (x ∷ []) ys
mergelemma3 x .[] nil = refl
mergelemma3 x .(y ∷ []) (one {y}) with em x y | em y x
mergelemma3 x .(y ∷ []) (one {y}) | inj₁ x₁ | inj₁ x₂ with ≤reflrefl x₁ x₂
mergelemma3 x .(y ∷ []) (one {y}) | inj₁ x₁ | inj₁ x₂ | refl = refl
mergelemma3 x .(y ∷ []) (one {y}) | inj₁ x₁ | inj₂ y₁ = refl
mergelemma3 x .(y ∷ []) (one {y}) | inj₂ y₁ | inj₁ x₁ = refl
mergelemma3 x .(y ∷ []) (one {y}) | inj₂ y₁ | inj₂ y₂ with ≤reflrefl y₁ y₂
mergelemma3 x .(y ∷ []) (one {y}) | inj₂ y₁ | inj₂ y₂ | refl = refl
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) with em x₁ x | em x x₁
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₁ x₅ with ≤reflrefl x₄ x₅ | em y x
mergelemma3 x .(x ∷ y ∷ L) (two .x y L x₂ x₃) | inj₁ x₄ | inj₁ x₅ | refl | inj₁ x₁ with ≤reflrefl x₁ x₂
mergelemma3 x .(x ∷ x ∷ L) (two x .x L x₂ x₃) | inj₁ x₄ | inj₁ x₅ | refl | inj₁ x₁ | refl = cong (_∷_ x) ( cong (_∷_ x) (mergelemma1 x L x₃) )
mergelemma3 x .(x ∷ y ∷ L) (two .x y L x₂ x₃) | inj₁ x₄ | inj₁ x₅ | refl | inj₂ y₁ = refl
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ with em y x | em x y
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₁ x₅ | inj₁ x₆ with ≤reflrefl x₆ x₅
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₁ x₅ | inj₁ x₆ | refl = cong (_∷_ x₁) (cong (_∷_ x) (mergelemma1 x L x₃))
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₁ x₅ | inj₂ y₂ = cong (_∷_ x₁) (cong (_∷_ y) (mergelemma3 x L (extractorder y L x₃ )) )
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₂ y₂ | inj₁ x₅ = cong (_∷_ x₁) refl
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₂ y₂ | inj₂ y₃ with ≤reflrefl y₂ y₃
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₁ x₄ | inj₂ y₁ | inj₂ y₂ | inj₂ y₃ | refl = cong (_∷_ x₁) (cong (_∷_ x) ( sym (mergelemma2 x L x₃)))
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₂ y₁ | inj₁ x₄ = refl
mergelemma3 x .(x₁ ∷ y ∷ L) (two x₁ y L x₂ x₃) | inj₂ y₁ | inj₂ y₂ with ≤reflrefl y₁ y₂ | em x y
mergelemma3 x .(x ∷ y ∷ L) (two .x y L x₂ x₃) | inj₂ y₁ | inj₂ y₂ | refl | inj₁ x₁ = cong (_∷_ x) refl
mergelemma3 x .(x ∷ y ∷ L) (two .x y L x₂ x₃) | inj₂ y₁ | inj₂ y₂ | refl | inj₂ y₃ with ≤reflrefl x₂ y₃
mergelemma3 x .(x ∷ y ∷ L) (two .x y L x₂ x₃) | inj₂ y₁ | inj₂ y₂ | refl | inj₂ y₃ | refl = cong (_∷_ x) (cong (_∷_ x)  (sym (mergelemma2 x L x₃)))

mutual
  mergelemma5 :  (x : ℕ) -> (xs ys : List ℕ) -> issorted (x ∷ xs ) -> issorted (x ∷ ys ) -> merge ys (x ∷ xs) ≡ x ∷ merge ys xs
  mergelemma5 x xs .[] x₁ one = refl
  mergelemma5 x xs .(y ∷ L) x₁ (two .x y L x₂ x₃) with em y x
  mergelemma5 x xs .(y ∷ L) x₁ (two .x y L x₂ x₃) | inj₁ x₄ with ≤reflrefl x₂ x₄
  mergelemma5 x .[] .(x ∷ L) one (two .x .x L x₂ x₃) | inj₁ x₄ | refl = cong (_∷_ x) (mergelemma1 x L x₃)
  mergelemma5 x .(y ∷ L₁) .(x ∷ L) (two .x y L₁ x₁ x₅) (two .x .x L x₂ x₃) | inj₁ x₄ | refl with em x y
  mergelemma5 x .(y ∷ L₁) .(x ∷ L) (two .x y L₁ x₁ x₅) (two .x x L x₂ x₃) | inj₁ x₄ | refl | inj₁ x₆ = cong (_∷_ x) (mergelemma5 x (y ∷ L₁) L (two x y L₁ x₁ x₅) x₃ )
  mergelemma5 x .(y ∷ L₁) .(x ∷ L) (two .x y L₁ x₁ x₅) (two .x x L x₂ x₃) | inj₁ x₄ | refl | inj₂ y₁ with ≤reflrefl x₁ y₁
  mergelemma5 x .(y ∷ L₁) .(x ∷ L) (two .x y L₁ x₁ x₅) (two .x x L x₂ x₃) | inj₁ x₄ | refl | inj₂ y₁ | refl = cong (_∷_ x) (begin
    merge L (x ∷ x ∷ L₁)
    ≡⟨ mergelemma5 x (x ∷ L₁) L (two x x L₁ x₂ x₅) x₃  ⟩
    x ∷ merge L (x ∷ L₁)
    ≡⟨ cong (_∷_ x) (mergelemma5 x L₁ L x₅ x₃) ⟩
    x ∷ x ∷ merge L L₁
    ≡⟨ cong (_∷_ x) (sym (mergelemma6 x L L₁ x₃ x₅)) ⟩
    x ∷ merge (x ∷ L) L₁
    ∎)
  mergelemma5 x xs .(y ∷ L) x₁ (two .x y L x₂ x₃) | inj₂ y₁ = refl

  mergelemma6 :  (x : ℕ) -> (xs ys : List ℕ) -> issorted (x ∷ xs ) -> issorted (x ∷ ys ) -> merge (x ∷ xs) ys ≡ x ∷ merge xs ys
  mergelemma6 x .[] ys one x₂ = mergelemma2 x ys x₂
  mergelemma6 x .(y ∷ L) .[] (two .x y L x₁ x₃) one = refl
  mergelemma6 x .(y ∷ L) .(y₁ ∷ L₁) (two .x y L x₁ x₃) (two .x y₁ L₁ x₂ x₄) with em x y₁
  mergelemma6 x .(y ∷ L) .(y₁ ∷ L₁) (two .x y L x₁ x₃) (two .x y₁ L₁ x₂ x₄) | inj₁ x₅ with em y y₁
  mergelemma6 x .(y ∷ L) .(y₁ ∷ L₁) (two .x y L x₁ x₃) (two .x y₁ L₁ x₂ x₄) | inj₁ x₅ | inj₁ x₆ = refl
  mergelemma6 x .(y ∷ L) .(y₁ ∷ L₁) (two .x y L x₁ x₃) (two .x y₁ L₁ x₂ x₄) | inj₁ x₅ | inj₂ y₂ = refl
  mergelemma6 x .(y ∷ L) .(y₁ ∷ L₁) (two .x y L x₁ x₃) (two .x y₁ L₁ x₂ x₄) | inj₂ y₂ with ≤reflrefl x₂ y₂ | em y x
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₁ x₅ with em y x | ≤reflrefl x₁ x₅
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₁ x₅ | inj₁ x₆ | refl = cong (_∷_ x) (begin
    merge (x ∷ x ∷ L) L₁
    ≡⟨ mergelemma6 x (x ∷ L) L₁ (two x x L x₂ x₃) x₄ ⟩
    x ∷ merge (x ∷ L) L₁
    ≡⟨ cong (_∷_ x) (mergelemma6 x L L₁  x₃ x₄)  ⟩
    x ∷ x ∷ merge L L₁
    ≡⟨ cong (_∷_ x) (sym (mergelemma5 x L₁  L x₄ x₃)) ⟩
    x ∷ merge L (x ∷ L₁)
    ∎)
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₁ x₅ | inj₂ y₁ | refl = cong (_∷_ x) (mergelemma6 x (x ∷ L) L₁ (two x x L x₂ x₃) x₄ )
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₂ y₁ with em y x
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₂ y₁ | inj₁ x₅ with ≤reflrefl x₅ y₁
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₂ y₁ | inj₁ x₅ | refl = cong (_∷_ x) (begin
    merge (x ∷ x ∷ L) L₁
    ≡⟨ mergelemma6 x (x ∷ L) L₁ (two x x L x₁ x₃) x₄  ⟩
     x ∷ merge (x ∷ L) L₁
    ≡⟨ cong (_∷_ x) (mergelemma6 x L L₁ x₃ x₄ ) ⟩
      x ∷ x ∷ merge L L₁
    ≡⟨ cong (_∷_ x) (sym (mergelemma5 x L₁ L x₄ x₃)) ⟩
    x ∷ merge L (x ∷ L₁)
    ∎)
  mergelemma6 x .(y ∷ L) .(x ∷ L₁) (two .x y L x₁ x₃) (two .x x L₁ x₂ x₄) | inj₂ y₂ | refl | inj₂ y₁ | inj₂ y₃ = cong (_∷_ x) (mergelemma6 x (y ∷ L) L₁ (two x y L x₁ x₃) x₄)

mergelemma7 : ( x : ℕ ) -> ( xs ys : List ℕ ) -> issorted (x ∷ xs) -> issorted ys -> merge ys (x ∷ xs ) ≡ merge ( x ∷ xs ) ys
mergelemma7 x xs .[] x₁ nil = refl
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) with em x x₂ | em x₂ x
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) | inj₁ x₃ | inj₁ x₄ with ≤reflrefl x₄ x₃
mergelemma7 x xs .(x ∷ []) x₁ (one {.x}) | inj₁ x₃ | inj₁ x₄ | refl = cong (_∷_ x) (sym ( mergelemma1 x xs x₁ ))
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) | inj₁ x₃ | inj₂ y = cong (_∷_ x) (sym (mergelemma3 x₂ xs (extractorder x xs x₁) ) )
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) | inj₂ y | inj₁ x₃ = refl
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) | inj₂ y | inj₂ y₁ with ≤reflrefl y y₁
mergelemma7 x xs .(x₂ ∷ []) x₁ (one {x₂}) | inj₂ y | inj₂ y₁ | refl = cong (_∷_ x) (mergelemma2 x xs x₁)
mergelemma7 x xs .(x₂ ∷ y ∷ L) x₁ (two x₂ y L x₃ x₄) with em x₂ x | em x x₂
mergelemma7 x xs .(x₂ ∷ y ∷ L) x₁ (two x₂ y L x₃ x₄) | inj₁ x₅ | inj₁ x₆ with ≤reflrefl x₆ x₅ | em y x
mergelemma7 x xs .(x ∷ y ∷ L) x₁ (two .x y L x₃ x₄) | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₂ with ≤reflrefl x₂ x₃
mergelemma7 x xs .(x ∷ y ∷ L) x₁ (two .x y L x₃ x₄) | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₂ | refl = {!!}
mergelemma7 x xs .(x ∷ y ∷ L) x₁ (two .x y L x₃ x₄) | inj₁ x₅ | inj₁ x₆ | refl | inj₂ y₁ = {!!}
mergelemma7 x xs .(x₂ ∷ y ∷ L) x₁ (two x₂ y L x₃ x₄) | inj₁ x₅ | inj₂ y₁ = {!!}
mergelemma7 x xs .(x₂ ∷ y ∷ L) x₁ (two x₂ y L x₃ x₄) | inj₂ y₁ | inj₁ x₅ = {!!}
mergelemma7 x xs .(x₂ ∷ y ∷ L) x₁ (two x₂ y L x₃ x₄) | inj₂ y₁ | inj₂ y₂ = {!!}

mergelemma4 : (x y : ℕ) -> ( ys L : List ℕ ) -> x ≤ y -> issorted ( y ∷ L ) -> issorted ys ->  merge ys (x ∷ y ∷ L) ≡ merge (x ∷ y ∷ L) ys
mergelemma4 x y [] L x₁ x₂ x₃ = refl
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ with em x₄ x | em x x₄
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ with ≤reflrefl x₅ x₆
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl with em y x
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₄ with ≤reflrefl x₁ x₄
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₄ | refl = cong (_∷_ x) {!!} {- difficulty -}
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₂ y₁ = cong (_∷_ x) {!!} {- difficulty -}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₂ y₁ = {!!} {- not sure -}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ with em x₄ y | em y x₄
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ | inj₁ x₆ | inj₁ x₇ with ≤reflrefl x₆ x₇
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ | inj₁ x₆ | inj₁ x₇ | refl = {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ | inj₁ x₆ | inj₂ y₂ = {!!} {- todo -}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ | inj₂ y₂ | inj₁ x₆ = {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ | inj₂ y₂ | inj₂ y₃ = {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₂ y₂ with em x₄ y | ≤reflrefl y₂ y₁
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₂ y₂ | inj₁ x₄ | refl = {!!} {- trival -}
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₂ y₂ | inj₂ y₃ | refl = {!!} {- trival -}

mergeswap : ( xs ys  : List ℕ ) -> issorted xs -> issorted ys -> merge ys xs  ≡ merge xs ys 
mergeswap .[] ys nil x₁ = sym (merge[] ys)
mergeswap .(x ∷ []) ys (one {x}) x₁ = mergelemma3 x ys x₁
mergeswap .(x ∷ y ∷ L) ys (two x y L x₂ x₃) x₁ = mergelemma4 x y ys L x₂ x₃ x₁
-}

coqlemma : {x : ℕ}{L1 L2 : List ℕ} -> issorted (x ∷ L1) -> issorted (x ∷ L2) -> issorted (merge L1 L2) -> issorted (x ∷ merge L1 L2)
coqlemma {x} {[]} {L2} x₁ x₂ x₃ = x₂
coqlemma {x} {x₄ ∷ L1} {[]} x₁ x₂ x₃ = x₁
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ x₂ x₃ with em x₄ x₅
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} (two .x .x₄ .L1 x₁ x₇) x₂ x₃ | inj₁ x₆ = two x x₄ (merge L1 (x₅ ∷ L2)) x₁ x₃
coqlemma {x} {x₄ ∷ L1} {x₅ ∷ L2} x₁ (two .x .x₅ .L2 x₂ x₆) x₃ | inj₂ y = two x x₅ (merge (x₄ ∷ L1) L2) x₂ x₃

lemma1 : ( x y : ℕ ) -> (L : List ℕ ) -> y ≤ x -> issorted (y ∷ L) -> issorted (y ∷ merge (x ∷ [] ) L )
lemma1 x y .[] x₁ one = two y x [] x₁ one
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) with em x y₁
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₁ x₄ = two y x (y₁ ∷ L) x₁ (two x y₁ L x₄ x₃)
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₂ y₂ = two y y₁ (merge (x ∷ []) L) x₂ (lemma1 x y₁ L y₂ x₃ )

lemma2 : ( x y : ℕ ) -> (L : List ℕ ) -> y ≤ x -> issorted (y ∷ L) -> issorted (y ∷ merge L (x ∷ [] ) )
lemma2 x y .[] x₁ one = two y x [] x₁ one
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) with em y₁ x
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₁ x₄ = two y y₁ (merge L (x ∷ [])) x₂ (lemma2 x y₁ L x₄ x₃ )
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₂ y₂ = two y x (y₁ ∷ L) x₁ (two x y₁ L y₂ x₃)

mutual
  lemma3 : ( y y₁ : ℕ ) -> ( L L₁ : List ℕ ) -> y ≤ y₁ ->  issorted (y₁ ∷ L₁) ->  issorted (y ∷ L) ->  issorted (y ∷ merge L (y₁ ∷ L₁))
  lemma3 y y₁ .[] L₁ x x₁ one = two y y₁ L₁ x x₁
  lemma3 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) with em y₂ y₁
  lemma3 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₁ x₄ = two y y₂ (merge L (y₁ ∷ L₁)) x₂  (lemma3 y₂ y₁ L L₁ x₄  x₁ x₃)
  lemma3 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₂ y₃ = two y y₁ (merge (y₂ ∷ L) L₁) x (lemma4 y₁ y₂ L₁ L y₃ x₃ x₁ )

  lemma4 : ( y y₁ : ℕ ) -> ( L L₁ : List ℕ ) -> y ≤ y₁ ->  issorted (y₁ ∷ L₁) ->  issorted (y ∷ L) ->  issorted (y ∷ merge (y₁ ∷ L₁) L)
  lemma4 y y₁ .[] L₁ x x₁ one = two y y₁ L₁ x x₁
  lemma4 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) with em y₁ y₂
  lemma4 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₁ x₄ = two y y₁ (merge L₁ (y₂ ∷ L)) x (lemma3 y₁ y₂ L₁ L x₄ x₃ x₁)
  lemma4 y y₁ .(y₂ ∷ L) L₁ x x₁ (two .y y₂ L x₂ x₃) | inj₂ y₃ = two y y₂ (merge (y₁ ∷ L₁) L) x₂ (lemma4 y₂ y₁ L L₁ y₃ x₁ x₃ )

lemma5 : ( x₁ y₁ y : ℕ ) -> ( L L₁ : List ℕ ) ->  y ≤ x₁ -> x₁ ≤ y₁ ->  issorted (y₁ ∷ L₁) ->  issorted ( y ∷ L) -> issorted (y ∷ merge L (x₁ ∷ y₁ ∷ L₁))
lemma5 x₁ y₁ y .[] L₁ x₂ x₃ x₄ one = two y x₁ (y₁ ∷ L₁) x₂ (two x₁ y₁ L₁ x₃ x₄)
lemma5 x₁ y₁ y .(y₂ ∷ L) L₁ x₂ x₃ x₄ (two .y y₂ L x₅ x₆) with em y₂ x₁
lemma5 x₁ y₁ y .(y₂ ∷ L) L₁ x₂ x₃ x₄ (two .y y₂ L x₅ x₆) | inj₁ x₇ = two y y₂ (merge L (x₁ ∷ y₁ ∷ L₁)) x₅ (lemma5 x₁ y₁ y₂ L L₁  x₇ x₃ x₄ x₆)
lemma5 x₁ y₁ y .(y₂ ∷ L) L₁ x₂ x₃ x₄ (two .y y₂ L x₅ x₆) | inj₂ y₃ with em y₂ y₁
lemma5 x₁ y₁ y .(y₂ ∷ L) L₁ x₂ x₃ x₄ (two .y y₂ L x₅ x₆) | inj₂ y₃ | inj₁ x₇ = two y x₁ (y₂ ∷ merge L (y₁ ∷ L₁)) x₂ (two x₁ y₂ (merge L (y₁ ∷ L₁)) y₃ (lemma3 y₂ y₁ L L₁ x₇ x₄ x₆))
lemma5 x₁ y₁ y .(y₂ ∷ L) L₁ x₂ x₃ x₄ (two .y y₂ L x₅ x₆) | inj₂ y₃ | inj₂ y₄ = two y x₁ (y₁ ∷ merge (y₂ ∷ L) L₁) x₂ (two x₁ y₁ (merge (y₂ ∷ L) L₁) x₃ (lemma4 y₁ y₂ L₁ L y₄ x₆ x₄))


lemma6 : ( x y y₁ : ℕ ) -> ( L L₁ : List ℕ ) -> x ≤ y -> y₁ ≤ x ->  issorted (y₁ ∷ L₁) -> issorted (y ∷ L) -> issorted (y₁ ∷ merge (x ∷ y ∷ L) L₁)
lemma6 x y y₁ L .[] x₁ x₂ one x₄ = two y₁ x (y ∷ L) x₂ (two x y L x₁ x₄)
lemma6 x y y₁ L .(y₂ ∷ L₁) x₁ x₂ (two .y₁ y₂ L₁ x₃ x₅) x₄ with em x y₂
lemma6 x y y₁ L .(y₂ ∷ L₁) x₁ x₂ (two .y₁ y₂ L₁ x₃ x₅) x₄ | inj₁ x₆ with em y y₂
lemma6 x y y₁ L .(y₂ ∷ L₁) x₁ x₂ (two .y₁ y₂ L₁ x₃ x₅) x₄ | inj₁ x₆ | inj₁ x₇ = two y₁ x (y ∷ merge L (y₂ ∷ L₁)) x₂ (two x y (merge L (y₂ ∷ L₁)) x₁ (lemma3 y y₂ L L₁ x₇ x₅  x₄))
lemma6 x y y₁ L .(y₂ ∷ L₁) x₁ x₂ (two .y₁ y₂ L₁ x₃ x₅) x₄ | inj₁ x₆ | inj₂ y₃ = two y₁ x (y₂ ∷ merge (y ∷ L) L₁) x₂ (two x y₂ (merge (y ∷ L) L₁) x₆ (lemma4 y₂ y L₁ L  y₃ x₄ x₅))
lemma6 x y y₁ L .(y₂ ∷ L₁) x₁ x₂ (two .y₁ y₂ L₁ x₃ x₅) x₄ | inj₂ y₃ = two y₁ y₂ (merge (x ∷ y ∷ L) L₁) x₃ (lemma6 x y y₂ L  L₁ x₁ y₃ x₅ x₄)


correctness : ( xs ys : List ℕ ) -> issorted xs -> issorted ys -> issorted ( merge xs ys )
correctness [] [] nil nil = nil
correctness [] (x ∷ .[]) nil one = one
correctness [] (x ∷ .(y ∷ L)) nil (two .x y L x₁ x₂) = two x y L x₁ x₂
correctness (x ∷ .[]) [] one nil = one
correctness (x ∷ .(y ∷ L)) [] (two .x y L x₁ x₂) nil = two x y L x₁ x₂
correctness (x ∷ .[]) (x₁ ∷ .[]) one one with em x x₁
correctness (x ∷ .[]) (x₁ ∷ .[]) one one | inj₁ x₂ = two x x₁ [] x₂ one
correctness (x ∷ .[]) (x₁ ∷ .[]) one one | inj₂ y = two x₁ x [] y one
correctness (x ∷ .[]) (x₁ ∷ .(y ∷ L)) one (two .x₁ y L x₂ x₃) with em x x₁
correctness (x ∷ .[]) (x₁ ∷ .(y ∷ L)) one (two .x₁ y L x₂ x₃) | inj₁ x₄ = two x x₁ (y ∷ L) x₄ (two x₁ y L x₂ x₃)
correctness (x ∷ .[]) (x₁ ∷ .(y ∷ L)) one (two .x₁ y L x₂ x₃) | inj₂ y₁ with em x y
correctness (x ∷ .[]) (x₁ ∷ .(y ∷ L)) one (two .x₁ y L x₂ x₃) | inj₂ y₁ | inj₁ x₄ = two x₁ x (y ∷ L) y₁ (two x y L x₄ x₃)
correctness (x ∷ .[]) (x₁ ∷ .(y ∷ L)) one (two .x₁ y L x₂ x₃) | inj₂ y₁ | inj₂ y₂ = two x₁ y (merge (x ∷ []) L) x₂ (lemma1 x y L y₂ x₃ )
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .[]) (two .x y L x₂ x₃) one with em x x₁
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .[]) (two .x y L x₂ x₃) one | inj₁ x₄ with em y x₁
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .[]) (two .x y L x₂ x₃) one | inj₁ x₄ | inj₁ x₅ = two x y (merge L (x₁ ∷ [])) x₂ (lemma2 x₁ y L x₅ x₃ )
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .[]) (two .x y L x₂ x₃) one | inj₁ x₄ | inj₂ y₁ = two x x₁ (y ∷ L) x₄ (two x₁ y L y₁ x₃)
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .[]) (two .x y L x₂ x₃) one | inj₂ y₁ = two x₁ x (y ∷ L) y₁ (two x y L x₂ x₃)
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) with em x x₁ | em y x₁ | em x y₁ | em y y₁
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₁ x₆ | inj₁ x₇ | z | zz = two x y (merge L (x₁ ∷ y₁ ∷ L₁)) x₂ (lemma5 x₁ y₁ y L L₁ x₇ x₄ x₅ x₃ )
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₁ x₆ | inj₂ y₂ | z | inj₁ x₇ = two x x₁ (y ∷ merge L (y₁ ∷ L₁)) x₆ (two x₁ y (merge L (y₁ ∷ L₁)) y₂ (lemma3 y y₁ L L₁ x₇ x₅ x₃ ) )
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₁ x₆ | inj₂ y₂ | z | inj₂ y₃ = two x x₁ (y₁ ∷ merge (y ∷ L) L₁) x₆ (two x₁ y₁ (merge (y ∷ L) L₁) x₄ (lemma4 y₁ y L₁ L y₃ x₃ x₅) )
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₂ y₂ | z | inj₁ x₆ | inj₁ x₇ = two x₁ x (y ∷ merge L (y₁ ∷ L₁)) y₂ (two x y (merge L (y₁ ∷ L₁)) x₂ (lemma3 y y₁ L L₁ x₇ x₅ x₃ ))
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₂ y₂ | z | inj₁ x₆ | inj₂ y₃ = two x₁ x (y₁ ∷ merge (y ∷ L) L₁) y₂ (two x y₁ (merge (y ∷ L) L₁) x₆ (lemma4 y₁ y L₁ L y₃ x₃ x₅ ))
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) | inj₂ y₂ | z | inj₂ y₃ | zz = two x₁ y₁ (merge (x ∷ y ∷ L) L₁) x₄ (lemma6 x y y₁ L L₁ x₂ y₃ x₅ x₃) 

_≼_ : ∀ {a} {A : Set a} → Rel (List A) _
x ≼ x₁ = ( length x )   ≤′ length x₁

partition : List ℕ -> List ℕ × List ℕ
partition [] = [] , []
partition (x ∷ []) = x ∷ [] , []
partition (x ∷ x₁ ∷ xs) with partition xs
partition (x ∷ x₁ ∷ xs) | fst , snd = x ∷ fst , x₁ ∷ snd

partition-size : (xs : List ℕ) → proj₁ (partition xs) ≼ xs × proj₂ (partition xs) ≼ xs
partition-size [] = _≤′_.≤′-refl , _≤′_.≤′-refl
partition-size (x ∷ []) = _≤′_.≤′-refl , _≤′_.≤′-step _≤′_.≤′-refl
partition-size (x ∷ x₁ ∷ xs) with partition xs | partition-size xs
partition-size (x ∷ x₁ ∷ xs) | fst , snd | fst₁ , snd₁ = s≤′s (_≤′_.≤′-step fst₁) , s≤′s (_≤′_.≤′-step snd₁)

{-
_≼_ : ∀ {a} {A : Set a} → Rel (List A) _
x ≼ x₁ = ( length x )  ≤ length x₁

partition-size : (xs : List ℕ) → proj₁ (partition xs) ≼ xs × proj₂ (partition xs) ≼ xs
partition-size [] = ≤-reflex , ≤-reflex
partition-size (x ∷ []) = ≤-reflex , s≤s ≤-reflex
partition-size (x ∷ x₁ ∷ xs) with partition xs | partition-size xs
partition-size (x ∷ x₁ ∷ xs) | fst , snd | fst₁ , snd₁ = sucsuc _ _ (s≤s fst₁) , sucsuc _ _ (s≤s snd₁)
-}

{-
example : ( partition ( 1 ∷ 2 ∷ [] ) ) ≡ ( 1 ∷ 2 ∷ [] , [] )
example with ( partition ( 2 ∷ [] ) ) ≡ ( 2 ∷ [] , []) 
example | z = refl

partition-size : (xs : List ℕ) → proj₁ (partition xs) ≼ xs × proj₂ (partition xs) ≼ xs
partition-size [] = ≤-reflex , ≤-reflex
partition-size (x ∷ xs) with partition xs | partition-size xs
partition-size (x ∷ xs) | fst , snd | fst₁ , snd₁ = sucsuc _ _ fst₁ , s≤s snd₁
-}


mergesort' : ( xs : List ℕ ) -> Acc  _<′_ (length xs) -> List ℕ
mergesort' [] _ = []
mergesort' (x ∷ []) _ = x ∷ []
mergesort' (x ∷ x₁ ∷ xs) (acc rs) with partition xs | partition-size xs
mergesort' (x ∷ x₁ ∷ xs) (acc rs) | fst , snd | fst₁ , snd₁ = merge (mergesort' ( x ∷ fst ) (rs _ (s≤′s (s≤′s fst₁))) ) (mergesort' (x₁ ∷ snd) (rs _ (s≤′s (s≤′s snd₁))))


mergesort : List ℕ -> List ℕ
mergesort xs = mergesort' xs (<′-wellFounded (length xs))

mergesortcorrectness' : ( xs : List ℕ ) -> ( a :  Acc  _<′_ (length xs)) -> issorted (mergesort' xs a)
mergesortcorrectness' [] a = nil
mergesortcorrectness' (x ∷ []) a = one
mergesortcorrectness' (x ∷ x₁ ∷ xs) (acc rs) with partition xs | partition-size xs
mergesortcorrectness' (x ∷ x₁ ∷ xs) (acc rs) | fst , snd | fst₁ , snd₁ = correctness (mergesort' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesort' (x₁ ∷ snd)  (rs _ (s≤′s (s≤′s snd₁)))) (mergesortcorrectness' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesortcorrectness' (x₁ ∷ snd) (rs _ (s≤′s (s≤′s snd₁)))) 

mergesortcorrectness : ( xs : List ℕ ) -> issorted (mergesort xs)
mergesortcorrectness xs = mergesortcorrectness' xs (acc (<′-wellFounded′ (length xs) ))

data Permutation : List ℕ -> List ℕ -> Set where
  [][] : Permutation [] []
  skip : {l l' : List ℕ} -> ( x : ℕ ) -> Permutation l l' -> Permutation (x ∷ l) (x ∷ l')
  swap : {l : List ℕ} -> (x y : ℕ) -> Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  permtrans : {l l' l'' : List ℕ} -> Permutation l l' -> Permutation l' l'' -> Permutation l l''

permutation-refl : (xs : List ℕ ) -> Permutation xs xs
permutation-refl [] = [][]
permutation-refl (x ∷ xs) = skip x (permutation-refl xs)

permutation-swap : {xs ys : List ℕ} -> Permutation xs ys -> Permutation ys xs
permutation-swap {.[]} {.[]} [][] = [][]
permutation-swap {.(x ∷ _)} {.(x ∷ _)} (skip x x₁) = skip x (permutation-swap x₁)
permutation-swap {.(x ∷ y ∷ _)} {.(y ∷ x ∷ _)} (swap x y) = swap y x
permutation-swap {xs} {ys} (permtrans x x₁) = permtrans (permutation-swap x₁) (permutation-swap x)

++swap : (xs ys : List ℕ ) -> Permutation ( xs ++ ys ) (ys ++ xs)
++swap [] ys  rewrite Data.List.Properties.++-identityʳ ys  = permutation-refl ys
++swap (x ∷ xs) [] rewrite Data.List.Properties.++-identityʳ (x ∷ xs ) = permutation-refl (x ∷ xs) 
++swap (x ∷ xs) (y ∷ ys) with ++swap xs (y ∷ ys) | ++swap (x ∷ xs) ys | ++swap ys xs  {- surprise -}
++swap (x ∷ xs) (y ∷ ys) | z | g | c = permtrans (skip x z) (permtrans (permtrans (swap x y ) (skip y (skip x c))) (skip y g))

++merge : (xs ys : List ℕ ) -> Permutation ( xs ++ ys ) (merge xs ys )
++merge [] ys = permutation-refl ys
++merge (x ∷ xs) [] rewrite Data.List.Properties.++-identityʳ (x ∷ xs ) = permutation-refl (x ∷ xs)
++merge (x ∷ xs) (y ∷ ys) with em x y | ++merge xs (y ∷ ys) | ++merge (x ∷ xs) ys
++merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | a | b = skip x a
++merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | a | b = permtrans (++swap (x ∷ xs) (y ∷ ys)) (skip y (permtrans (++swap ys (x ∷ xs)) b ))

++partition : (xs : List ℕ ) -> Permutation xs  (( proj₁ (partition xs)) ++  (proj₂ (partition xs)) )
++partition [] = [][]
++partition (x ∷ []) = skip x [][]
++partition (x ∷ x₁ ∷ xs) with partition xs | ++partition xs
++partition (x ∷ x₁ ∷ xs) | fst , snd | z = skip x (permtrans (skip x₁ (permtrans z (++swap fst snd) )) (++swap (x₁ ∷ snd ) fst ))

mergepermutation : (xs : List ℕ ) -> Permutation xs (merge (proj₁ (partition xs)) (proj₂ (partition xs)) )
mergepermutation xs with partition xs | ++partition xs 
mergepermutation xs | fst , snd | z = permtrans z (++merge fst snd)


mergel : (xs1 xs2 ys : List ℕ) -> Permutation xs1 xs2 -> Permutation (ys ++ xs1) (ys ++ xs2  )
mergel xs1 xs2 [] p = p
mergel xs1 xs2 (y ∷ ys) p = skip y (mergel xs1 xs2 ys p)

merger :  (xs1 xs2 ys : List ℕ) -> Permutation xs1 xs2 -> Permutation (xs1 ++ ys) ( xs2 ++ ys )
merger xs1 xs2 ys x = permtrans (++swap xs1 ys ) (permtrans (mergel xs1 xs2 ys x) (++swap ys xs2 ) )

mergesortpermutation' : (xs : List ℕ ) ->  ∀ ( a :  Acc  _<′_ (length xs)) -> Permutation xs (mergesort' xs a)
mergesortpermutation' [] a = [][]
mergesortpermutation' (x ∷ []) a = skip x [][]
mergesortpermutation' (x ∷ x₁ ∷ xs) (acc rs) with partition xs | partition-size xs | mergepermutation (x ∷ x₁ ∷ xs )
mergesortpermutation' (x ∷ x₁ ∷ xs) (acc rs) | fst , snd | fst₁ , snd₁ | z = permtrans (permtrans z (permtrans (permtrans (permutation-swap (++merge (x ∷ fst) (x₁ ∷ snd)) ) (merger (x ∷ fst ) (mergesort' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (x₁ ∷ snd) (mergesortpermutation' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁))) ) )) (mergel (x₁ ∷ snd) (mergesort' (x₁ ∷ snd) (rs _ (s≤′s (s≤′s snd₁)))) (mergesort' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesortpermutation' (x₁ ∷ snd ) (rs _ (s≤′s (s≤′s snd₁))))))) (++merge (mergesort' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesort' (x₁ ∷ snd)  (rs _ (s≤′s (s≤′s snd₁)))) )

mergesortpermutation : ( xs : List ℕ ) -> Permutation xs ( mergesort xs )
mergesortpermutation xs = mergesortpermutation' xs (acc (<′-wellFounded′ (length xs) ))

