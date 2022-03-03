
{-# OPTIONS --type-in-type --guardedness #-}


module Three where

open import Category.Applicative  using (RawApplicative)
open import Data.Char             using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties   -- you can use it all!
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   as L      using (List; []; _∷_; map)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Vec   as V
  using (Vec; []; _∷_; _++_; replicate; map; splitAt)
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
  
data isorder : List ℕ -> Set where
  nil : isorder []
  one : {x : ℕ } -> isorder ( x ∷ [] )
  two : (x y : ℕ ) -> (L : List ℕ ) -> x ≤ y -> isorder ( y ∷ L ) -> isorder ( x ∷ y ∷ L )

extractorder : (x : ℕ) -> (l : List ℕ ) -> isorder ( x ∷ l ) -> isorder l
extractorder x .[] one = nil
extractorder x .(y ∷ L) (two .x y L x₁ x₂) = x₂

{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = x ∷ b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = y ∷ c 

merge[] : ( x : List ℕ ) -> x ≡ merge x []
merge[] [] = refl
merge[] (x ∷ x₁) = refl

mergelemma1 : ( x : ℕ ) -> (xs : List ℕ ) -> isorder (x ∷ xs ) -> merge xs (x ∷ []) ≡ x ∷ xs
mergelemma1 x .[] one = refl
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) with em y x
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) | inj₁ x₃ with ≤reflrefl x₁ x₃
mergelemma1 x .(x ∷ L) (two .x .x L x₁ x₂) | inj₁ x₃ | refl = cong (_∷_ x) (mergelemma1 x L x₂)
mergelemma1 x .(y ∷ L) (two .x y L x₁ x₂) | inj₂ y₁ = refl

mergelemma2 : ( x : ℕ ) -> (xs : List ℕ ) -> isorder (x ∷ xs ) -> merge (x ∷ []) xs ≡ x ∷ xs
mergelemma2 x .[] one = refl
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) with em x y
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) | inj₁ x₃ = refl
mergelemma2 x .(y ∷ L) (two .x y L x₁ x₂) | inj₂ y₁ with ≤reflrefl x₁ y₁
mergelemma2 x .(x ∷ L) (two .x .x L x₁ x₂) | inj₂ y₁ | refl = cong (_∷_ x) (mergelemma2 x L x₂)

mergelemma3 : ( x : ℕ ) ->  ( ys : List ℕ ) -> isorder ys ->  merge ys (x ∷ []) ≡ merge (x ∷ []) ys
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

{-
mutual
  mergelemma5 :  (x : ℕ) -> (xs ys : List ℕ) -> isorder (x ∷ xs ) -> isorder (x ∷ ys ) -> merge ys (x ∷ xs) ≡ x ∷ merge ys xs
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

  mergelemma6 :  (x : ℕ) -> (xs ys : List ℕ) -> isorder (x ∷ xs ) -> isorder (x ∷ ys ) -> merge (x ∷ xs) ys ≡ x ∷ merge xs ys
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

mergelemma7 : ( x : ℕ ) -> ( xs ys : List ℕ ) -> isorder (x ∷ xs) -> isorder ys -> merge ys (x ∷ xs ) ≡ merge ( x ∷ xs ) ys
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

mergelemma4 : (x y : ℕ) -> ( ys L : List ℕ ) -> x ≤ y -> isorder ( y ∷ L ) -> isorder ys ->  merge ys (x ∷ y ∷ L) ≡ merge (x ∷ y ∷ L) ys
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

mergeswap : ( xs ys  : List ℕ ) -> isorder xs -> isorder ys -> merge ys xs  ≡ merge xs ys 
mergeswap .[] ys nil x₁ = sym (merge[] ys)
mergeswap .(x ∷ []) ys (one {x}) x₁ = mergelemma3 x ys x₁
mergeswap .(x ∷ y ∷ L) ys (two x y L x₂ x₃) x₁ = mergelemma4 x y ys L x₂ x₃ x₁
-}

lemma1 : ( x y : ℕ ) -> (L : List ℕ ) -> y ≤ x -> isorder (y ∷ L) -> isorder (y ∷ merge (x ∷ [] ) L )
lemma1 x y .[] x₁ one = two y x [] x₁ one
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) with em x y₁
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₁ x₄ = two y x (y₁ ∷ L) x₁ (two x y₁ L x₄ x₃)
lemma1 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₂ y₂ = two y y₁ (merge (x ∷ []) L) x₂ (lemma1 x y₁ L y₂ x₃ )

lemma2 : ( x y : ℕ ) -> (L : List ℕ ) -> y ≤ x -> isorder (y ∷ L) -> isorder (y ∷ merge L (x ∷ [] ) )
lemma2 x y .[] x₁ one = two y x [] x₁ one
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) with em y₁ x
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₁ x₄ = two y y₁ (merge L (x ∷ [])) x₂ (lemma2 x y₁ L x₄ x₃ )
lemma2 x y .(y₁ ∷ L) x₁ (two .y y₁ L x₂ x₃) | inj₂ y₂ = two y x (y₁ ∷ L) x₁ (two x y₁ L y₂ x₃)

correctness : ( xs ys : List ℕ ) -> isorder xs -> isorder ys -> isorder ( merge xs ys )
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
correctness (x ∷ .(y ∷ L)) (x₁ ∷ .(y₁ ∷ L₁)) (two .x y L x₂ x₃) (two .x₁ y₁ L₁ x₄ x₅) = {!!}
