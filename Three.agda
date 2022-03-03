
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

mergelemma4 : (x y : ℕ) -> ( ys L : List ℕ ) -> x ≤ y -> isorder ( y ∷ L ) -> isorder ys ->  merge ys (x ∷ y ∷ L) ≡ merge (x ∷ y ∷ L) ys
mergelemma4 x y [] L x₁ x₂ x₃ = refl
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ with em x₄ x | em x x₄
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ with ≤reflrefl x₅ x₆
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl with em y x
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₄ with ≤reflrefl x₁ x₄
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₁ x₄ | refl = cong (_∷_ x) {!!}
mergelemma4 x y (x ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₁ x₆ | refl | inj₂ y₁ = cong (_∷_ x) {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₁ x₅ | inj₂ y₁ = {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₁ x₅ = {!!}
mergelemma4 x y (x₄ ∷ ys) L x₁ x₂ x₃ | inj₂ y₁ | inj₂ y₂ = {!!}

mergeswap : ( xs ys  : List ℕ ) -> isorder xs -> isorder ys -> merge ys xs  ≡ merge xs ys 
mergeswap .[] ys nil x₁ = sym (merge[] ys)
mergeswap .(x ∷ []) ys (one {x}) x₁ = mergelemma3 x ys x₁
mergeswap .(x ∷ y ∷ L) ys (two x y L x₂ x₃) x₁ = {!!}

correctness : ( xs ys : List ℕ ) -> isorder xs -> isorder ys -> isorder ( merge xs ys )
correctness = {!!}
