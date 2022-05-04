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


sucsuc : (n m : ℕ ) -> n ≤ m -> (suc n ) ≤ (suc m )
sucsuc n .n ≤-reflex = ≤-reflex
sucsuc n .(suc m) (s≤s {m = m} x) = s≤s (sucsuc n m x)

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

sorted-inv : {x : ℕ} {l : List ℕ } -> sorted ( x ∷ l ) -> sorted l
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

mutual
  sorted-merge : ( xs ys : List ℕ ) -> sorted xs -> sorted ys -> sorted ( merge xs ys )
  sorted-merge [] ys x x₁ = x₁
  sorted-merge (x₂ ∷ xs) [] x x₁ = x
  sorted-merge (x₂ ∷ xs) (x₃ ∷ ys) x x₁ with em x₂ x₃
  sorted-merge (x₂ ∷ xs) (x₃ ∷ ys) x x₁ | inj₁ x₄  = coqlemma x (two x₂ x₃ ys x₄ x₁) (sorted-merge xs (x₃ ∷ ys) (sorted-inv  x) x₁)
  sorted-merge (x₂ ∷ xs) (x₃ ∷ ys) x x₁ | inj₂ y = coqlemma (two x₃ _ _ y x) x₁ (sorted-merge-aux x₂ xs ys x (sorted-inv  x₁))
  
  sorted-merge-aux : (x : ℕ) -> ( xs ys : List ℕ ) -> sorted (x ∷ xs) -> sorted ys -> sorted ( merge (x ∷ xs) ys )
  sorted-merge-aux x xs [] x₁ x₂ = x₁
  sorted-merge-aux x xs (x₃ ∷ ys) x₁ x₂ with em x x₃
  sorted-merge-aux x xs (x₃ ∷ ys) x₁ x₂ | inj₁ x₄ = coqlemma x₁ (two x x₃ ys x₄ x₂) (sorted-merge xs (x₃ ∷ ys) (sorted-inv x₁) x₂) 
  sorted-merge-aux x xs (x₃ ∷ ys) x₁ x₂ | inj₂ y = coqlemma (two x₃ x xs y x₁) x₂ (sorted-merge-aux x xs ys x₁ (sorted-inv x₂))

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

mergesortcorrectness' : ( xs : List ℕ ) -> ( a :  Acc  _<′_ (length xs)) -> sorted (mergesort' xs a)
mergesortcorrectness' [] a = nil
mergesortcorrectness' (x ∷ []) a = one
mergesortcorrectness' (x ∷ x₁ ∷ xs) (acc rs) with partition xs | partition-size xs
mergesortcorrectness' (x ∷ x₁ ∷ xs) (acc rs) | fst , snd | fst₁ , snd₁ = sorted-merge (mergesort' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesort' (x₁ ∷ snd)  (rs _ (s≤′s (s≤′s snd₁)))) (mergesortcorrectness' (x ∷ fst) (rs _ (s≤′s (s≤′s fst₁)))) (mergesortcorrectness' (x₁ ∷ snd) (rs _ (s≤′s (s≤′s snd₁)))) 

mergesortcorrectness : ( xs : List ℕ ) -> sorted (mergesort xs)
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

