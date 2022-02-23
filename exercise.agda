-- {-# OPTIONS --safe --guardedness #-}

open import Function
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Agda.Builtin.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

State : Set → Set → Set
State S A = S → A × S

data ITreeF (A X : Set) : Set where
  leaf : A → ITreeF A X 
  node : A → X → X → ITreeF A X

data μITree (A : Set) : Set where
  con : ITreeF A (μITree A) → μITree A

record νITree (A : Set) : Set where
  coinductive
  field decon : ITreeF A (νITree A)

data ∂ITree (A B : Set) : Set where
    ○-⟨_,_⟩ : νITree A → (B → B → B) → ∂ITree A B
    ⟨_⟩-○   :               (B → B)  → ∂ITree A B

data Focus (A B : Set) : Set where
  ↓_ : A → Focus A B
  ↑_ : B        → Focus A B

fromjust : {A : Set} → A → Maybe A → A
fromjust e nothing = e
fromjust e (just x) = x

{-# TERMINATING #-}
repeat : {A : Set} → (A → Maybe A) → Nat → A → A → Maybe A
repeat f 0 e s = just s
repeat f 1 e = f
repeat f n e = repeat f (n - 1) e ∘ fromjust e ∘ f

--------------------------------------------------------

module SynthesizedExample where
    
  record Attr : Set where
    field
      Value : Nat
      Sum : Maybe Nat 
      Product : Maybe Nat 
  open Attr

  record algebra : Set where
    field
      e : Attr → Attr
      k : Attr → Attr → Attr → Attr
  open algebra

  record MachineState : Set where
    constructor ⟨_,_,_⟩
    field
      state : List algebra
      focus : Focus (νITree Attr) (νITree Attr)
      stack : List (∂ITree Attr (νITree Attr))

  -- 避免重複
  step : MachineState → Maybe MachineState
  step ⟨ alg ∷ algs , ↓ t , stk ⟩ with νITree.decon t
  ... | leaf attr =
    let b = mb (e alg) attr in just ⟨ alg ∷ algs , (↑ b) , stk ⟩
      where
        mb : (Attr → Attr) → Attr → νITree Attr
        mb = λ e attr → record { decon = leaf (e attr) }
  ... | node attr u v =
    let mg₁ = mg (k alg) attr in just ⟨ alg ∷ algs , (↓ u) , (○-⟨ v , mg₁ ⟩ ∷ stk) ⟩
      where
        mg : (Attr → Attr → Attr → Attr) → Attr → (νITree Attr → νITree Attr → νITree Attr)
        mg k attr u v with νITree.decon u | νITree.decon v
        ... | leaf l | leaf r = record { decon = node (k attr l r) u v }
        ... | leaf l | node r _ _ = record { decon = node (k attr l r) u v }
        ... | node l _ _ | leaf r = record { decon = node (k attr l r) u v }
        ... | node l _ _ | node r _ _ = record { decon = node (k attr l r) u v }
  step ⟨ [] , _ , _ ⟩ = nothing
  step ⟨ alg ∷ algs , ↑ b , [] ⟩ = step ⟨ algs , (↓ b) , [] ⟩
  step ⟨ algs , ↑ b , ○-⟨ v , mg₁ ⟩ ∷ stk ⟩ = 
    let mg₂ = mg₁ b in just ⟨ algs , ↓ v , ⟨ mg₂ ⟩-○ ∷ stk ⟩
  step ⟨ algs , ↑ b , ⟨ mg₂ ⟩-○ ∷ stk ⟩ =
    let b' = mg₂ b in just ⟨ algs , ↑ b' , stk ⟩

  s : algebra
  e s = λ a → record { Value = Value a ; Sum = just (Value a) ; Product = Product a }
  k s = λ a ua va → record { Value = Value a 
                          ; Sum = Data.Maybe.zipWith _+_ (Sum ua) (Sum va) >>= λ x → just (Value a + x) 
                          ; Product = Product a }

  p : algebra
  e p = λ a → record { Value = Value a 
                    ; Sum = Sum a
                    ; Product = just (Value a) }
  k p = λ a ua va → record { Value = Value a 
                          ; Sum = Sum a 
                          ; Product = Data.Maybe.zipWith _*_ (Product ua) (Product va) >>= λ x → just (Value a * x) }

  t : νITree Attr
  t = record { decon = node (record { Value = 1 ; Sum = nothing ; Product = nothing }) (record { decon = node (record { Value = 2 ; Sum = nothing ; Product = nothing }) (record { decon = leaf (record { Value = 4 ; Sum = nothing ; Product = nothing }) }) (record { decon = leaf (record { Value = 5 ; Sum = nothing ; Product = nothing}) }) }) (record { decon = leaf (record { Value = 3 ; Sum = nothing ; Product = nothing })}) }
  -- 1-3
  --  \2-5
  --    \4

  test : Maybe MachineState
  test = repeat step 9 (⟨ [] , ↓ t , [] ⟩) (⟨ (s ∷ p ∷ []) , (↓ t) , [] ⟩)

module InheritedExample where

  record Attr : Set where
    field
      value : Nat
      locmin : Maybe Nat
      gmin : Maybe Nat
  open Attr

  record Algebra : Set where
    field
      e : Attr → Attr → Attr
      k : Attr → Attr → (Attr → Attr → Attr)
  open Algebra

  record MachineState : Set where
    constructor ⟨_,_,_⟩
    field
      state : List Algebra
      focus : Attr × Focus (νITree Attr) (νITree Attr)
      stack : List (∂ITree Attr (νITree Attr) × Attr)

  getAttr : νITree Attr → Attr
  getAttr t with νITree.decon t
  ... | leaf a = a
  ... | node a u v = a
  
  step : MachineState → Maybe MachineState
  step ⟨ alg ∷ algs , (pa , ↓ t) , stk ⟩ with νITree.decon t
  ... | leaf attr =
    let b = mb (e alg) pa attr in just ⟨ alg ∷ algs , (getAttr b , ↑ b) , stk ⟩
      where
        mb : (Attr → Attr → Attr) → Attr → Attr → νITree Attr
        mb = λ e pa attr → record { decon = leaf (e pa attr) }

  ... | node attr u v =
    let mg₁ = mg (k alg) pa attr in just ⟨ alg ∷ algs , (attr , ↓ u) , (○-⟨ v , mg₁ ⟩ , attr) ∷ stk ⟩
      where
        mg : (Attr → Attr → Attr → Attr → Attr) → Attr → Attr → (νITree Attr → νITree Attr → νITree Attr)
        mg k pa attr u v with νITree.decon u | νITree.decon v
        ... | leaf l | leaf r = record { decon = node (k pa attr l r) u v }
        ... | leaf l | node r _ _ = record { decon = node (k pa attr l r) u v }
        ... | node l _ _ | leaf r = record { decon = node (k pa attr l r) u v }
        ... | node l _ _ | node r _ _ = record { decon = node (k pa attr l r) u v }

  step ⟨ [] , _ , _ ⟩ = nothing
  step ⟨ alg ∷ algs , (ca , ↑ b) , [] ⟩ = step ⟨ algs , (ca , ↓ b) , [] ⟩
  step ⟨ algs , (ca , ↑ b) , (○-⟨ v , mg₁ ⟩ , pa) ∷ stk ⟩ = 
    let mg₂ = mg₁ b in just ⟨ algs , (pa , ↓ v) , (⟨ mg₂ ⟩-○ , pa) ∷ stk ⟩
  step ⟨ algs , (ca , ↑ b) , (⟨ mg₂ ⟩-○ , pa) ∷ stk ⟩ =
    let b' = mg₂ b in just ⟨ algs , (getAttr b' , ↑ b') , stk ⟩

  min : Nat → Nat → Nat
  min a b with a Agda.Builtin.Nat.< b
  ... | false = b
  ... | true = a
  
  findGmin : Algebra
  e findGmin = λ pa a → record { value = value a ; locmin = just (value a) ; gmin = just (value a) }
  k findGmin = λ pa a ua va → record { value = value a 
                               ; locmin = Data.Maybe.zipWith min (locmin ua) (locmin va) >>= λ n →  just (min (value a) n)
                               ; gmin = Data.Maybe.zipWith min (locmin ua) (locmin va) >>= λ n → just (min (value a) n)}

  broadcast : Algebra
  e broadcast = λ pa a → record { value = value a ; locmin = locmin a ; gmin = gmin pa } 
  k broadcast = λ pa a ua va → record { value = value a ; locmin = locmin a ; gmin = gmin pa }

  t : νITree Attr
  t = newNode 4 (newNode 1 (newLeaf 2) (newLeaf 3)) (newLeaf 5)
    where
      newLeaf : Nat → νITree Attr
      newLeaf n = record { decon = leaf (record { value = n ; locmin = nothing ; gmin = nothing }) }
      newNode : Nat → νITree Attr → νITree Attr → νITree Attr
      newNode n u v = record { decon = node (record { value = n ; locmin = nothing ; gmin = nothing }) u v }

  t1 : Maybe MachineState
  t1 = repeat step 18 (⟨ [] , (getAttr t , ↓ t) , [] ⟩) (⟨ (findGmin ∷ broadcast ∷ []) , (getAttr t , ↓ t) , [] ⟩)
