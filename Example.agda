module Example where
  open import Eff

  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.Nat
  open import Data.Product
  open import Data.String hiding (replicate)
  open import Function
  open import Relation.Binary.PropositionalEquality

  private
    variable
      R : List (Req)

  addGet : ⦃ Reader ℕ ∈ R ⦄ → ℕ → Eff R ℕ
  addGet x = do
    i ← ask
    return (i + x)

  addN : ⦃ Reader ℕ ∈ R ⦄ → ℕ → Eff R ℕ
  addN n = foldl _>=>_ return (replicate n addGet) 0

  t1 : 11 ≡ (run ∘ runReader 10 $ addGet 1)
  t1 = refl

  rdwr : ⦃ Reader ℕ ∈ R ⦄ → ⦃ Writer String ∈ R ⦄ → Eff R ℕ
  rdwr = do
    tell "begin"
    r ← addN 10
    tell "end"
    return r

  -- TODO: Fix instance search
  t2 : (100 , "begin" ∷ "end" ∷ []) ≡ (run ∘ runReader 10 ∘ runWriter $ rdwr ⦃ ∈-there ⦃ ∈-here ⦄ ⦄ ⦃ ∈-here ⦄)
  t2 = refl
