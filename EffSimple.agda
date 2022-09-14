open import Level renaming (zero to lzero; suc to lsuc)

module EffSimple {a : Level} where
  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any
  open import Data.Maybe hiding (_>>=_)
  open import Data.Nat hiding (_<_; _⊔_)
  open import Data.Nat.Properties
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Function
  open import Induction
  open import Induction.WellFounded
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  Req : Set (lsuc a)
  Req = Set a → Set a

  private
    variable
      A B C D : Set a
      T U : Req
      R R′ : List (Req)

  data Union : List Req → Set a → Set a where
    here  : ∀ {T R A} → T A       → Union (T ∷ R) A
    there : ∀ {T R A} → Union R A → Union (T ∷ R) A

  inj : ⦃ T ∈ R ⦄ → T A → Union R A
  inj ⦃ here refl ⦄ x = here x
  inj ⦃ there p   ⦄ x = there (inj ⦃ p ⦄ x)

  prj : ⦃ T ∈ R ⦄ → Union R A → Maybe (T A)
  prj ⦃ here refl ⦄ (here  x) = just x
  prj ⦃ here refl ⦄ (there x) = nothing
  prj ⦃ there p ⦄   (here  x) = nothing
  prj ⦃ there p ⦄   (there x) = prj ⦃ p ⦄ x

  decomp : Union (T ∷ R) A → Union R A ⊎ T A
  decomp (here  p) = inj₂ p
  decomp (there p) = inj₁ p

  data Eff (R : List Req) (A : Set a) : Set (lsuc a) where
    pure   : A → Eff R A
    impure : Union R B → (B → Eff R A) → Eff R A

  module EffRec {R : List Req} {A : Set a} where

    data _<_ : Eff R A → Eff R A → Set (lsuc a) where
      <-eff : ∀ {B} (m : Union R B) (f : B → Eff R A) (x : B) → f x < impure m f

    <-Rec : ∀ {ℓ} → RecStruct (Eff R A) ℓ _
    <-Rec = WfRec _<_

    <-wellFounded : WellFounded _<_
    <-wellFounded x = acc (go x)
      where
        go : ∀ x → <-Rec (Acc _<_) x
        go (pure x) y ()
        go (impure m f) _ (<-eff _ _ x) = <-wellFounded (f x)

  open EffRec

  qapp : (B → Eff R A) → B → Eff R A
  qapp q x = q x

  qcomp : (A → Eff R B) → (Eff R B → Eff R′ C) → (A → Eff R′ C)
  qcomp g h a = h (qapp g a)

  fmap : (A → B) → Eff R A → Eff R B
  fmap f (pure x) = pure (f x)
  fmap f (impure m g) = impure m (fmap f ∘ g)

  return : A → Eff R A
  return = pure

  infixl 1 _>>=_ _>>_ _>=>_
  _>>=_ : Eff R A → (A → Eff R B) → Eff R B
  pure x >>= f = f x
  impure m g >>= f = impure m λ x → g x >>= f

  _>>_ : Eff R A → Eff R B → Eff R B
  x >> y = x >>= λ _ → y

  _>=>_ : (A → Eff R B) → (B → Eff R C) → (A → Eff R C)
  f >=> g = λ a → f a >>= g

  send : ⦃ T ∈ R ⦄ → T A → Eff R A
  send t = impure (inj t) pure

  run : Eff [] A → A
  run (pure x) = x

  handle-relay′ : (A → Eff R B)
                → (∀ {X} → T X → (X → Eff R B) → Eff R B)
                → (m : Eff (T ∷ R) A)
                → Acc _<_ m
                → Eff R B
  handle-relay′ ret h (pure x) _ = ret x
  handle-relay′ ret h (impure m f) (acc rs) with decomp m
  ... | inj₁ x = impure x λ a → handle-relay′ ret h (f a) (rs (f a) (<-eff m f a))
  ... | inj₂ x = h x λ a → handle-relay′ ret h (f a) (rs (f a) (<-eff m f a))

  Handler : ∀ (T : Req) (R : List Req) (A B : Set a) → Set (lsuc a)
  Handler T R A B = Eff (T ∷ R) A → Eff R B

  handle-relay : (A → Eff R B)
               → (∀ {X} → T X → (X → Eff R B) → Eff R B)
               → Handler T R A B
  handle-relay ret h m = handle-relay′ ret h m (<-wellFounded _)

  data Reader (A : Set a) : Set a → Set a where
    get : Reader A A

  ask : ⦃ Reader A ∈ R ⦄ → Eff R A
  ask = send get

  runReader : A → Handler (Reader A) R B B
  runReader i = handle-relay return λ where get k → k i

  data Writer (A : Set a) : Set a → Set a where
    put : A → Writer A (Lift _ ⊤)

  tell : ⦃ Writer A ∈ R ⦄ → A → Eff R _
  tell o = send (put o)

  runWriter : Handler (Writer A) R B (B × List A)
  runWriter = handle-relay (λ x → return (x , []))
    λ where (put o) k → do
      (x , l) ← k _
      return (x , o ∷ l)
