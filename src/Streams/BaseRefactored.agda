module Streams.BaseRefactored where

open import C
open C.C ⦃ ... ⦄

open import Data.Unit using (⊤)
open import Data.Integer as ℤ using (ℤ)
open import Data.Nat as ℕ using (ℕ ; s≤s ; z≤n)
open import Data.Product using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂ ; ∃-syntax)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Function
import Level

-- Stream Fusion, to Completeness ----------------------------------------

module Strymonas ⦃ _ : C ⦄ where

  data Cardinality : Set where
    at-most-one : Cardinality                         -- from filter
    many : Cardinality                                -- from flatmap

  data Producer (α σ : Set) : Set where
    for :
      (σ → (Ref Int → Statement))                     -- upper-bound
      × (σ → Expr Int → (α → Statement) → Statement)  -- index to val
      → Producer α σ
    unfolder :
     (σ → (Ref Bool → Statement))                     -- end?
     × Cardinality                                    -- cardinality
     × (σ → (α → Statement) → Statement)              -- step function
     → Producer α σ

  Driver : Set → Set₁
  Driver α =
    ∃[ σ ] (                         -- state type
      ((σ → Statement) → Statement)  -- state initialiser
      × Producer α σ)                -- Producer

  data SStream (α : Set) : Set₁ where
    linear : Driver α → SStream α
    nested : ∀ { β } → Driver β × (β → SStream α) → SStream α

  Stream : c_type → Set₁
  Stream α = SStream (Expr α)

  ∥_∥ₛ : ∀ { α } → SStream α → ℕ
  ∥ linear _ ∥ₛ = 0
  ∥ nested _ ∥ₛ = 1

  ∥_∥ₚ : ∀ { α } → Driver α → ℕ
  ∥ _ , _ , unfolder _ ∥ₚ = 0
  ∥ _ , _ , for _ ∥ₚ = 1

  forUnfold : ∀ { α } → Driver α → Driver α
  forUnfold { α } (σ , init , for (bound , index)) =
    _ , init' , unfolder (term , many , step)
    where
      init' : ((Ref Int × σ) → Statement) → Statement
      init' k =
        init (λ s0 →
          decl Int λ i →
          i ≔ ⟪ ℤ.+ 0 ⟫ ；
          k (i , s0))
      term : (Ref Int × σ) → Ref Bool → Statement
      term (i , s0) ref =
        decl Int λ x →
        x ← bound s0 ；
        ref ≔ (★ i) <= (★ x)
      step : (Ref Int × σ) →  (α → Statement) → Statement
      step (i , s0) k =
        index s0 (★ i) (λ a → i ≔ (★ i) + ⟪ ℤ.+ 1 ⟫ ； k a)
  forUnfold (_ , init , unfolder x) =
    _ , init , unfolder x

  forUnfold-size : ∀ { α } (p : Driver α) → ∥ forUnfold p ∥ₚ ≡ 0
  forUnfold-size (_ , _ , for _) = refl
  forUnfold-size (_ , _ , unfolder _) = refl

  ofVecRaw : ∀ { α n m } {m≤n : m ℕ.≤ n} → Ref (Array α n) → Vec (Expr α) m → Statement
  ofVecRaw _ Vec.[] = nop
  ofVecRaw {n = n} {m≤n = 1≤n} x (h ∷ []) =
    x [ ⟪ ℤ.+ (n ℕ.∸ 1) ⟫ ] ≔ h
  ofVecRaw {n = n} {m = ℕ.suc (ℕ.suc m)} {m≤n = m+2≤n} x (h₁ ∷ h₂ ∷ t) =
    x [ ⟪ ℤ.+ (n ℕ.∸ (ℕ.suc m) ℕ.∸ 1) ⟫ ] ≔ h₁ ；
    ofVecRaw {m≤n = ≤-trans (n≤1+n (ℕ.suc m)) m+2≤n} x (h₂ ∷ t)

  ofVec : ∀ { α n } → Vec (Expr α) n → Stream α
  ofVec { α } { n } vec =
    let init : (Ref (Array α n) → Statement) → Statement
        init k =
          decl (Array α n) λ x →
          ofVecRaw {m≤n = ≤-refl} x vec ；
          k x
        upb : ∀ { m } → Ref (Array α m) → Ref Int → Statement
        upb { m } _ ref =
          ref ≔ ⟪ ℤ.+ (m ℕ.∸ 1) ⟫
        index : ∀ { m } → Ref (Array α m) → Expr Int → (Expr α → Statement) → Statement
        index arr i k =
          decl α λ el →
          el ≔ ★ (arr [ i ]) ；
          k (★ el) -- TODO: requires i ∈ n
    in
      linear (_ , init , for (upb , index))

  ofArr : ∀ { α n } → Ref (Array α n) → Stream α
  ofArr {α} {n} arr = linear (_ , init , for (upb , index))
    where
      init : (Ref (Array α n) → Statement) → Statement
      init k = k arr
      upb : ∀ { m } → Ref (Array α m) → Ref Int → Statement
      upb {m} _ ref = ref ≔ ⟪ ℤ.+ (m ℕ.∸ 1) ⟫
      index : ∀ { m } → Ref (Array α m) → Expr Int → (Expr α → Statement) → Statement
      index arr i k =
        decl α λ el →
        el ≔ ★ (arr [ i ]) ；
        k (★ el) -- TODO: requires i ∈ n

  -- unfold ≡ λ f z → Functor.fmap f (Applicative.pure z)
  unfold : ∀ { α ζ }
    → (Expr ζ → (Expr Bool × Expr α × Expr ζ)) → Expr ζ → Stream α
  unfold { α } { ζ } f x =
    linear (_ , init , unfolder (term , many , step))
    where
      init : (Ref Bool × Ref α × Ref ζ → Statement) → Statement
      init k =
        let b , a , z = f x in
          decl Bool λ u → u ≔ b ；
          decl α λ v → v ≔ a ；
          decl ζ λ w → w ≔ z ；
          k (u , v , w)
      term : Ref Bool × Ref α × Ref ζ → Ref Bool → Statement
      term (b , _) r = r ≔ ★ b
      step : Ref Bool × Ref α × Ref ζ → (Expr α → Statement) → Statement
      step (b , a , z) body =
        let b' , a' , z' = f (★ z) in
          body (★ a) ；
          b ≔ b' ；
          a ≔ a' ；
          z ≔ z'

  iterRaw : ∀ { α } → (α → Statement) → (x : SStream α)
    → {n : ℕ} { _ : n ≡ ∥ x ∥ₛ } → Statement
  iterRaw consumer (linear (_ , init , for (bound , index))) = 
    init (λ sp →
      decl Int λ l →
      l ← bound sp ；
      for ⟪ ℤ.+ 0 ⟫ to ★ l then λ i →
        index sp (★ i) consumer)
  iterRaw consumer (linear (_ , init , unfolder (term , at-most-one , step))) =
    init λ sp →
      decl Bool λ cond →
      cond ← term sp ；
      if ★ cond then step sp consumer else nop
  iterRaw consumer (linear (_ , init , unfolder (term , many , step))) =
    init λ sp →
      decl Bool λ cond →
      cond ← term sp ；
      while ★ cond then (
        step sp consumer ；
        cond ← term sp
      )
  iterRaw consumer (nested (prod , f)) {1} =
    iterRaw (λ e → iterRaw consumer (f e) {∥ f e ∥ₛ} {refl}) (linear prod) {0} {refl}

  iter : ∀ { α } → (α → Statement) → SStream α → Statement
  iter f s = iterRaw f s {∥ s ∥ₛ} {refl}

  fold : ∀ { α ζ } → (Expr ζ → α → Expr ζ) → Expr ζ → SStream α → (Ref ζ → Statement)
  fold f z s acc =
    acc ≔ z ；
    iter (λ a → acc ≔ f (★ acc) a) s

  mapRaw : ∀ { α β } → (α → (β → Statement) → Statement)
    → SStream α → SStream β
  mapRaw tr (linear (_ , init , for (bound , index))) =
    let index' s i k = index s i (λ e → tr e k) in
      linear (_ , init , for (bound , index'))
  mapRaw tr (linear (_ , init , unfolder (term , card , step))) =
    let step' s k = step s (λ e → tr e k) in
      linear (_ , init , unfolder (term , card , step'))
  mapRaw tr (nested (p , f)) = nested (p , (λ a → mapRaw tr (f a)))

  -- map ≡ Functor.fmap
  map : ∀ { α β } → (α → Expr β) → SStream α → Stream β
  map { β = β } f =
    mapRaw (λ a k →
      decl β λ t →
      t ≔ f a ；
      k (★ t)
    )

  -- Inefficient, but more general and ≅-equivalent
  map' : ∀ { α β } → (α → β) → SStream α → SStream β
  map' f = mapRaw (λ a k → k (f a))

  -- flatmap ≡ λ f x → x Monad.>>= f
  flatmap : ∀ { α β } → (α → SStream β) → SStream α → SStream β
  flatmap {α = α} f (linear x) = nested (x , f) -- TODO: can we eliminate this case when α is Bool or other prim type
  flatmap f (nested (x , g)) = nested (x , λ a → flatmap f (g a))

  filter : ∀ { α } → (α → Expr Bool) → SStream α → SStream α
  filter f = flatmap (
    λ x → linear (_ , (λ k → k x) , unfolder ((λ a r → r ≔ f a) , at-most-one , λ a k → k a)))

  addToProducerRaw : ∀ { α } → (Ref Bool → Statement) → (p : Driver α)
    → { n : ℕ } { _ : n ≡ ∥ p ∥ₚ } → Driver α
  addToProducerRaw new (_ , init , unfolder (term , many , step)) =
    _ , init , unfolder (term' , many , step)
    where
      term' : _ → Ref Bool → Statement
      term' s r =
        decl Bool λ a →
        a ← new ；
        decl Bool λ b →
        b ← term s ；
        r ≔ (★ a) && (★ b)
  addToProducerRaw new (_ , init , unfolder (term , at-most-one , step)) =
    _ , init , unfolder (term , at-most-one , step)
  addToProducerRaw new (_ , init , for x) {1} =
    addToProducerRaw new (forUnfold (_ , init , for x)) {0} {refl}

  addToProducer : ∀ { α } → (Ref Bool → Statement) → Driver α → Driver α
  addToProducer new p = addToProducerRaw new p {∥ p ∥ₚ} {refl}

  moreTermination : ∀ { α } → (Ref Bool → Statement) → SStream α → SStream α
  moreTermination new (linear p) = linear (addToProducer new p)
  moreTermination new (nested (p , f)) =
    nested (addToProducer new p , λ a → moreTermination new (f a))

  addNr : ∀ { α } → Expr Int → (p : Driver α) → Driver (Ref Int × α)
  addNr n (σ , init , unfolder (term , card , step)) =
    _ , init' , unfolder (term' card , card , step')
    where
      init' : (Ref Int × σ → Statement) → Statement
      init' k = init (λ s → decl Int λ nr → nr ≔ n ； k (nr , s))
      term' : Cardinality → Ref Int × σ → Ref Bool → Statement
      term' many (nr , s) r =
        r ← term s ；
        r ≔ (★ r) && ((★ nr) > ⟪ ℤ.+ 0 ⟫)
      term' at-most-one (nr , s) = term s
      step' : Ref Int × σ → (Ref Int × _ → Statement) → Statement
      step' (nr , s) k = step s (λ el → k (nr , el))
  addNr _ (_ , _ , for _) =
    _ , (λ k → k ⊤.tt) , for ((λ _ r → r ≔ ⟪ ℤ.+ 0 ⟫) , (λ _ _ _ → nop))

  take : Expr Int → ∀ { α } → SStream α → SStream α
  take n (linear (_ , init , for (bound , index))) =
    linear (
      _ , init , for (
        (λ s r →
          decl Int λ b →
          b ← bound s ；
          if ((n - ⟪ ℤ.+ 1 ⟫) < (★ b)) then
            r ≔ n - ⟪ ℤ.+ 1 ⟫
          else
            r ≔ ★ b
        )
        , index
      )
    )
  take n (linear p@(_ , init , unfolder x)) =
    mapRaw
      (λ { (nr , el) k → nr ≔ ★ nr - ⟪ ℤ.+ 1 ⟫ ； k el })
      (linear (addNr n (_ , init , unfolder x)))
  take n (nested { β = α } (p , f)) =
    nested (
      addNr n (forUnfold p) ,
      λ nra →
        let nr , a = nra in
          mapRaw
            (λ el k → nr ≔ ★ nr - ⟪ ℤ.+ 1 ⟫ ； k el)
            (moreTermination (λ r → r ≔ (★ nr) > ⟪ ℤ.+ 0 ⟫) (f a))
    )

  -- TODO: drop

  zipProducer : ∀ { α β } (a : Driver α) (b : Driver β)
    → { n : ℕ } { _ : n ≡ ∥ a ∥ₚ } { m : ℕ } { _ : m ≡ ∥ b ∥ₚ }
    → Driver (α × β)
  zipProducer {α} {β} (σ₁ , i₁ , for (b₁ , x₁)) (σ₂ , i₂ , for (b₂ , x₂)) =
    _ , i , for (b , x)
    where
      i : (σ₁ × σ₂ → Statement) → Statement
      i k = i₁ (λ a → i₂ (λ b → k (a , b)))
      b : σ₁ × σ₂ → Ref Int → Statement
      b (a , b) r =
        decl Int λ x →
        decl Int λ y →
        x ← b₁ a ；
        y ← b₂ b ；
        if (★ x) < (★ y) then
          r ≔ ★ x
        else
          r ≔ ★ y
      x : σ₁ × σ₂ → Expr Int → (α × β → Statement) → Statement
      x (a , b) i k = x₁ a i (λ n → x₂ b i (λ m → k (n , m)))
  zipProducer {α} {β} (σ₁ , i₁ , unfolder (t₁ , c₁ , s₁)) (σ₂ , i₂ , unfolder (t₂ , c₂ , s₂)) =
    _ , i , unfolder (t , many , s)
    where
      i : (σ₁ × σ₂ → Statement) → Statement
      i k = i₁ (λ a → i₂ (λ b → k (a , b)))
      t : σ₁ × σ₂ → Ref Bool → Statement
      t (a , b) r =
        decl Bool λ x →
        decl Bool λ y →
        x ← t₁ a ；
        y ← t₂ b ；
        r ≔ (★ x) && (★ y)
      s : σ₁ × σ₂ → (α × β → Statement) → Statement
      s (a , b) k = s₁ a (λ x → s₂ b (λ y → k (x , y)))
  zipProducer a@(_ , _ , for _) b@(_ , _ , unfolder _) {n = 1} {refl} {0} {refl} =
    zipProducer (forUnfold a) b {n = 0} {refl} {0} {refl}
  zipProducer a@(_ , _ , unfolder _) b@(_ , _ , for _) {n = 0} {refl} {1} {refl} =
    zipProducer a (forUnfold b) {n = 0} {refl} {0} {refl}

  pushLinear : ∀ { α β γ }
    → (p : Driver α) (q : Driver β) → ∥ p ∥ₚ ≡ 0 → ∥ q ∥ₚ ≡ 0
    → (β → SStream γ) → SStream (α × γ)
  pushLinear {α} {β} {γ} (σ₁ , init₁ , unfolder (term₁ , _ , step₁)) (σ₂ , init₂ , unfolder (term₂ , _ , step₂)) _ _ f =
    nested ((_ , init , unfolder (term , many , step)) , g)
    where
      init : (Ref Bool × σ₁ × σ₂ → Statement) → Statement
      init k =
        init₁ (λ s₁ →
          init₂ (λ s₂ →
            decl Bool λ r →
            r ← term₁ s₁ ；
            k (r , s₁ , s₂)))
      term : Ref Bool × σ₁ × σ₂ → Ref Bool → Statement
      term (b , s₁ , s₂) r =
        r ← term₂ s₂ ；
        r ≔ (★ r) && (★ b)
      step : Ref Bool × σ₁ × σ₂ → (Ref Bool × σ₁ × β → Statement) → Statement
      step (r , s₁ , s₂) k = step₂ s₂ (λ b → k (r , s₁ , b))
      g : Ref Bool × σ₁ × β → SStream (α × γ)
      g (r , s₁ , b) =
        mapRaw
          (λ c k → step₁ s₁ (λ a → r ← term₁ s₁ ； k (a , c)))
          (moreTermination (λ x → x ≔ ★ r) (f b))

  -- Prohibt zip of two nested streams
  zip : ∀ { α β } (x : SStream α) (y : SStream β) → ∥ x ∥ₛ ℕ.+ ∥ y ∥ₛ ℕ.≤ 1
    → SStream (α × β)
  zip (linear p) (linear q) z≤n =
    linear (zipProducer p q {_} {refl} {_} {refl})
  zip (linear p) (nested (q , f)) (s≤s z≤n) =
    pushLinear (forUnfold p) (forUnfold q) (forUnfold-size p) (forUnfold-size q) f
  zip (nested (p , f)) (linear q) (s≤s z≤n) =
    mapRaw
      (λ { (y , x) k → k (x , y) })
      (pushLinear (forUnfold q) (forUnfold p) (forUnfold-size q) (forUnfold-size p) f)

  zipWith : ∀ { α β γ } → (α → β → γ)
    → (x : SStream α) (y : SStream β) → ∥ x ∥ₛ ℕ.+ ∥ y ∥ₛ ℕ.≤ 1 → SStream γ
  zipWith f a b p = mapRaw (λ { (x , y) k → k (f x y) }) (zip a b p)

  nil : ∀ { α } → SStream α
  nil = linear (⊤ , (λ x → x ⊤.tt) , for ((λ _ _ → nop) , λ _ _ _ → nop))

  -- iota n
  -- The infinite stream of natural numbers starting at n
  iota : ℕ → Stream Int
  iota n = unfold (λ n → (true , n , n + ⟪ ℤ.+ 1 ⟫)) ⟪ ℤ.+ n ⟫

  -- nat n
  -- The stream of natural numbers less than n
  nat' : Expr Int → Stream Int
  nat' n = unfold (λ x → (x < n , x , x + ⟪ ℤ.+ 1 ⟫)) ⟪ ℤ.+ 0 ⟫

  nat : ℕ → Stream Int
  nat n = nat' ⟪ ℤ.+ n ⟫

  _▹_ : ∀ { α n } → ∀ { β : Set n } → Stream α → (Stream α → β) → β
  x ▹ f = f x 
  infixl 0 _▹_
