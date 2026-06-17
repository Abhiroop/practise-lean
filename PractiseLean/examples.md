### Some examples

#### Infinitude of Primes

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactics

-- THEOREM: There is always a prime number greater than any given number n
theorem infinitude_of_primes (n : ℕ) : ∃ p, p > n ∧ Nat.Prime p := by
  -- 1. Consider the number (N! + 1)
  let M := Nat.factorial n + 1
  
  -- 2. Every number greater than 1 has a prime factor. 
  -- Let 'p' be the smallest prime factor of M.
  let p := Nat.minFac M
  
  -- 3. Tell Lean this 'p' is our candidate prime
  use p
  
  -- 4. Split the goal into: (p > n) AND (Nat.Prime p)
  constructor
  · -- Goal 1: Prove p > n
    by_contra h_le
    push_neg at h_le
    -- If p ≤ n, then p must divide n!
    have h1 : p ∣ Nat.factorial n := Nat.dvd_factorial (Nat.minFac_pos M) h_le
    -- By definition, p also divides (n! + 1)
    have h2 : p ∣ Nat.factorial n + 1 := Nat.minFac_dvd M
    -- Therefore, p must divide the difference, which is 1
    have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
    -- Contradiction! A prime cannot divide 1.
    exact Nat.Prime.not_dvd_one (Nat.minFac_prime (by omega)) h3
    
  · -- Goal 2: Prove p is actually prime
    -- This is true by definition of minFac for any number > 1
    exact Nat.minFac_prime (by omega)
```

#### Crypto

```lean
-- Define our Byte type
def Byte := UInt8

-- Encryption function: XOR two lists of bytes item by item
def encrypt_bytes : List Byte → List Byte → List Byte
  | [], _ => []
  | _, [] => []
  | (m :: ms), (k :: ks) => (m ^^^ k) :: encrypt_bytes ms ks

-- Helper Lemma: XORing a byte with the same key twice yields the original byte
lemma xor_self_inverse (m k : Byte) : (m ^^^ k) ^^^ k = m := by
  -- UInt8 has 256 states, so Lean can check them all automatically
  decide

-- THEOREM: Decryption is perfectly correct if the key is long enough
theorem otp_decryption_correct (m k : List Byte) (h : m.length = k.length) :
  encrypt_bytes (encrypt_bytes m k) k = m := by
  -- Start induction on the message list
  induction m generalizing k with
  | nil => 
    -- Base Case: The message is empty []
    rfl
  | cons m ms ih => 
    -- Inductive Case: The message looks like (m :: ms)
    -- Destruct the key list to match the message structure
    cases k with
    | nil => 
      -- Contradiction: length says key can't be empty if message has items
      nomatch h
    | cons k ks => 
      -- Step 1: Simplify the encryption definitions
      simp [encrypt_bytes]
      -- Step 2: Use our helper lemma to fix the head byte
      rw [xor_self_inverse]
      -- Step 3: Clean up the length hypothesis for the remaining list
      aesop


```