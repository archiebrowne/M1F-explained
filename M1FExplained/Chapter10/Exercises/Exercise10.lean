import Mathlib.Tactic

namespace Chapter10.Exercise10

/-
After a particularly exciting viewing of the new Danish thriller Den heletal, critic Ivor Smallbrain 
repairs for refreshment to the prison’s highsecurity fast-food outlet O’Ducks. He decides that he’d 
like to eat some delicious Chicken O’Nuggets. These are sold in packs of two sizes —
one containing 4 O’Nuggets, and the other containing 9 O’Nuggets.
-/

-- part a

/-
Prove that for any integer n > 23, it is possible for Ivor to buy n O’Nuggets
(assuming he has enough money).
-/

/-
The basic idea of the proof goes as follows:

  Do induction on n starting at 24. Prove n = 24 trivially.
  -- assume ∃ aₖ, bₖ, 9aₖ + 4bₖ = k
  -- contidion on bₖ = 0, 1 or ≥ 2.
  -- bₖ = 0:
    -- aₖ₊₁ = aₖ - 3, bₖ₊₁ = 7 (since aₖ ≥ 3)
  -- bₖ = 1:
    -- aₖ₊₁ = aₖ - 3, bₖ₊₁ = 8 (since aₖ ≥ 3)
  -- bₖ ≥ 2:
    -- aₖ₊₁ = aₖ bₖ₊₁ = bₖ - 2 (since bₖ ≥ 2)

The claim aₖ ≥ 3 in the first two cases can be proven easily 
based on the assumption that n > 23 and the value of bₖ.
-/

lemma part_a (n : ℤ) (hn : 23 < n) : ∃ (a b : ℤ), 0 ≤ a ∧ 0 ≤ b ∧ 9 * a + 4 * b = n := by
  -- Prove the startment by induction on n.
  apply @Int.le_induction _ 24 ?h0 ?h1 n (show 24 ≤ n by exact hn)
  -- Case: n = 24
  · use 0, 6
    simp
  -- Case: 24 < n 
  · intros k hk
    intro
    |⟨a, b, ⟨ha, hb, hab⟩⟩ => 
  -- To condition on the value of b, we must have one of three cases.
    have : b = 0 ∨ b = 1 ∨ 2 ≤ b := by 
      · by_cases h : b < 1
        · left
          rw [← Int.abs_lt_one_iff, abs_lt]
          constructor 
          <;> linarith
        · right
          push_neg at h
          by_cases h' : b = 1
          · left; exact h'
          · right
            have : 1 < b := by exact Ne.lt_of_le' h' h
            exact this
  -- In two of these cases, we know that 0 ≤ a - 3. 
    have ha' : b = 0 ∨ b = 1 → 0 ≤ a - 3 := by 
      · intro
        | Or.inl b0 => 
        rw [b0, mul_zero, add_zero] at hab
        rw [sub_nonneg]
        by_contra h3a 
        push_neg at h3a
        linarith  
        | Or.inr b1 => 
        rw [b1, mul_one] at hab
        rw [sub_nonneg]
        by_contra h3a' 
        push_neg at h3a'
        linarith
  -- Condition over our three cases: b = 0 ∨ b = 1 ∨ 2 ≤ b.
    rcases this with (h1 | h2 | h3)
  -- Case: b = 0.
    · rw [h1, mul_zero, add_zero] at hab
      use (a - 3), 7
      constructor
  -- 0 ≤ a - 3.
      · exact ha' (Or.inl h1)
  -- 0 ≤ 7 ∧ 9 * (a - 3) + 4 * 7 = k + 1. 
      · simp
        rw [Int.mul_sub, hab, sub_add]
        norm_num
  -- Case: b = 1.
    · rw [h2, mul_one] at hab
      use (a - 3), 8
      constructor
  -- 0 ≤ a - 3.
      · exact ha' (Or.inr h2)
  -- 0 ≤ 8 ∧ 9 * (a - 3) + 4 * 8 = k + 1.
      · simp
        rw [Int.mul_sub, show 9 * a - 9 * 3 + 4 * 8 = 9 * a + 4 - 9 * 3 + 4 * 7 by ring, hab]
        ring
  -- Case: 2 ≤ b.
    · have hb' : 0 ≤ b - 2 := by exact Int.sub_nonneg_of_le h3
      use (a + 1), (b - 2)
      constructor
  -- 0 ≤ a.
      · exact Int.le_add_one ha
  -- 0 ≤ b - 2 ∧ 9 * a + 4 * (b - 2) = k + 1.
      · constructor
        · exact hb'
        · rw [show 9 * (a + 1) + 4 * (b - 2) = 9 * a + 4 * b + 9 - 4 * 2 by ring, hab] 
          ring

-- part b

/-
Perversely, however, Ivor decides that he must buy exactly 23 O’Nuggets,
no more and no less. Is he able to do this?
-/

lemma part_b : ¬ ∃ (a b : ℤ), 0 ≤ a ∧ 0 ≤ b ∧ 9 * a + 4 * b = 23 := by
  rintro ⟨a, b, ha, hb, hab⟩
  have ha3 : a < 3 := by
    by_contra h
    push_neg at h
    have : (27 : ℤ) ≤ 23 := by 
      calc
        27 = 9 * 3 + 4 * 0 := by norm_num
        _  ≤ 9 * a + 4 * b := by rel [h, hb]
        _  = 23            := by exact hab
    contradiction
  have : a = 0 ∨ a = 1 ∨ a = 2 := by interval_cases a <;> tauto
  have hb' : b = b.natAbs := by exact Eq.symm (Int.natAbs_of_nonneg hb)
  rcases this with (h1 | h2 | h3)
  · rw [h1, mul_zero, zero_add] at hab
    have h23 : 4 ∣ 23 := by
      use b.natAbs
      rw [hb'] at hab
      exact Iff.mp Int.ofNat_inj (Eq.symm hab)
    simp at h23
  · rw [h2, mul_one, show 9 + 4 * b = 23 ↔ 4 * b = 23 - 9 by 
        constructor <;> intro <;> linarith] at hab
    have h14 : 4 ∣ 14 := by 
      use b.natAbs
      rw [hb'] at hab
      exact Iff.mp Int.ofNat_inj (Eq.symm hab)
    simp at h14
  · rw [h3, show 9 * 2 + 4 * b = 23 ↔ 4 * b = 5 by 
        constructor <;> intro <;> linarith] at hab
    have h5 : 4 ∣ 5 := by
      use b.natAbs
      rw [hb'] at hab
      exact Iff.mp Int.ofNat_inj (Eq.symm hab)
    simp at h5

-- part c

/-
Generalize this question, replacing 4 and 9 by any pair a,b of coprime
positive integers: find an integer N (depending on a and b), such that
for any integer n > N it is possible to find integers s,t ≥ 0 satisfying
s * a + t * b = n, but no such s,t exist satisfying s * a + t * b = N.
-/

example (t b : ℤ) (hb : 0 < b): t * b / t = b := by sorry

#check Int.mul_ediv_assoc
example (s t a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : s * a + t * b = 0) : (s = 0 ∧ t = 0) ∨ (a ∣ b ∨ b ∣ a) := by 
  apply Or.elim (Classical.em (s = 0))
  <;> intro hs
  · left
    rw [hs, zero_mul, zero_add] at hab
    have : t = 0 := by sorry
    tauto
  · right
    apply Or.elim (Classical.em (t < s))
    <;> intro hst
    · left
      use -(s / t)
      rw [Int.mul_neg, ← Int.sub_eq_zero, Int.sub_neg, Int.add_comm]
      have : (s * a + t * b) / t = 0 := by 
        rw [hab]; norm_num
      rw [Int.add_ediv_of_dvd_right] at this
      · rw [← Int.mul_ediv_assoc, mul_comm]
      · use b
        
      
    · right
      sorry
sorry

lemma part_c (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : Int.gcd a b = 1) :
  ∃ (N : ℤ), (∀ n ≥ N, ∃ (s t : ℤ), 0 ≤ s ∧ 0 ≤ t ∧ s * a + t * b = n) 
  ∧ (¬ ∃ (s t : ℤ), 0 ≤ s ∧ 0 ≤ t ∧ s * a + t * b = N - 1) := by 
  use (a - 1) * (b - 1)
  constructor
  · intros n hn
    have hbez1 : ∃ (x₀ y₀ : ℤ), a * x₀ + b * y₀ = 1 := by sorry
    have hbezn : ∃ (x₁ y₁ : ℤ), a * x₁ + b * y₁ = n := by sorry
    rcases hbezn with ⟨x₁, y₁, hxy⟩
    set t := Inf {t : ℤ | 0 < t ∧ 0 ≤ y₁ + t * a} with ht
    use (x₁ - t * b), (y₁ + t * a) 
    repeat (any_goals constructor)
    · sorry
    · sorry -- definition of t
    · ring
      rw [mul_comm]
      sorry
  · by_contra h 
    match h with
    | ⟨s, t, ⟨hs, ht, hst⟩⟩ => 
    rw [show (a - 1) * (b - 1) - 1 = a * b - a - b by ring] at hst
    have : a * (s - b + 1) + b * (t + 1) = 0 := by sorry
    
    
    sorry


  
  sorry

end Chapter10.Exercise10