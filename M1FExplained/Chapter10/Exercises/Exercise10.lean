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

lemma part_a' (n : ℤ) (hn : 23 < n) : ∃ (a b : ℤ), 0 ≤ a ∧ 0 ≤ b ∧ 9 * a + 4 * b = n := by
  apply @Int.le_induction _ 24 ?h0 ?h1 n (show 24 ≤ n by exact hn)
  · use 0, 6
    simp
  · intros k hk
    intro
    |⟨a, b, ⟨ha, hb, hab⟩⟩ => 
    have ha' : b = 0 ∨ b = 1 → 0 ≤ a - 3 := by 
      · intro
        | Or.inl b0 => 
        rw [b0, mul_zero, add_zero] at hab
        rw [sub_nonneg]
        by_contra h3a 
        push_neg at h3a
        have : k ≤ 18 := by
          · calc
            k = 9 * a := by exact id (Eq.symm hab)
            _ ≤ 9 * 2 := by rel [show a ≤ 2 by exact Iff.mp Int.lt_add_one_iff h3a]
        linarith   
        | Or.inr b1 => 
        rw [b1, mul_one] at hab
        rw [sub_nonneg]
        by_contra h3a' 
        push_neg at h3a'
        have : k ≤ 22 := by
          · calc
            k = 9 * a + 4 := by exact id (Eq.symm hab)
            _ ≤ 9 * 2 + 4 := by rel [show a ≤ 2 by exact Iff.mp Int.lt_add_one_iff h3a']
        linarith
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
    rcases this with (h1 | h2 | h3)
  -- case: b = 0
    · rw [h1, mul_zero, add_zero] at hab
      use (a - 3), 7
      constructor
  -- 0 ≤ a - 3
      · exact ha' (Or.inl h1)
  -- 0 ≤ 7 ∧ 9 * (a - 3) + 4 * 7 = k + 1 
      · simp
        rw [Int.mul_sub, hab, sub_add]
        norm_num
  -- case: b = 1
    · rw [h2, mul_one] at hab
      use (a - 3), 8
      constructor
  -- 0 ≤ a - 3
      · exact ha' (Or.inr h2)
  -- 0 ≤ 8 ∧ 9 * (a - 3) + 4 * 8 = k + 1
      · simp
        rw [Int.mul_sub, show 9 * a - 9 * 3 + 4 * 8 = 9 * a + 4 - 9 * 3 + 4 * 7 by ring, hab]
        ring
  -- case: 2 ≤ b
    · have hb' : 0 ≤ b - 2 := by exact Int.sub_nonneg_of_le h3
      use (a + 1), (b - 2)
      constructor
  -- 0 ≤ a
      · exact Int.le_add_one ha
  -- 0 ≤ b - 2 ∧ 9 * a + 4 * (b - 2) = k + 1
      · constructor
        · exact hb'
        · rw [show 9 * (a + 1) + 4 * (b - 2) = 9 * a + 4 * b + 9 - 4 * 2 by ring, hab] 
          ring
      


  /-
  Do induction on n. Prove n = 24 trivially
  -- assume ∃ aₖ, bₖ, 9aₖ + 4bₖ = k
  -- contidion on bₖ = 0, 1, else
  -- bₖ = 0:
    -- aₖ₊₁ = aₖ - 3, bₖ₊₁ = 7 (since aₖ ≥ 3)
  -- bₖ = 1:
    -- aₖ₊₁ = aₖ - 3, bₖ₊₁ = 8 (since aₖ ≥ 3)
  -- bₖ ≥ 2:
    -- aₖ₊₁ = aₖ bₖ₊₁ = bₖ - 2 (since bₖ ≥ 2)
  
  -/

-- part b

/-
Perversely, however, Ivor decides that he must buy exactly 23 O’Nuggets,
no more and no less. Is he able to do this?
-/

-- part c

/-
Generalize this question, replacing 4 and 9 by any pair a,b of coprime
positive integers: find an integer N (depending on a and b), such that
for any integer n > N it is possible to find integers s,t ≥ 0 satisfying
s * a + t * b = n, but no such s,t exist satisfying sa+tb = N.
-/

end Chapter10.Exercise10