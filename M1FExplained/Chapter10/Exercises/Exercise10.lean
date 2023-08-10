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

lemma part_a (n : ℕ) (hn : 23 < n) : ∃ (a b : ℕ), 9 * a + 4 * b = n := by
  set m := n - 24 with hm
  rw [show n = m + 24 by exact Iff.mp (Nat.sub_eq_iff_eq_add hn) rfl] at *
  induction m with
  | zero => use 0, 6
  | succ m ih => 
  rcases ih with ⟨a, b, hab⟩
  have : b = 0 ∨ b = 1 ∨ 2 ≤ b := by sorry
  apply Or.elim this
  · intro h1
    use (a - 3), 7
    simp at hab
    rw [Nat.mul_sub_left_distrib, hab]
    norm_num
    sorry
  · intro 
    | Or.inl h2 => 
      rw [h2] at hab
      simp at hab
      use (a - 3), 8
      norm_num
      rw [show 9 * (a - 3) = 9 * a - 9 * 3 by sorry]
      rw [hab]
      norm_num
      sorry
    | Or.inr h3 =>  
      use (a + 1), (b - 2)
      rw [Nat.left_distrib, show 4 * (b - 2) = 4 * b - 4 * 2 by exact Nat.mul_sub_left_distrib 4 b 2, 
          show 9 * a + 9 * 1 + (4 * b - 4 * 2) = 9 * a + 4 * b + 9 * 1 - 4 * 2 by exact?, hab]
      simp
      
      

    
    
    



  sorry

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
sorry

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