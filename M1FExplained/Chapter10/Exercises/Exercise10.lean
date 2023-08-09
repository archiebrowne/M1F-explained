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
#check induction
lemma part_a (n : ℕ) (hn : 23 < n) : ∃ (a b : ℕ), 4 * a + 9 * b = n := by
  induction (n - 24) with
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