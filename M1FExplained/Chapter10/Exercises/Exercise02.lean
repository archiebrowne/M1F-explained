import Mathlib.Tactic

namespace Chapter10.Exercise02

-- part a

/-
Show that if a, b are positive integers and d = gcd(a, b), there exists positive integers s, t such
that d = s * a - t * b
-/

lemma Int.sub_ediv_of_dvd_right {a b c : ℤ} (H : c ∣ b) : (a - b) / c = a / c - b / c := by
  simp only [sub_eq_add_neg, Int.add_ediv_of_dvd_right <| Int.dvd_neg.2 H, Int.neg_ediv_of_dvd H]

lemma Int.sub_lt_div_mul_self {a b : ℤ} (hb : 0 < b) : a - b < a / b * b := by
  by_contra h
  push_neg at h
  have := Int.le_ediv_of_mul_le hb h
  rw [Int.sub_ediv_of_dvd_right <| dvd_rfl, Int.ediv_self hb.ne'] at this
  linarith

lemma helper_1 (a b n : ℤ) (hb : 0 < b) (hab : ∃ (s t : ℤ), s * a + t * b = n) : 
    ∃ (s' t' : ℤ), 0 < s' ∧ s' * a + t' * b = n := by 
  rcases hab with ⟨s, t, hst⟩
  set p := (b - s) / b with hp
  use s + p * b, t - p * a
  constructor
  · rw [hp, ← neg_lt_iff_pos_add']
    calc
      -s = (b - s) - b := by norm_num
      _ < (b - s) / b * b := by exact Int.sub_lt_div_mul_self hb
  · linear_combination hst

lemma helper_2 (a b n : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : ∃ (s t : ℤ), s * a + t * b = n) : 
    ∃ (s' t' : ℤ), 0 < s' ∧ t' < 0 ∧ s' * a + t' * b = n := by 
    have := helper_1 a b n hb hab
    match this with
    |⟨s, t, ⟨h1, h2⟩⟩ => 
    apply Or.elim (Classical.em (t < 0))
    <;> intro ht
    · use s, t
      repeat (any_goals constructor)
      all_goals assumption
    · push_neg at ht
      set p := (t + a) / a with hp
      have hpos : 0 ≤ p := by 
        · rw [hp]
          refine Iff.mpr (Int.le_ediv_iff_mul_le ha) ?_
          norm_num
          exact Int.add_nonneg ht (show 0 ≤ a by exact Int.nonneg_of_pos ha)
      use (s + p * b), (t - p * a)
      repeat (any_goals constructor)
      · refine add_pos_of_pos_of_nonneg h1 ?hb
        exact Iff.mpr (zero_le_mul_right hb) hpos
      · rw [sub_neg, hp]
        have := @Int.sub_lt_div_mul_self (t + a) a ha
        simp at this
        assumption
      · linear_combination h2 


lemma part_a (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 
  ∃ (s t : ℤ), 0 < s ∧ 0 < t ∧ Int.gcd a b = s * a - t * b := by 
  have := helper_2 a b (Int.gcd a b) ha hb (show _ by {
    use Int.gcdA a b, Int.gcdB a b
    simp [mul_comm]
    exact Eq.symm (Int.gcd_eq_gcd_ab a b)
  })
  match this with
  |⟨s, t, ⟨hs, ht, hst⟩⟩ => 
  use s, -t
  repeat (any_goals constructor)
  · assumption
  · exact Int.neg_pos_of_neg ht
  · rw [Int.neg_mul]
    simp
    exact id (Eq.symm hst)


-- part b

/-
Find such positive integers s, t for each of the cases (i) - (iii) in Exercise 1.
-/

/-
These are exatly the integers we found in Exercise 1, and lean finds them for us easily.
-/

-- a = 17, b = 29

#eval Nat.gcd 17 29 -- 1
#eval Nat.gcdA 17 29 -- 12
#eval Nat.gcdB 17 29 -- -7
-- So 1 = 12 * 17 - 7 * 29, giving s = 12 and t = 7

-- a = 552, b = 713

#eval Nat.gcd 713 552 -- 23
#eval Nat.gcdA 713 552 -- 7
#eval Nat.gcdB 713 552 -- -9
-- So 23 = 7 * 713 - 9 * 552, giving s = 7, t = 9

-- a = 299, b = 345

#eval Nat.gcd 299 345  -- 23
#eval Nat.gcdA 299 345 -- 7
#eval Nat.gcdB 299 345 -- -6
-- So 23 = 7 * 299 - 6 * 345, giving s = 7, t = 6


end Chapter10.Exercise02