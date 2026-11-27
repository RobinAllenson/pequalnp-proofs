import Mathlib

namespace PEqualNP.Outside.L_lib_567_aux

theorem main (n k : ℕ) (m : Fin k → ℕ) (v : (j : Fin k) → Fin (m j) → Fin n → ℝ) (w : Fin k → ℝ)
    (hm : ∀ j, 0 < m j) (hw : ∀ j, 0 ≤ w j)
    (hon : ∀ j a b, (∑ i, v j a i * v j b i) = if a = b then 1 else 0)
    (hpar : ∀ x : Fin n → ℝ, (∑ j, w j * (∑ a, (∑ i, x i * v j a i) ^ 2)) = ∑ i, x i * x i) :
    (∀ j, w j ≤ 1) ∧
      ∀ i j, i ≠ j → w i = 1 → 0 < w j → ∀ a b, (∑ c, v i a c * v j b c) = 0 := by
  have hT : ∀ (x : Fin n → ℝ) j, 0 ≤ w j * (∑ a, (∑ i, x i * v j a i) ^ 2) := fun x j =>
    mul_nonneg (hw j) (Finset.sum_nonneg (fun a _ => sq_nonneg _))
  have hself : ∀ j (a : Fin (m j)), ∑ a', (∑ i, v j a i * v j a' i) ^ 2 = 1 := by
    intro j a
    simp [hon]
  have hnorm : ∀ j (a : Fin (m j)), ∑ i, v j a i * v j a i = 1 := by
    intro j a
    simp [hon]
  constructor
  · intro j
    have h := hpar (v j ⟨0, hm j⟩)
    rw [hnorm] at h
    have := Finset.single_le_sum (f := fun j' => w j' * (∑ a, (∑ i, v j ⟨0, hm j⟩ i * v j' a i) ^ 2))
      (fun j' _ => hT _ j') (Finset.mem_univ j)
    simp only [hself, mul_one] at this
    linarith
  · intro i j hij hi hj a b
    have h := hpar (v i a)
    rw [hnorm] at h
    set f := fun j' => w j' * (∑ a', (∑ c, v i a c * v j' a' c) ^ 2) with hf
    have hsub : f i + f j ≤ ∑ j', f j' := by
      rw [← Finset.sum_pair hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j' _ _ => hT _ j')
    have hfi : f i = 1 := by simp only [hf, hself, hi, mul_one]
    have hfj : w j * (∑ c, v i a c * v j b c) ^ 2 ≤ f j := by
      apply mul_le_mul_of_nonneg_left _ (hw j)
      exact Finset.single_le_sum (f := fun a' => (∑ c, v i a c * v j a' c) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
    have h0 : w j * (∑ c, v i a c * v j b c) ^ 2 ≤ 0 := by
      have : ∑ j', f j' = 1 := h
      linarith
    have h1 : (∑ c, v i a c * v j b c) ^ 2 ≤ 0 := by
      by_contra hc
      have := mul_pos hj (not_le.mp hc)
      linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h1 (sq_nonneg _))

end PEqualNP.Outside.L_lib_567_aux

theorem PEqualNP.Outside.L_lib_567 : ∀ (n k : ℕ) (m : Fin k → ℕ) (v : (j : Fin k) → Fin (m j) → Fin n → ℝ) (w : Fin k → ℝ),
  (∀ j, 0 < m j) →
  let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
  (∀ j, 0 ≤ w j) →
  (∀ j a b, dot (v j a) (v j b) = if a = b then 1 else 0) →
  (∀ x, (∑ j, w j * (∑ a, (dot x (v j a))^2)) = dot x x) →
  (∀ j, w j ≤ 1) ∧
    ∀ i j, i ≠ j → w i = 1 → 0 < w j → ∀ a b, dot (v i a) (v j b) = 0 := by
  intro n k m v w hm dot hw hon hpar
  exact PEqualNP.Outside.L_lib_567_aux.main n k m v w hm hw hon hpar
