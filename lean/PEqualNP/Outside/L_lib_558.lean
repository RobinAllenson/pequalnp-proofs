import Mathlib

namespace PEqualNP.Outside.L_lib_558_aux

theorem absl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Submodule ℝ E)
    [FiniteDimensional ℝ K] (n m : ℕ) (N : ℝ) (g : Fin n → E) (σ : Fin m ↪ Fin n)
    (hg : ∀ j, g (σ j) ∈ K)
    (hframe : ∀ e : E, ∑ c, (inner ℝ (g c) e) ^ 2 ≤ N * ‖e‖ ^ 2) :
    ∑ j, ‖g (σ j)‖ ^ 2 ≤ N * (Module.finrank ℝ K) := by
  set b := stdOrthonormalBasis ℝ K
  have h1 : ∀ j, ‖g (σ j)‖ ^ 2 = ∑ k, (inner ℝ (g (σ j)) ((b k : K) : E)) ^ 2 := by
    intro j
    have := b.sum_sq_norm_inner_right (⟨g (σ j), hg j⟩ : K)
    simp only [Real.norm_eq_abs, sq_abs] at this
    rw [show ‖g (σ j)‖ = ‖(⟨g (σ j), hg j⟩ : K)‖ from rfl, ← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_comm]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  calc ∑ k, ∑ j, (inner ℝ (g (σ j)) ((b k : K) : E)) ^ 2
      ≤ ∑ k, ∑ c, (inner ℝ (g c) ((b k : K) : E)) ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [← Finset.sum_map Finset.univ σ (fun c => (inner ℝ (g c) ((b k : K) : E)) ^ 2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ k : Fin (Module.finrank ℝ K), N := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have := hframe ((b k : K) : E)
        have hn : ‖((b k : K) : E)‖ = 1 := by
          exact b.orthonormal.1 k
        rw [hn] at this
        simpa using this
    _ = N * (Module.finrank ℝ K) := by simp [mul_comm]

theorem frame (n a : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (rows : Fin a ↪ Fin n)
    (horth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (x : Fin a → ℝ) :
    ∑ j, (∑ i, x i * H (rows i) j) ^ 2 = n * ∑ i, x i ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  have : ∀ i' : Fin a, ∑ j, x i * H (rows i) j * (x i' * H (rows i') j) =
      x i * x i' * (if i = i' then (n : ℝ) else 0) := by
    intro i'
    have hh := horth (rows i) (rows i')
    simp only [rows.injective.eq_iff] at hh
    rw [← hh, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun i' _ => this i')]
  simp
  ring

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1)
    (horth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n) :
    a * b ≤ n * (H.submatrix rows cols).rank := by
  set B := H.submatrix rows cols
  let e := (WithLp.linearEquiv 2 ℝ (Fin a → ℝ)).symm
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin a)) := (LinearMap.range B.mulVecLin).map e.toLinearMap
  have hK : Module.finrank ℝ K = B.rank := by
    unfold Matrix.rank
    exact LinearEquiv.finrank_map_eq e _
  let g : Fin n → EuclideanSpace ℝ (Fin a) := fun c => WithLp.toLp 2 (fun i => H (rows i) c)
  have hg : ∀ j, g (cols j) ∈ K := by
    intro j
    refine Submodule.mem_map.mpr ⟨B.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, ?_⟩
    rw [Matrix.mulVec_single_one]
    rfl
  have hfr : ∀ v : EuclideanSpace ℝ (Fin a), ∑ c, (inner ℝ (g c) v) ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
    intro v
    have h1 : ∀ c, inner ℝ (g c) v = ∑ i, (WithLp.ofLp v) i * H (rows i) c := by
      intro c
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [g, dotProduct]
    simp only [h1]
    rw [frame n a H rows horth, EuclideanSpace.norm_sq_eq]
    simp
  have := absl K n b (n : ℝ) g cols hg hfr
  rw [hK] at this
  have hn : ∀ j, ‖g (cols j)‖ ^ 2 = a := by
    intro j
    rw [EuclideanSpace.norm_sq_eq]
    have : ∀ i, (WithLp.ofLp (g (cols j))) i ^ 2 = 1 := by
      intro i
      simp only [g]
      rcases hpm (rows i) (cols j) with h | h <;> simp [h]
    simp only [Real.norm_eq_abs, sq_abs, this]
    simp
  simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact_mod_cast (show ((a * b : ℕ) : ℝ) ≤ ((n * B.rank : ℕ) : ℝ) by push_cast; linarith)

end PEqualNP.Outside.L_lib_558_aux

theorem PEqualNP.Outside.L_lib_558 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n),
    a * b ≤ n * (H.submatrix rows cols).rank := by
  intro n H _ hpm horth a b rows cols
  exact PEqualNP.Outside.L_lib_558_aux.main n H hpm horth a b rows cols
