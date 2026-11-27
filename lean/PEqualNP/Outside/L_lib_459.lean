import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_459_aux

def e {n : ℕ} (s : Fin n × Fin n → Bool) (p : Fin n × Fin n) : ℝ := if s p then -1 else 1

theorem e_sq {n : ℕ} (s : Fin n × Fin n → Bool) (p : Fin n × Fin n) : e s p * e s p = 1 := by
  unfold e
  split_ifs <;> norm_num

theorem e_update_same {n : ℕ} (s : Fin n × Fin n → Bool) (p : Fin n × Fin n) :
    e (Function.update s p (!s p)) p = - e s p := by
  unfold e
  rw [Function.update_self]
  cases s p <;> simp

theorem e_update_ne {n : ℕ} (s : Fin n × Fin n → Bool) (p q : Fin n × Fin n) (h : q ≠ p) :
    e (Function.update s p (!s p)) q = e s q := by
  unfold e
  rw [Function.update_of_ne h]

def flip {n : ℕ} (p : Fin n × Fin n) : Equiv.Perm (Fin n × Fin n → Bool) :=
  Function.Involutive.toPerm (fun s => Function.update s p (!s p)) (by
    intro s
    funext q
    by_cases h : q = p
    · subst h
      simp
    · simp [Function.update_of_ne h])

theorem flip_apply {n : ℕ} (p : Fin n × Fin n) (s : Fin n × Fin n → Bool) :
    flip p s = Function.update s p (!s p) := rfl

theorem orth {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ∑ s : Fin n × Fin n → Bool, ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) =
      if σ = τ then (2 : ℝ) ^ (n * n) else 0 := by
  split_ifs with h
  · subst h
    simp [e_sq]
  · have hex : ∃ i, σ i ≠ τ i := by
      by_contra hne
      exact h (Equiv.ext (fun i => by
        by_contra hi
        exact hne ⟨i, hi⟩))
    obtain ⟨i0, hi0⟩ := hex
    have key : ∑ s : Fin n × Fin n → Bool, ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) =
        ∑ s : Fin n × Fin n → Bool, -∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) := by
      refine ((Equiv.sum_comp (flip (σ i0, i0))
        (fun s : Fin n × Fin n → Bool => ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)))).symm).trans ?_
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [flip_apply]
      have hpt : ∀ i : Fin n,
          e (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i, i) *
            e (Function.update s (σ i0, i0) (!s (σ i0, i0))) (τ i, i) =
          (if i = i0 then (-1 : ℝ) else 1) * (e s (σ i, i) * e s (τ i, i)) := by
        intro i
        by_cases hi : i = i0
        · subst hi
          rw [e_update_same, e_update_ne s (σ i, i) (τ i, i)
            (fun h' => hi0 (Prod.mk.inj h').1.symm)]
          simp
        · rw [e_update_ne s (σ i0, i0) (σ i, i) (fun h' => hi (Prod.mk.inj h').2),
            e_update_ne s (σ i0, i0) (τ i, i) (fun h' => hi (Prod.mk.inj h').2)]
          simp [hi]
      rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib]
      simp
    rw [Finset.sum_neg_distrib] at key
    linarith

theorem core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Equiv.Perm (Fin n) → ℝ)
    (hc : ∀ σ, c σ * c σ = 1) :
    ∑ s : Fin n × Fin n → Bool,
      (∑ σ : Equiv.Perm (Fin n), c σ * ∏ i : Fin n, (e s (σ i, i) * A (σ i) i)) ^ 2 =
    (2 : ℝ) ^ (n * n) * ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, A (σ i) i ^ 2 := by
  have h1 : ∀ (s : Fin n × Fin n → Bool) (σ τ : Equiv.Perm (Fin n)),
      (c σ * ∏ i : Fin n, (e s (σ i, i) * A (σ i) i)) *
        (c τ * ∏ i : Fin n, (e s (τ i, i) * A (τ i) i)) =
      (c σ * c τ * ∏ i : Fin n, (A (σ i) i * A (τ i) i)) *
        ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) := by
    intro s σ τ
    simp only [Finset.prod_mul_distrib]
    ring
  calc ∑ s : Fin n × Fin n → Bool,
      (∑ σ : Equiv.Perm (Fin n), c σ * ∏ i : Fin n, (e s (σ i, i) * A (σ i) i)) ^ 2
      = ∑ s : Fin n × Fin n → Bool, ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
          (c σ * c τ * ∏ i : Fin n, (A (σ i) i * A (τ i) i)) *
            ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => h1 s σ τ))
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), ∑ s : Fin n × Fin n → Bool,
          (c σ * c τ * ∏ i : Fin n, (A (σ i) i * A (τ i) i)) *
            ∏ i : Fin n, (e s (σ i, i) * e s (τ i, i)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun σ _ => Finset.sum_comm)
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
          (c σ * c τ * ∏ i : Fin n, (A (σ i) i * A (τ i) i)) *
            (if σ = τ then (2 : ℝ) ^ (n * n) else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
        rw [← Finset.mul_sum, orth]
    _ = (2 : ℝ) ^ (n * n) * ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, A (σ i) i ^ 2 := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        have hp : ∏ i : Fin n, (A (σ i) i * A (σ i) i) = ∏ i : Fin n, A (σ i) i ^ 2 :=
          Finset.prod_congr rfl (fun i _ => (sq _).symm)
        rw [hc, hp]
        ring

theorem main (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ s : Fin n × Fin n → Bool, (Matrix.det
      ((fun i j => if s (i,j) then -A i j else A i j) : Matrix (Fin n) (Fin n) ℝ)) ^ 2) =
    (2 : ℝ)^(n*n) * Matrix.permanent ((fun row col => A row col ^ 2) : Matrix (Fin n) (Fin n) ℝ) := by
  have hc : ∀ σ : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hs : ∀ s : Fin n × Fin n → Bool, Matrix.det
      ((fun i j => if s (i,j) then -A i j else A i j) : Matrix (Fin n) (Fin n) ℝ) =
      ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) *
        ∏ i : Fin n, (e s (σ i, i) * A (σ i) i) := by
    intro s
    refine (Matrix.det_apply' _).trans ?_
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    show (if s (σ i, i) then -A (σ i) i else A (σ i) i) = _
    unfold e
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => by rw [hs s]), core A _ hc]
  rfl

end PEqualNP.Outside.L_lib_459_aux

theorem PEqualNP.Outside.L_lib_459 : (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
  let signed : (Fin n × Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ := fun s =>
    fun i j => if s (i,j) then -A i j else A i j
  let weights : Matrix (Fin n) (Fin n) ℝ := fun row col => A row col ^ 2
  (∑ s : Fin n × Fin n → Bool, (Matrix.det (signed s)) ^ 2) =
    (2 : ℝ)^(n*n) * weights.permanent) := by
  intro n A signed weights
  exact PEqualNP.Outside.L_lib_459_aux.main n A
