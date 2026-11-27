import Mathlib

namespace PEqualNP.Outside.L_lib_578_aux

theorem P_congr {n l : ℕ} (L : Fin l → Finset (Fin n)) (p : (i : Fin l) → ((↥(L i) → Bool) → Bool))
    (x x' : Fin n → Bool) (h : ∀ v, (∃ i, v ∈ L i) → x v = x' v) :
    (∀ i, p i (fun v => x v.val) = true) ↔ (∀ i, p i (fun v => x' v.val) = true) := by
  have : ∀ i, (fun v : ↥(L i) => x v.val) = (fun v => x' v.val) :=
    fun i => funext fun v => h v.val ⟨i, v.2⟩
  simp only [this]

theorem decomp {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j)
    (p : (i : Fin l) → ((↥(L i) → Bool) → Bool)) (q : (j : Fin r) → ((↥(R j) → Bool) → Bool)) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧ (∀ j, q j (fun v => x v.val) = true))).card =
    ∑ σ ∈ (Finset.univ : Finset (Fin n → Bool)).filter
        (fun σ => ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false),
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧
        (∀ v, ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → x v = σ v) ∧
        (∀ v, ¬ (∃ i, v ∈ L i) → x v = false))).card *
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
        (∀ j, q j (fun v => y v.val) = true) ∧
        (∀ v, ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → y v = σ v) ∧
        (∀ v, ¬ (∃ j, v ∈ R j) → y v = false))).card := by
  classical
  let f : (Fin n → Bool) → (Fin n → Bool) := fun z v =>
    if ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) then z v else false
  rw [Finset.card_eq_sum_card_fiberwise (f := f)]
  · apply Finset.sum_congr rfl
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [← Finset.card_product]
    apply Finset.card_nbij'
      (fun z => ((fun v => if (∃ i, v ∈ L i) then z v else false),
        (fun v => if (∃ j, v ∈ R j) then z v else false)))
      (fun xy => fun v => if (∃ i, v ∈ L i) then xy.1 v else xy.2 v)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hz
      obtain ⟨⟨hP, hQ⟩, hf⟩ := hz
      have hfz : ∀ v, ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → z v = σ v := by
        intro v hv
        have := congrFun hf v
        simp only [f, if_pos hv] at this
        exact this
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      refine ⟨⟨(P_congr L p (fun v => if (∃ i, v ∈ L i) then z v else false) z
          (fun v hv => by simp [hv])).2 hP, fun v hv => by simp [hv.1, hfz v hv],
        fun v hv => by simp [hv]⟩, ⟨(P_congr R q (fun v => if (∃ j, v ∈ R j) then z v else false) z
          (fun v hv => by simp [hv])).2 hQ,
        fun v hv => by simp [hv.2, hfz v hv], fun v hv => by simp [hv]⟩⟩
    · intro xy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hxy
      obtain ⟨⟨hP, hxS, hx0⟩, ⟨hQ, hyS, hy0⟩⟩ := hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      refine ⟨⟨(P_congr L p (fun v => if (∃ i, v ∈ L i) then xy.1 v else xy.2 v) xy.1
          (fun v hv => by simp [hv])).2 hP,
        (P_congr R q (fun v => if (∃ i, v ∈ L i) then xy.1 v else xy.2 v) xy.2
          (fun v hv => ?_)).2 hQ⟩, ?_⟩
      · by_cases hl : ∃ i, v ∈ L i
        · simp only [hl, ite_true]
          rw [hxS v ⟨hl, hv⟩, hyS v ⟨hl, hv⟩]
        · simp [hl]
      · funext v
        simp only [f]
        split_ifs with h1 h2
        · rw [hxS v h1]
        · exact absurd h1.1 h2
        · by_cases hσv : σ v = false
          · exact hσv.symm
          · exact absurd (hσ v h1) hσv
    · intro z _
      funext v
      by_cases hl : ∃ i, v ∈ L i
      · simp [hl]
      · have hr := (hcov v).resolve_left hl
        simp [hl, hr]
    · intro xy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hxy
      obtain ⟨⟨hP, hxS, hx0⟩, ⟨hQ, hyS, hy0⟩⟩ := hxy
      ext v
      · by_cases hl : ∃ i, v ∈ L i
        · simp [hl]
        · simp [hl, hx0 v hl]
      · by_cases hr : ∃ j, v ∈ R j
        · by_cases hl : ∃ i, v ∈ L i
          · simp only [hr, hl, ite_true]
            rw [hxS v ⟨hl, hr⟩, hyS v ⟨hl, hr⟩]
          · simp [hr, hl]
        · simp [hr, hy0 v hr]
  · intro z _
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    intro v hv
    simp only [f]
    simp [hv]

theorem card_masks {n : ℕ} (S : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => ∀ v, v ∉ S → σ v = false)).card
      = 2 ^ S.card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_nbij' (fun σ => S.filter (fun v => σ v = true))
    (fun T => fun v => decide (v ∈ T))
  · intro σ _
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.filter_subset _ _
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_powerset] at hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    intro v hv
    simp only [decide_eq_false_iff_not]
    exact fun h => hv (hT h)
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hσ
    funext v
    by_cases hv : v ∈ S
    · cases h : σ v <;> simp [hv, h]
    · simp [hv, hσ v hv]
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_powerset] at hT
    ext v
    simp only [Finset.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩

theorem diag {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (σ τ : Fin n → Bool)
    (hσ : ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false)
    (hτ : ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → τ v = false) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, (fun (i : Fin l) (f : ↥(L i) → Bool) => decide (∀ v : ↥(L i), f v = σ v.val)) i
        (fun v => x v.val) = true) ∧
      (∀ j, (fun (j : Fin r) (f : ↥(R j) → Bool) => decide (∀ v : ↥(R j), f v = τ v.val)) j
        (fun v => x v.val) = true))).card = if σ = τ then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Finset.card_eq_one]
    refine ⟨σ, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      funext v
      rcases hcov v with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact h1 i ⟨v, hi⟩
      · exact h2 j ⟨v, hj⟩
    · rintro rfl
      exact ⟨fun i v => rfl, fun j v => rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    simp only [decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    obtain ⟨v, hv⟩ := Function.ne_iff.1 h
    by_cases hS : (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j
    · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hS
      have a1 := h1 i ⟨v, hi⟩
      have a2 := h2 j ⟨v, hj⟩
      exact hv (a1.symm.trans a2)
    · exact hv ((hσ v hS).trans (hτ v hS).symm)

theorem main (K : Type) [Field K] {n l r : ℕ} (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (d : ℕ) :
    (∃ (A : ((i : Fin l) → ((↥(L i) → Bool) → Bool)) → Fin d → K)
       (B : ((j : Fin r) → ((↥(R j) → Bool) → Bool)) → Fin d → K),
      ∀ p q, ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧ (∀ j, q j (fun v => x v.val) = true))).card : ℕ) : K)
          = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ ((Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)).card ≤ d := by
  classical
  set Sig := (Finset.univ : Finset (Fin n → Bool)).filter
        (fun σ => ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false) with hSig
  have hcard : Sig.card = 2 ^ ((Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)).card := by
    rw [← card_masks]
    congr 1
    ext σ
    simp [Sig]
  rw [← hcard]
  constructor
  · rintro ⟨A, B, hAB⟩
    let pp : Sig → ((i : Fin l) → ((↥(L i) → Bool) → Bool)) := fun σ i f =>
      decide (∀ v : ↥(L i), f v = σ.val v.val)
    let qq : Sig → ((j : Fin r) → ((↥(R j) → Bool) → Bool)) := fun σ j f =>
      decide (∀ v : ↥(R j), f v = σ.val v.val)
    let Ma : Matrix Sig (Fin d) K := Matrix.of fun σ j => A (pp σ) j
    let Mb : Matrix (Fin d) Sig K := Matrix.of fun j τ => B (qq τ) j
    have hM : Ma * Mb = 1 := by
      ext σ τ
      simp only [Matrix.mul_apply, Ma, Mb, Matrix.of_apply]
      rw [← hAB]
      have hσ := σ.2
      have hτ := τ.2
      simp only [Sig, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hτ
      rw [show (pp σ) = (fun (i : Fin l) (f : ↥(L i) → Bool) => decide (∀ v : ↥(L i), f v = σ.val v.val))
        from rfl, show (qq τ) = (fun (j : Fin r) (f : ↥(R j) → Bool) =>
          decide (∀ v : ↥(R j), f v = τ.val v.val)) from rfl, diag L R hcov σ.val τ.val hσ hτ,
        Matrix.one_apply]
      by_cases h : σ = τ
      · rw [if_pos h, if_pos (congrArg Subtype.val h)]; simp
      · rw [if_neg h, if_neg (fun e => h (Subtype.ext e))]; simp
    have h1 := Matrix.rank_one (R := K) (n := Sig)
    rw [← hM] at h1
    have h2 := Matrix.rank_mul_le_left Ma Mb
    have h3 := Matrix.rank_le_card_width Ma
    simp only [Fintype.card_fin, Fintype.card_coe] at h1 h3
    omega
  · intro hc
    obtain ⟨m, rfl⟩ : ∃ m, d = Sig.card + m := ⟨d - Sig.card, by omega⟩
    let e := Sig.equivFin
    let A' : ((i : Fin l) → ((↥(L i) → Bool) → Bool)) → (Fin n → Bool) → K := fun p σ =>
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧
        (∀ v, ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → x v = σ v) ∧
        (∀ v, ¬ (∃ i, v ∈ L i) → x v = false))).card : K)
    let B' : ((j : Fin r) → ((↥(R j) → Bool) → Bool)) → (Fin n → Bool) → K := fun q σ =>
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun y =>
        (∀ j, q j (fun v => y v.val) = true) ∧
        (∀ v, ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → y v = σ v) ∧
        (∀ v, ¬ (∃ j, v ∈ R j) → y v = false))).card : K)
    refine ⟨fun p j => if h : j.val < Sig.card then A' p (e.symm ⟨j.val, h⟩).val else 0,
      fun q j => if h : j.val < Sig.card then B' q (e.symm ⟨j.val, h⟩).val else 0, ?_⟩
    intro p q
    rw [decomp L R hcov p q, Fin.sum_univ_add]
    push_cast
    have h2 : ∑ i : Fin m, (if h : (Fin.natAdd Sig.card i).val < Sig.card then
        A' p (e.symm ⟨(Fin.natAdd Sig.card i).val, h⟩).val else 0) *
        (if h : (Fin.natAdd Sig.card i).val < Sig.card then
        B' q (e.symm ⟨(Fin.natAdd Sig.card i).val, h⟩).val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : ¬ (Fin.natAdd Sig.card i).val < Sig.card := by simp
      rw [dif_neg this, zero_mul]
    rw [h2, add_zero]
    have h3 : ∀ i : Fin Sig.card, (if h : (Fin.castAdd m i).val < Sig.card then
        A' p (e.symm ⟨(Fin.castAdd m i).val, h⟩).val else 0) *
        (if h : (Fin.castAdd m i).val < Sig.card then
        B' q (e.symm ⟨(Fin.castAdd m i).val, h⟩).val else 0) =
        A' p (e.symm i).val * B' q (e.symm i).val := by
      intro i
      have hi : (Fin.castAdd m i).val < Sig.card := i.isLt
      rw [dif_pos hi, dif_pos hi]
      rfl
    simp only [h3]
    rw [Equiv.sum_comp e.symm (fun σ => A' p σ.val * B' q σ.val)]
    rw [Finset.sum_coe_sort Sig (fun σ => A' p σ * B' q σ)]

end PEqualNP.Outside.L_lib_578_aux

theorem PEqualNP.Outside.L_lib_578 : ∀ (K : Type) [Field K] (n l r : ℕ)
  (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)),
  (∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) →
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
  let Left := (i : Fin l) → ((↥(L i) → Bool) → Bool)
  let Right := (j : Fin r) → ((↥(R j) → Bool) → Bool)
  let count := fun (p : Left) (q : Right) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧
      (∀ j, q j (fun v => x v.val) = true))).card
  ∀ d : ℕ,
    (∃ (A : Left → Fin d → K) (B : Right → Fin d → K),
      ∀ p q, (count p q : K) = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ S.card ≤ d := by
  intro K _ n l r L R hcov S Left Right count d
  exact PEqualNP.Outside.L_lib_578_aux.main K L R hcov d
