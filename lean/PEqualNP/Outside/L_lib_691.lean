import Mathlib

namespace PEqualNP.Outside.L_lib_691_aux

theorem fwd (q : ℕ) (T : Fin (q + 3) → Fin q → Fin q)
    (hfib : ∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2)
    (x : Fin q → Fin q) (hx : ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) :
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j)) := by
  classical
  choose g hg using hx
  let load := fun j : Fin q => (Finset.univ.filter (fun r => g r = j)).card
  have hl : ∀ j, load j ≤ 2 := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hfib j (x j))
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [← hr]; exact hg r
  have hsum : ∑ j, load j = q + 3 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 3))))
      (t := (Finset.univ : Finset (Fin q))) (f := g) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  let J := Finset.univ.filter (fun j => load j = 2)
  have hJ : 3 ≤ J.card := by
    have h1 : ∑ j, load j ≤ ∑ j, (if load j = 2 then 2 else 1) := by
      apply Finset.sum_le_sum
      intro j _
      have := hl j
      split_ifs with h
      · omega
      · omega
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const] at h1
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin q)))
      (fun j => load j = 2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1 h2
    show 3 ≤ (Finset.univ.filter (fun j => load j = 2)).card
    omega
  obtain ⟨J3, hJ3sub, hJ3⟩ := Finset.exists_subset_card_eq hJ
  let c : Fin 3 → Fin q := fun k => J3.orderEmbOfFin hJ3 k
  have hc : ∀ k, c k ∈ J := fun k => hJ3sub (Finset.orderEmbOfFin_mem J3 hJ3 k)
  refine ⟨c, fun k => Finset.univ.filter (fun r => g r = c k), ?_, ?_, ?_⟩
  · intro a b h
    exact (J3.orderEmbOfFin hJ3).injective h
  · intro k
    refine ⟨?_, x (c k), ?_⟩
    · have := hc k
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [← hr]; exact hg r
  · intro i j hij
    rw [Finset.disjoint_left]
    intro r hri hrj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hri hrj
    exact hij ((J3.orderEmbOfFin hJ3).injective (hri.symm.trans hrj))

theorem bwd (q : ℕ) (T : Fin (q + 3) → Fin q → Fin q)
    (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3)))
    (hc : Function.Injective c)
    (hP : ∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a)
    (hdis : ∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j)) :
    ∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j := by
  classical
  choose a ha using fun k => (hP k).2
  let Rc : Finset (Fin (q + 3)) := Finset.univ.biUnion P
  let Cc : Finset (Fin q) := Finset.univ.image c
  have hRc : Rc.card = 6 := by
    rw [Finset.card_biUnion (fun i _ j _ h => hdis i j h)]
    simp [(hP _).1]
  have hCc : Cc.card = 3 := by
    rw [Finset.card_image_of_injective _ hc]; simp
  let R' := Rcᶜ
  let C' := Ccᶜ
  have hcard : Fintype.card R' = Fintype.card C' := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hRc, hCc, R', C']
    omega
  let e : R' ≃ C' := Fintype.equivOfCardEq hcard
  let x : Fin q → Fin q := fun j =>
    if j = c 0 then a 0 else if j = c 1 then a 1 else if j = c 2 then a 2 else
      if h : j ∈ C' then T (e.symm ⟨j, h⟩).val j else j
  refine ⟨x, fun r => ?_⟩
  by_cases hr : r ∈ Rc
  · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.1 hr
    refine ⟨c k, ?_⟩
    rw [ha k r hk]
    have h01 : c 0 ≠ c 1 := fun h => by have := hc h; simp at this
    have h02 : c 0 ≠ c 2 := fun h => by have := hc h; simp at this
    have h12 : c 1 ≠ c 2 := fun h => by have := hc h; simp at this
    fin_cases k <;> simp [x, h01, h02, h12, h01.symm, h02.symm, h12.symm]
  · have hr' : r ∈ R' := by simp [R', hr]
    let j := (e ⟨r, hr'⟩).val
    have hj : j ∈ C' := (e ⟨r, hr'⟩).property
    refine ⟨j, ?_⟩
    have hjC : j ∉ Cc := by simpa [C'] using hj
    have hk : ∀ k, j ≠ c k := fun k h => hjC (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h.symm⟩)
    simp only [x, if_neg (hk 0), if_neg (hk 1), if_neg (hk 2), dif_pos hj]
    have : e.symm ⟨j, hj⟩ = ⟨r, hr'⟩ := by
      rw [Equiv.symm_apply_eq]
    rw [this]

end PEqualNP.Outside.L_lib_691_aux

theorem PEqualNP.Outside.L_lib_691 : ∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
  (∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2) →
  ((∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) ↔
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j))) := by
  intro q T _ hfib
  exact ⟨fun ⟨x, hx⟩ => PEqualNP.Outside.L_lib_691_aux.fwd q T hfib x hx,
    fun ⟨c, P, hc, hP, hd⟩ => PEqualNP.Outside.L_lib_691_aux.bwd q T c P hc hP hd⟩
