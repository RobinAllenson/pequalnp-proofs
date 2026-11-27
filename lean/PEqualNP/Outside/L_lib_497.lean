import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_497_aux

open MvPolynomial PEqualNP.ProofComplexity

noncomputable def g {n : ℕ} (C : Clause (Fin n)) (i : Fin n) : MvPolynomial (Fin n) (ZMod 2) :=
  if (i, true) ∈ C then 1 + X i else X i

theorem deg_g {n : ℕ} (C : Clause (Fin n)) (i : Fin n) : (g C i).totalDegree ≤ 1 := by
  unfold g
  split_ifs
  · refine (totalDegree_add _ _).trans ?_
    simp [totalDegree_X]
  · simp [totalDegree_X]

theorem deg_D {n : ℕ} (C : Clause (Fin n)) (U : Finset (Fin n)) :
    (∏ i ∈ U, g C i).totalDegree ≤ U.card :=
  (totalDegree_finsetProd U _).trans
    ((Finset.sum_le_card_nsmul U _ 1 (fun i _ => deg_g C i)).trans (by simp))

theorem deg_M {n : ℕ} (U : Finset (Fin n)) :
    (∏ i ∈ U, (X i : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ U.card :=
  (totalDegree_finsetProd U _).trans
    ((Finset.sum_le_card_nsmul U _ 1 (fun i _ => by simp [totalDegree_X])).trans (by simp))

theorem split {n : ℕ} (C : Clause (Fin n)) (U : Finset (Fin n)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), (∏ i ∈ U, g C i) = (∏ i ∈ U, X i) + q ∧
      (q = 0 ∨ q.totalDegree + 1 ≤ U.card) := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl⟩
  | insert a U ha ih =>
    obtain ⟨q, hq, hd⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hq, Finset.card_insert_of_notMem ha]
    by_cases hc : (a, true) ∈ C
    · refine ⟨X a * q + (∏ i ∈ U, X i) + q, ?_, Or.inr ?_⟩
      · simp only [g, hc, ↓reduceIte]
        ring
      · have hM := deg_M (n := n) U
        have h1 : (X a * q).totalDegree ≤ U.card := by
          rcases hd with rfl | hd
          · simp
          · have h3 := totalDegree_mul (X a) q
            rw [totalDegree_X] at h3
            omega
        have h2 : q.totalDegree ≤ U.card := by
          rcases hd with rfl | hd
          · simp
          · omega
        have h4 := le_trans (totalDegree_add (X a * q + ∏ i ∈ U, X i) q)
          (max_le (le_trans (totalDegree_add _ _) (max_le h1 hM)) h2)
        omega
    · refine ⟨X a * q, ?_, ?_⟩
      · simp only [g, hc, ↓reduceIte]
        ring
      · rcases hd with rfl | hd
        · left
          simp
        · right
          have h3 := totalDegree_mul (X a) q
          rw [totalDegree_X] at h3
          omega

theorem clause_eq {n : ℕ} (C : Clause (Fin n))
    (hprop : ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) :
    clausePoly C = ∏ i ∈ C.image Prod.fst, g C i := by
  unfold clausePoly
  rw [Finset.prod_image]
  · refine Finset.prod_congr rfl (fun l hl => ?_)
    obtain ⟨v, b⟩ := l
    cases b
    · have hno : (v, true) ∉ C := fun h => hprop v ⟨h, hl⟩
      simp [g, hno]
    · simp [g, hl]
  · intro l hl l' hl' h
    obtain ⟨v, b⟩ := l
    obtain ⟨v', b'⟩ := l'
    simp only at h
    subst h
    cases b
    · cases b'
      · rfl
      · exact absurd ⟨hl', hl⟩ (hprop v)
    · cases b'
      · exact absurd ⟨hl, hl'⟩ (hprop v)
      · rfl

theorem derive {n : ℕ} (P : Set (MvPolynomial (Fin n) (ZMod 2))) (S : Finset (Fin n))
    (C : Clause (Fin n)) (hVS : C.image Prod.fst ⊆ S)
    (hder : PCDerivable P S.card (∏ i ∈ C.image Prod.fst, g C i)) (T : Finset (Fin n)) :
    T ⊆ S → Disjoint T (C.image Prod.fst) →
      PCDerivable P S.card (∏ i ∈ T ∪ C.image Prod.fst, g C i) := by
  induction T using Finset.induction_on with
  | empty =>
    intro _ _
    rw [Finset.empty_union]
    exact hder
  | insert a T ha ih =>
    intro hsub hdis
    have haV : a ∉ C.image Prod.fst := Finset.disjoint_left.mp hdis (Finset.mem_insert_self a T)
    have haU : a ∉ T ∪ C.image Prod.fst := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact ha h
      · exact haV h
    have hno : (a, true) ∉ C := fun h => haV (Finset.mem_image.mpr ⟨(a, true), h, rfl⟩)
    have hg : g C a = X a := by simp [g, hno]
    have hdeg : (X a * ∏ i ∈ T ∪ C.image Prod.fst, g C i).totalDegree ≤ S.card := by
      rw [← hg, ← Finset.prod_insert haU, ← Finset.insert_union]
      exact (deg_D C _).trans (Finset.card_le_card (Finset.union_subset hsub hVS))
    rw [Finset.insert_union, Finset.prod_insert haU, hg]
    exact PCDerivable.mulX a
      (ih ((Finset.insert_subset_iff.mp hsub).2)
        (Finset.disjoint_of_subset_left (Finset.subset_insert a T) hdis)) hdeg

theorem main (n : ℕ) (F : Set (Clause (Fin n))) (S : Finset (Fin n)) (C : Clause (Fin n))
    (hne : S.Nonempty) (hVS : (C.image Prod.fst) ⊆ S)
    (hprop : ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (hder : PCDerivable (cnfSystem F) S.card (clausePoly C)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
      PCDerivable (cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q) := by
  obtain ⟨q, hq, hd⟩ := split C S
  refine ⟨q, ?_, ?_⟩
  · have hpos : 0 < S.card := Finset.card_pos.mpr hne
    rcases hd with rfl | hd
    · simpa using hpos
    · omega
  · rw [← hq]
    rw [clause_eq C hprop] at hder
    have h := derive (cnfSystem F) S C hVS hder (S \ C.image Prod.fst) Finset.sdiff_subset
      Finset.sdiff_disjoint
    rwa [Finset.sdiff_union_of_subset hVS] at h

end PEqualNP.Outside.L_lib_497_aux

theorem PEqualNP.Outside.L_lib_497 : (∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (S : Finset (Fin n)) (C : PEqualNP.ProofComplexity.Clause (Fin n)),
  S.Nonempty → (C.image Prod.fst) ⊆ S →
  (∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card (PEqualNP.ProofComplexity.clausePoly C) →
  ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
    PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q)) := by
  intro n F S C hne hVS hprop hder
  exact PEqualNP.Outside.L_lib_497_aux.main n F S C hne hVS hprop hder
