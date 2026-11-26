import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19380
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def net (n : ℕ) : Circuit :=
  ⟨[⟨.or, [n + (n - 1), n + (n - 2)]⟩,
    ⟨.and, [0,n+n]⟩, ⟨.or,[0,n+(n-1)]⟩,
    ⟨.and,[1,n+(n-2)]⟩, ⟨.or,[n+n+2,n+n+3]⟩,
    ⟨.not,[n+n+4]⟩, ⟨.or,[n+n+1,n+n+5]⟩], n+n+6⟩

theorem readSnoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i = w.length
  · subst i; simp [List.getD]
  · by_cases h' : i < w.length
    · simp [h, List.getD, List.getElem?_append_left h']
    · have hg : (w ++ [b]).length ≤ i := by simp; omega
      have hg' : w.length ≤ i := by omega
      simp [h, List.getD, List.getElem?_eq_none hg, List.getElem?_eq_none hg']

theorem leftRead {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [Fin.ext_iff]

theorem rightRead {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD (n+i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [Fin.ext_iff]

theorem opAnd (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
theorem opOr (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
theorem opNot (a : Bool) : GateOp.not.eval [a] = !a := rfl

theorem computed {n : ℕ} (hn : 3 ≤ n) (u v : Fin n) :
    (net n).eval (oneEach u v) =
       ((decide (0 = u.val) && (decide (n-1 = v.val) || decide (n-2 = v.val))) ||
       !((decide (0 = u.val) || decide (n-1 = v.val)) || (decide (1 = u.val) && decide (n-2 = v.val)))) := by
  have hl : (oneEach u v).length = n+n := by simp [oneEach]
  simp only [net, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, opAnd, opOr, opNot]
  have val0 := leftRead u v (0) (by omega)
  have val1 := leftRead u v (1) (by omega)
  have val2 := rightRead u v ((n-1)) (by omega)
  have val3 := rightRead u v ((n-2)) (by omega)
  have e0_0 : 0 ≠ n+n := by omega
  have e0_1 : 0 ≠ n+n+1 := by omega
  have e1_0 : 1 ≠ n+n := by omega
  have e1_1 : 1 ≠ n+n+1 := by omega
  have e1_2 : 1 ≠ n+n+2 := by omega
  have e2_0 : n+(n-1) ≠ n+n := by omega
  have e2_1 : n+(n-1) ≠ n+n+1 := by omega
  have e3_0 : n+(n-2) ≠ n+n := by omega
  have e3_1 : n+(n-2) ≠ n+n+1 := by omega
  have e3_2 : n+(n-2) ≠ n+n+2 := by omega
  have e5_0 : n+n+1 ≠ n+n := by omega
  have e5_2 : n+n+1 ≠ n+n+2 := by omega
  have e5_3 : n+n+1 ≠ n+n+3 := by omega
  have e5_4 : n+n+1 ≠ n+n+4 := by omega
  have e5_5 : n+n+1 ≠ n+n+5 := by omega
  have e6_0 : n+n+2 ≠ n+n := by omega
  have e6_1 : n+n+2 ≠ n+n+1 := by omega
  have e6_3 : n+n+2 ≠ n+n+3 := by omega
  have e7_0 : n+n+3 ≠ n+n := by omega
  have e7_1 : n+n+3 ≠ n+n+1 := by omega
  have e7_2 : n+n+3 ≠ n+n+2 := by omega
  have e8_0 : n+n+4 ≠ n+n := by omega
  have e8_1 : n+n+4 ≠ n+n+1 := by omega
  have e8_2 : n+n+4 ≠ n+n+2 := by omega
  have e8_3 : n+n+4 ≠ n+n+3 := by omega
  have e9_0 : n+n+5 ≠ n+n := by omega
  have e9_1 : n+n+5 ≠ n+n+1 := by omega
  have e9_2 : n+n+5 ≠ n+n+2 := by omega
  have e9_3 : n+n+5 ≠ n+n+3 := by omega
  have e9_4 : n+n+5 ≠ n+n+4 := by omega
  have e10_0 : n+n+6 ≠ n+n := by omega
  have e10_1 : n+n+6 ≠ n+n+1 := by omega
  have e10_2 : n+n+6 ≠ n+n+2 := by omega
  have e10_3 : n+n+6 ≠ n+n+3 := by omega
  have e10_4 : n+n+6 ≠ n+n+4 := by omega
  have e10_5 : n+n+6 ≠ n+n+5 := by omega
  simp only [Nat.add_assoc] at *
  simp only [readSnoc, List.length_append, List.length_singleton, hl, Nat.add_assoc, Nat.reduceAdd, ite_true, ite_false, eq_self, val0, val1, val2, val3, e0_0, e0_1, e1_0, e1_1, e1_2, e2_0, e2_1, e3_0, e3_1, e3_2, e5_0, e5_2, e5_3, e5_4, e5_5, e6_0, e6_1, e6_3, e7_0, e7_1, e7_2, e8_0, e8_1, e8_2, e8_3, e9_0, e9_1, e9_2, e9_3, e9_4, e10_0, e10_1, e10_2, e10_3, e10_4, e10_5]

end PEqualNP.Outside.L_meta_19380
open PEqualNP.Outside.L_meta_19380 PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_19380 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (u.val = 1 ∧ ¬ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (2 ≤ u.val ∧ v.val + 1 ≠ n))) C := by
  intro n hn
  refine ⟨net n, ?_, by exact Nat.le_refl 7, ?_⟩
  · intro g hg
    simp [net] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    rw [computed hn]
    rw [Bool.eq_iff_iff]
    simp
    omega
