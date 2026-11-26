import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24824 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148286 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
