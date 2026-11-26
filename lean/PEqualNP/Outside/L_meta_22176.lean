import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16923 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [16, 15]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
