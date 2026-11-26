import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21960 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not,[5]⟩,⟨.and,[2, 3]⟩,⟨.or,[2, 3]⟩,⟨.not,[8]⟩,⟨.and,[1, 9]⟩,⟨.or,[7, 10]⟩,⟨.or,[0, 11]⟩,⟨.and,[6, 12]⟩],13⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
