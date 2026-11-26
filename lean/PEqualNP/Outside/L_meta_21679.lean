import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21679 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4955 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[0,1]⟩,⟨.and,[2,5]⟩,⟨.or,[3,4]⟩,⟨.not,[5]⟩,⟨.and,[7,8]⟩,⟨.or,[6,9]⟩,⟨.not,[10]⟩],11⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
