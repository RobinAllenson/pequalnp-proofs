import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24110 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12632 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[3,4]⟩,⟨.and,[0,5]⟩,⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.or,[4,8]⟩,⟨.or,[0,9]⟩,⟨.not,[10]⟩,⟨.and,[7,11]⟩,⟨.or,[6,12]⟩],13⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
