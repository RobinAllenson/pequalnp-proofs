import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21703 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266911 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[2,4]⟩,⟨.and,[1,5]⟩,⟨.and,[2,3]⟩,⟨.or,[4,7]⟩,⟨.or,[1,8]⟩,⟨.not,[9]⟩,⟨.or,[6,10]⟩,⟨.or,[0,11]⟩],12⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
