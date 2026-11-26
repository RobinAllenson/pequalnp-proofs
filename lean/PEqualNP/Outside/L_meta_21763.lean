import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21763 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12633 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [0, 4]⟩,
      ⟨.and, [5, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩,
      ⟨.not, [10]⟩, ⟨.and, [6, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp
