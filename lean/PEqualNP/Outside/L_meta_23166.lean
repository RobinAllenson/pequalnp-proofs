import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23166 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30334 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [2, 16]⟩, ⟨.and, [12, 17]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
