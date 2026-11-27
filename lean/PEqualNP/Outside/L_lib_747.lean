import Mathlib

namespace PEqualNP.Outside.L_lib_747_aux

theorem L1 {E K : Type} [Field E] [Field K] [Algebra E K] (T : Set K)
    (ψ : K →ₗ[E] E) (h : ∀ t ∈ T, ψ t = 1) : (0 : K) ∉ affineSpan E T := by
  intro h0
  rcases T.eq_empty_or_nonempty with he | ⟨t0, ht0⟩
  · rw [he, AffineSubspace.span_empty] at h0
    exact (AffineSubspace.notMem_bot E K (0 : K)) h0
  · have hv := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan h0 (mem_affineSpan E ht0)
    have hker : vectorSpan E T ≤ LinearMap.ker ψ := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro v ⟨a, ha, b, hb, rfl⟩
      simp [h a ha, h b hb]
    have := hker hv
    simp [h t0 ht0] at this

theorem L2 {E K : Type} [Field E] [Field K] [Algebra E K] (T : Set K)
    (h0 : (0 : K) ∉ affineSpan E T) : ∃ ψ : K →ₗ[E] E, ∀ t ∈ T, ψ t = 1 := by
  rcases T.eq_empty_or_nonempty with he | ⟨t0, ht0⟩
  · exact ⟨0, by simp [he]⟩
  · have hnot : t0 ∉ vectorSpan E T := by
      intro ht
      apply h0
      have hneg : -t0 ∈ vectorSpan E T := Submodule.neg_mem _ ht
      have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) (mem_affineSpan E ht0)
      simpa using this
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    refine ⟨(f t0)⁻¹ • f, fun t ht => ?_⟩
    have hd : t - t0 ∈ vectorSpan E T := vsub_mem_vectorSpan E ht ht0
    have hz : f (t - t0) = 0 := by
      have : f (t - t0) ∈ (vectorSpan E T).map f := Submodule.mem_map_of_mem hd
      rw [hmap] at this
      simpa using this
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [map_sub, sub_eq_zero] at hz
    rw [hz, inv_mul_cancel₀ hf]

theorem fwd {E K : Type} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K) (C : K →ₗ[E] K) (hC : Module.finrank E (LinearMap.range C) ≤ 1)
    (hS : ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x) (h0 : (0 : K) ∉ S) :
    ∃ ψ : K →ₗ[E] E, ∀ t ∈ (fun z : K => z⁻¹) '' (↑S : Set K), ψ t = 1 := by
  rcases S.eq_empty_or_nonempty with he | ⟨z0, hz0⟩
  · exact ⟨0, by simp [he]⟩
  obtain ⟨x0, hx0, hCx0⟩ := hS z0 hz0
  have hz0ne : z0 ≠ 0 := fun h => h0 (h ▸ hz0)
  set v := C x0 with hv
  have hvne : v ≠ 0 := by rw [hCx0]; exact mul_ne_zero hz0ne hx0
  have hvr : (⟨v, LinearMap.mem_range_self C x0⟩ : LinearMap.range C) ≠ 0 := by
    intro h; apply hvne; exact congrArg Subtype.val h
  have hpos : 0 < Module.finrank E (LinearMap.range C) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hvr⟩
  have h1 : Module.finrank E (LinearMap.range C) = 1 := by omega
  have hall := (finrank_eq_one_iff_of_nonzero' _ hvr).mp h1
  have hmem : ∀ y, C y ∈ Submodule.span E {v} := by
    intro y
    obtain ⟨c, hc⟩ := hall ⟨C y, LinearMap.mem_range_self C y⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by have := congrArg Subtype.val hc; simpa using this⟩
  let φ : K →ₗ[E] E := (LinearEquiv.toSpanNonzeroSingleton E K v hvne).symm.toLinearMap ∘ₗ
    C.codRestrict (Submodule.span E {v}) hmem
  have hφ : ∀ y, φ y • v = C y := by
    intro y
    have h3 := congrArg Subtype.val ((LinearEquiv.toSpanNonzeroSingleton E K v hvne).apply_symm_apply
      (C.codRestrict (Submodule.span E {v}) hmem y))
    rw [LinearEquiv.toSpanNonzeroSingleton_apply] at h3
    exact h3
  refine ⟨φ ∘ₗ LinearMap.mulLeft E v, ?_⟩
  rintro t ⟨z, hz, rfl⟩
  obtain ⟨x, hx, hCx⟩ := hS z hz
  have hzne : z ≠ 0 := fun h => h0 (h ▸ hz)
  have e1 : φ x • v = z * x := by rw [hφ, hCx]
  have hφx : φ x ≠ 0 := by
    intro h; rw [h, zero_smul] at e1
    exact mul_ne_zero hzne hx e1.symm
  have e2 : x = φ x • (v * z⁻¹) := by
    rw [← smul_mul_assoc, e1]; field_simp
  have e3 : φ x = φ x * φ (v * z⁻¹) := by
    conv_lhs => rw [e2]
    rw [map_smul, smul_eq_mul]
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  have := mul_left_cancel₀ hφx (e3.symm.trans (mul_one _).symm)
  exact this

theorem bwd {E K : Type} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K) (h0 : (0 : K) ∉ S) (ψ : K →ₗ[E] E)
    (hψ : ∀ t ∈ (fun z : K => z⁻¹) '' (↑S : Set K), ψ t = 1) :
    ∃ C : K →ₗ[E] K, Module.finrank E (LinearMap.range C) ≤ 1 ∧
      ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x := by
  refine ⟨ψ.smulRight (1 : K), ?_, ?_⟩
  · have hle : LinearMap.range (ψ.smulRight (1 : K)) ≤ Submodule.span E {(1 : K)} := by
      rintro _ ⟨y, rfl⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨ψ y, rfl⟩
    exact le_trans (Submodule.finrank_mono hle) (le_of_eq (finrank_span_singleton one_ne_zero))
  · intro z hz
    have hzne : z ≠ 0 := fun h => h0 (h ▸ hz)
    refine ⟨z⁻¹, inv_ne_zero hzne, ?_⟩
    rw [LinearMap.smulRight_apply, hψ _ ⟨z, hz, rfl⟩, one_smul, mul_inv_cancel₀ hzne]

end PEqualNP.Outside.L_lib_747_aux

theorem PEqualNP.Outside.L_lib_747 : ∀ (E K : Type) [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K), (0 : K) ∉ S →
  ((∃ C : K →ₗ[E] K, Module.finrank E (LinearMap.range C) ≤ 1 ∧
    ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x) ↔
    (0 : K) ∉ affineSpan E (Set.image (fun z : K => z⁻¹) (↑S : Set K))) := by
  intro E K _ _ _ _ S h0
  constructor
  · rintro ⟨C, hC, hS⟩
    obtain ⟨ψ, hψ⟩ := PEqualNP.Outside.L_lib_747_aux.fwd S C hC hS h0
    exact PEqualNP.Outside.L_lib_747_aux.L1 _ ψ hψ
  · intro h
    obtain ⟨ψ, hψ⟩ := PEqualNP.Outside.L_lib_747_aux.L2 _ h
    exact PEqualNP.Outside.L_lib_747_aux.bwd S h0 ψ hψ
