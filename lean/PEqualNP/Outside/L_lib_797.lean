import Mathlib

namespace PEqualNP.Outside.L_lib_797_aux

theorem rows (n m : Nat) (r u : Fin n) (c v : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool → Bool)
    (hru : r ≠ u) (hrS : r ∉ S) (huS : u ∉ S) (hvT : v ∉ T) (hH : H ∅ ∅ = false)
    (hD : D ∅ ∅ false true = false)
    (hmono : ∀ X X' Y Y' w w' z z', X ⊆ X' → Y ⊆ Y' → w ≤ w' → z ≤ z' →
      D X Y w z ≤ D X' Y' w' z')
    (A : Fin n → Fin m → Bool)
    (hA : ∀ i j, A i j = D (if i = r ∨ i = u ∨ i ∈ S then ∅ else {i})
      (if j = c ∨ j = v ∨ j ∈ T then ∅ else {j}) (decide (i = u ∨ j = v))
      (!(decide (i = u ∨ j = v) || H (if i ∈ S then {i} else ∅) (if j ∈ T then {j} else ∅)))) :
    ∀ i ∈ S, (∀ j, A i j = A r j) ∨ (∀ k j, A i j ≤ A k j) := by
  intro i hi
  have hiu : i ≠ u := fun h => huS (h ▸ hi)
  have hir : i ≠ r := fun h => hrS (h ▸ hi)
  have hidden : ∀ k, k ≠ u → (k = r ∨ k ∈ S) → ∀ j ∈ T, A k j = false := by
    intro k hk hkr j hj
    have hjv : j ≠ v := fun h => hvT (h ▸ hj)
    rw [hA]
    have e1 : (if k = r ∨ k = u ∨ k ∈ S then (∅ : Finset (Fin n)) else {k}) = ∅ := by
      rw [if_pos]; rcases hkr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have e2 : (if j = c ∨ j = v ∨ j ∈ T then (∅ : Finset (Fin m)) else {j}) = ∅ := by
      rw [if_pos (Or.inr (Or.inr hj))]
    have e3 : decide (k = u ∨ j = v) = false := by simp [hk, hjv]
    rw [e1, e2, e3]
    have hz : ∀ z, D ∅ ∅ false z = false := by
      intro z
      have := hmono ∅ ∅ ∅ ∅ false false z true (le_refl _) (le_refl _) (le_refl _) (Bool.le_true z)
      rw [hD] at this
      exact Bool.eq_false_iff.mpr (fun h => by rw [h] at this; exact absurd this (by decide))
    exact hz _
  have ei : (if i = r ∨ i = u ∨ i ∈ S then (∅ : Finset (Fin n)) else {i}) = ∅ :=
    if_pos (Or.inr (Or.inr hi))
  have er : (if r = r ∨ r = u ∨ r ∈ S then (∅ : Finset (Fin n)) else {r}) = ∅ := if_pos (Or.inl rfl)
  have hi' : (if i ∈ S then ({i} : Finset (Fin n)) else ∅) = {i} := if_pos hi
  have hr' : (if r ∈ S then ({r} : Finset (Fin n)) else ∅) = ∅ := if_neg hrS
  cases hHi : H {i} ∅
  · left
    intro j
    by_cases hj : j ∈ T
    · rw [hidden i hiu (Or.inr hi) j hj, hidden r hru (Or.inl rfl) j hj]
    · rw [hA, hA, ei, er, hi', hr', if_neg hj, hHi, hH]
      simp [hiu, hru]
  · right
    intro k j
    by_cases hj : j ∈ T
    · rw [hidden i hiu (Or.inr hi) j hj]; exact Bool.false_le _
    · rw [hA, hA, ei, hi', if_neg hj, hHi, Bool.or_true, Bool.not_true]
      apply hmono
      · exact Finset.empty_subset _
      · exact le_refl _
      · by_cases hjv : j = v
        · simp [hjv]
        · simp [hjv, hiu]
      · exact Bool.false_le _

theorem cols (n m : Nat) (r u : Fin n) (c v : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool → Bool)
    (hcv : c ≠ v) (hcT : c ∉ T) (hvT : v ∉ T) (huS : u ∉ S) (hH : H ∅ ∅ = false)
    (hD : D ∅ ∅ false true = false)
    (hmono : ∀ X X' Y Y' w w' z z', X ⊆ X' → Y ⊆ Y' → w ≤ w' → z ≤ z' →
      D X Y w z ≤ D X' Y' w' z')
    (A : Fin n → Fin m → Bool)
    (hA : ∀ i j, A i j = D (if i = r ∨ i = u ∨ i ∈ S then ∅ else {i})
      (if j = c ∨ j = v ∨ j ∈ T then ∅ else {j}) (decide (i = u ∨ j = v))
      (!(decide (i = u ∨ j = v) || H (if i ∈ S then {i} else ∅) (if j ∈ T then {j} else ∅)))) :
    ∀ j ∈ T, (∀ i, A i j = A i c) ∨ (∀ l i, A i j ≤ A i l) := by
  have := rows m n c v r u T S (fun Y X => H X Y) (fun Y X w z => D X Y w z) hcv hcT hvT huS hH hD
    (fun Y Y' X X' w w' z z' h1 h2 h3 h4 => hmono X X' Y Y' w w' z z' h2 h1 h3 h4)
    (fun j i => A i j) (by
      intro j i
      rw [hA]
      have e : decide (i = u ∨ j = v) = decide (j = v ∨ i = u) := by
        apply decide_eq_decide.mpr; exact or_comm
      rw [e])
  intro j hj
  rcases this j hj with h | h
  · exact Or.inl h
  · exact Or.inr (fun l i => h l i)

end PEqualNP.Outside.L_lib_797_aux

theorem PEqualNP.Outside.L_lib_797 : ∀ (n m : Nat) (r u : Fin n) (c v : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool → Bool),
  r ≠ u → c ≠ v → r ∉ S → u ∉ S → c ∉ T → v ∉ T → H ∅ ∅ = false →
  D ∅ ∅ false true = false →
  (∀ X X' Y Y' w w' z z', X ⊆ X' → Y ⊆ Y' → w ≤ w' → z ≤ z' →
    D X Y w z ≤ D X' Y' w' z') →
  let A := fun (i : Fin n) (j : Fin m) =>
    let w := decide (i = u ∨ j = v)
    D (if i = r ∨ i = u ∨ i ∈ S then ∅ else {i})
      (if j = c ∨ j = v ∨ j ∈ T then ∅ else {j}) w
      (!(w || H (if i ∈ S then {i} else ∅) (if j ∈ T then {j} else ∅)))
  (∀ i ∈ S, (∀ j, A i j = A r j) ∨ (∀ k j, A i j ≤ A k j)) ∧
    (∀ j ∈ T, (∀ i, A i j = A i c) ∨ (∀ l i, A i j ≤ A i l)) := by
  intro n m r u c v S T H D hru hcv hrS huS hcT hvT hH hD hmono A
  exact ⟨PEqualNP.Outside.L_lib_797_aux.rows n m r u c v S T H D hru hrS huS hvT hH hD hmono A
      (fun i j => rfl),
    PEqualNP.Outside.L_lib_797_aux.cols n m r u c v S T H D hcv hcT hvT huS hH hD hmono A
      (fun i j => rfl)⟩
