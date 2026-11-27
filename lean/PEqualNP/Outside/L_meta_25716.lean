import Mathlib

namespace PEqualNP.Outside.L_meta_25716_aux

variable {k : ℕ} [NeZero k]

def rot (s : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 := w (i - (s : ZMod k))

def mix (d : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  w (i - (d : ZMod k)) + w i + w (i + (d : ZMod k))

def out (d u v : ℕ) (name c x : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  mix d (rot u x + name) j + (1 + mix d (rot u x + name) (j+1)) * mix d (rot u x + name) (j+2) +
    rot v x j + c j

def test (d u v : ℕ) (z : ZMod k → ZMod 2) (j : ZMod k) : Prop :=
  mix d (rot u z) j = rot v z j ∧ ((k = 1 ∨ k = 3) ∨
    (mix d (rot u z) (j+1) = 0 ∧ mix d (rot u z) (j+2) = 0))

theorem mix_add (d : ℕ) (a b : ZMod k → ZMod 2) (i : ZMod k) :
    mix d (a + b) i = mix d a i + mix d b i := by
  simp only [mix, Pi.add_apply]; ring

theorem rot_add (s : ℕ) (a b : ZMod k → ZMod 2) : rot s (a + b) = rot s a + rot s b := by
  funext i; simp [rot]

theorem expand (d u v : ℕ) (name c x z : ZMod k → ZMod 2) (j : ZMod k) :
    out d u v name c (x + z) j = out d u v name c x j +
      (mix d (rot u z) j + rot v z j +
        (1 + mix d (rot u x) (j+1) + mix d name (j+1)) * mix d (rot u z) (j+2) +
        mix d (rot u z) (j+1) * (mix d (rot u x) (j+2) + mix d name (j+2)) +
        mix d (rot u z) (j+1) * mix d (rot u z) (j+2)) := by
  simp only [out, rot_add, mix_add, Pi.add_apply]
  ring

theorem pos (d u v : ℕ) (name c z : ZMod k → ZMod 2) (j : ZMod k)
    (h13 : (k = 1 ∨ k = 3) → ∀ w : ZMod k → ZMod 2, mix d w (j+1) = mix d w (j+2))
    (hw : ¬ (k = 1 ∨ k = 3) → ∃ x, mix d (rot u x) (j+1) + mix d (rot u x) (j+2) = 1) :
    (∀ x, out d u v name c (x + z) j = out d u v name c x j) ↔ test d u v z j := by
  have h0 : ∀ i, mix d (rot u (0 : ZMod k → ZMod 2)) i = 0 := by intro i; simp [mix, rot]
  have h1 : ∀ i : ZMod k, mix d (rot u (fun _ : ZMod k => (1 : ZMod 2))) i = 1 := by intro i; simp [mix, rot]; decide
  simp only [expand, add_eq_left]
  unfold test
  by_cases hk : k = 1 ∨ k = 3
  · have e := h13 hk
    simp only [hk, true_or, and_true]
    rw [e (rot u z), e name]
    constructor
    · intro H
      have E := H 0
      rw [h0, h0] at E
      revert E
      generalize mix d (rot u z) j = A
      generalize rot v z j = R
      generalize mix d (rot u z) (j+2) = B
      generalize mix d name (j+2) = N
      revert A R B N
      decide
    · intro hAR x
      rw [e (rot u x)]
      revert hAR
      generalize mix d (rot u z) j = A
      generalize rot v z j = R
      generalize mix d (rot u z) (j+2) = B
      generalize mix d name (j+2) = N
      generalize mix d (rot u x) (j+2) = Y
      revert A R B N Y
      decide
  · obtain ⟨xw, hxw⟩ := hw hk
    simp only [hk, false_or]
    constructor
    · intro H
      have E0 := H 0
      have E1 := H (fun _ : ZMod k => 1)
      have Ed := H xw
      rw [h0, h0] at E0
      rw [h1, h1] at E1
      have s1 : mix d (rot u z) (j+2) + mix d (rot u z) (j+1) = 0 := by linear_combination E1 - E0
      have s2 : mix d (rot u xw) (j+1) * mix d (rot u z) (j+2) +
          mix d (rot u xw) (j+2) * mix d (rot u z) (j+1) = 0 := by linear_combination Ed - E0
      have alg : ∀ A1 A2 F1 F2 : ZMod 2, F1 + F2 = 1 → A2 + A1 = 0 → F1 * A2 + F2 * A1 = 0 →
          A1 = 0 ∧ A2 = 0 := by decide
      obtain ⟨hA1, hA2⟩ := alg _ _ _ _ hxw s1 s2
      refine ⟨?_, hA1, hA2⟩
      rw [hA1, hA2] at E0
      have alg2 : ∀ A R : ZMod 2, A + R = 0 → A = R := by decide
      exact alg2 _ _ (by linear_combination E0)
    · rintro ⟨hAR, hA1, hA2⟩ x
      rw [hA1, hA2, hAR]
      have hRR : ∀ R : ZMod 2, R + R = 0 := by decide
      simp [hRR]

theorem h13 (d : ℕ) (hd : d = 1 ∨ d = 2) (j : ZMod k) :
    (k = 1 ∨ k = 3) → ∀ w : ZMod k → ZMod 2, mix d w (j+1) = mix d w (j+2) := by
  rintro (rfl | rfl) w
  · have : (j + 1 : ZMod 1) = j + 2 := Subsingleton.elim _ _
    rw [this]
  · unfold mix
    rcases hd with rfl | rfl
    · have e1 : j + 1 - ((1:ℕ) : ZMod 3) = j + 2 + ((1:ℕ) : ZMod 3) := by revert j; decide
      have e2 : j + 1 + ((1:ℕ) : ZMod 3) = j + 2 := by revert j; decide
      have e3 : (j + 1 : ZMod 3) = j + 2 - ((1:ℕ) : ZMod 3) := by revert j; decide
      rw [e1, e2, e3]; ring
    · have e1 : j + 1 - ((2:ℕ) : ZMod 3) = j + 2 := by revert j; decide
      have e2 : j + 1 + ((2:ℕ) : ZMod 3) = j + 2 - ((2:ℕ) : ZMod 3) := by revert j; decide
      have e3 : (j + 1 : ZMod 3) = j + 2 + ((2:ℕ) : ZMod 3) := by revert j; decide
      rw [e1, e2, e3]; ring

theorem ne3 (hk : ¬ (k = 1 ∨ k = 3)) : (3 : ZMod k) ≠ 0 := by
  intro h
  have h' : ((3:ℕ) : ZMod k) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  rcases (Nat.dvd_prime Nat.prime_three).mp h' with h1 | h1
  · exact hk (Or.inl h1)
  · exact hk (Or.inr h1)

theorem w1 (j : ZMod k) : ¬ (k = 1 ∨ k = 3) →
    ∃ x, mix 1 (rot 1 x) (j+1) + mix 1 (rot 1 x) (j+2) = 1 := by
  intro hk
  refine ⟨fun q => if q - (j - ((1:ℕ) : ZMod k)) = 0 then 1 else 0, ?_⟩
  simp only [mix, rot]
  push_cast
  ring_nf
  have h3 := ne3 hk
  simp only [h3, if_false]
  generalize (if (1 : ZMod k) = 0 then (1 : ZMod 2) else 0) = B1
  generalize (if (2 : ZMod k) = 0 then (1 : ZMod 2) else 0) = B2
  revert B1 B2
  decide

theorem w2 (j : ZMod k) : ¬ (k = 1 ∨ k = 3) →
    ∃ x, mix 2 (rot 3 x) (j+1) + mix 2 (rot 3 x) (j+2) = 1 := by
  intro hk
  refine ⟨fun q => if q - (j - ((2:ℕ) : ZMod k)) = 0 then 1 else 0, ?_⟩
  simp only [mix, rot]
  push_cast
  ring_nf
  have h3 := ne3 hk
  simp only [h3, if_false, neg_eq_zero]
  generalize (if (1 : ZMod k) = 0 then (1 : ZMod 2) else 0) = B1
  generalize (if (2 : ZMod k) = 0 then (1 : ZMod 2) else 0) = B2
  revert B1 B2
  decide

theorem main (k : ℕ) [NeZero k] (row col cr cc z : ZMod k → ZMod 2) (S T : Finset (ZMod k)) :
    (∀ x : ZMod k → ZMod 2,
      (∀ j ∈ S, out 1 1 0 row cr (x+z) j = out 1 1 0 row cr x j) ∧
      (∀ i ∈ T, out 2 3 4 col cc (x+z) i = out 2 3 4 col cc x i)) ↔
    (∀ j ∈ S, test 1 1 0 z j) ∧ (∀ i ∈ T, test 2 3 4 z i) := by
  have P1 := fun j => pos 1 1 0 row cr z j (h13 1 (Or.inl rfl) j) (w1 j)
  have P2 := fun j => pos 2 3 4 col cc z j (h13 2 (Or.inr rfl) j) (w2 j)
  constructor
  · intro H
    exact ⟨fun j hj => (P1 j).mp (fun x => (H x).1 j hj), fun i hi => (P2 i).mp (fun x => (H x).2 i hi)⟩
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun j hj => (P1 j).mpr (h1 j hj) x, fun i hi => (P2 i).mpr (h2 i hi) x⟩

end PEqualNP.Outside.L_meta_25716_aux

theorem PEqualNP.Outside.L_meta_25716 : ∀ (k : ℕ) [NeZero k],
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let rot := fun (s : ℕ) (w : V) (i : I) => w (i-(s : I))
  let mix := fun (d : ℕ) (w : V) (i : I) => w (i-(d : I))+w i+w (i+(d : I))
  let out := fun (d u v : ℕ) (name c x : V) (j : I) =>
    let y := mix d (rot u x + name)
    y j + (1+y (j+1))*y (j+2) + rot v x j + c j
  let test := fun (d u v : ℕ) (z : V) (j : I) =>
    let a := mix d (rot u z)
    a j = rot v z j ∧ ((k = 1 ∨ k = 3) ∨ (a (j+1) = 0 ∧ a (j+2) = 0))
  ∀ (row col cr cc z : V) (S T : Finset I),
    (∀ x : V,
      (∀ j ∈ S, out 1 1 0 row cr (x+z) j = out 1 1 0 row cr x j) ∧
      (∀ i ∈ T, out 2 3 4 col cc (x+z) i = out 2 3 4 col cc x i)) ↔
    (∀ j ∈ S, test 1 1 0 z j) ∧ (∀ i ∈ T, test 2 3 4 z i) := by
  intro k _ I B V rot mix out test row col cr cc z S T
  exact PEqualNP.Outside.L_meta_25716_aux.main k row col cr cc z S T
