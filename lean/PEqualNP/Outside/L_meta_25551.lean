import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_25551_aux

open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def V (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

lemma V_input (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    V C x w = x.getD w false :=
  wiresFrom_getD_lt C.gates x w hw

lemma V_big (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    V C x w = false := by
  show (wiresFrom C.gates x).getD w false = false
  apply List.getD_eq_default
  rw [wiresFrom_length]
  omega

lemma V_gate (C : Circuit) (x : List Bool) (raw j : ℕ) (hx : x.length = raw)
    (hrb : ReadsBack raw C) (hj : j < C.gates.length) :
    V C x (raw + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (fun i => V C x i)) := by
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD, List.getElem?_eq_getElem hj]
  have hWlen : (wiresFrom (C.gates.take j) x).length = raw + j := by
    rw [wiresFrom_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hall : ∀ i, i < raw + j + 1 → V C x i =
      (wiresFrom (C.gates.take j) x ++ [C.gates[j].op.eval (C.gates[j].inputs.map
        fun i => (wiresFrom (C.gates.take j) x).getD i false)]).getD i false := by
    intro i hi
    show (wiresFrom C.gates x).getD i false = _
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_getD_lt]
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hall (raw + j) (by omega), getD_snoc_eq _ _ _ _ hWlen.symm, hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hrb j hj i (by rw [hgate]; exact hi)
  rw [hall i (by omega), getD_snoc_lt _ _ _ _ (by omega)]

lemma outside_agree (C : Circuit) (raw top : ℕ) (src region : Finset ℕ)
    (x1 x2 : List Bool) (h1 : x1.length = raw) (h2 : x2.length = raw)
    (hrb : ReadsBack raw C)
    (hout : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ src ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top))
    (hx : ∀ i < raw, i ∉ src → x1.getD i false = x2.getD i false)
    (T : Prop) (hT : T → V C x1 (raw + top) = V C x2 (raw + top)) :
    ∀ w, w ∉ src → ¬ (raw ≤ w ∧ w - raw ∈ region) → (w < raw + top ∨ T) →
      V C x1 w = V C x2 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hs hi hc
  by_cases hw : w < raw
  · rw [V_input C x1 w (by omega), V_input C x2 w (by omega)]
    exact hx w hw hs
  by_cases hw2 : raw + C.gates.length ≤ w
  · rw [V_big C x1 w (by omega), V_big C x2 w (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, w = raw + j := ⟨w - raw, by omega⟩
  have hj : j < C.gates.length := by omega
  have hjr : j ∉ region := fun h => hi ⟨by omega, by simpa using h⟩
  rw [V_gate C x1 raw j h1 hrb hj, V_gate C x2 raw j h2 hrb hj]
  congr 1
  apply List.map_congr_left
  intro i hii
  have hlt := hrb j hj i hii
  obtain ⟨his, hiin⟩ := hout j hj hjr i hii
  by_cases hI : (raw ≤ i ∧ i - raw ∈ region)
  · have := hiin hI
    subst this
    rcases hc with hc | hc
    · omega
    · exact hT hc
  · refine ih i hlt his hI ?_
    rcases hc with hc | hc
    · left; omega
    · right; exact hc

lemma inside_mono (C : Circuit) (raw : ℕ) (src entry region : Finset ℕ)
    (x1 x2 : List Bool) (h1 : x1.length = raw) (h2 : x2.length = raw)
    (hrb : ReadsBack raw C) (hreg : region ⊆ Finset.range C.size)
    (hgates : ∀ k ∈ region,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ src ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry)
    (hsrc : ∀ w ∈ src, V C x1 w = true → V C x2 w = true)
    (hent : ∀ w ∈ entry, V C x1 w = true → V C x2 w = true) :
    ∀ w, (raw ≤ w ∧ w - raw ∈ region) → V C x1 w = true → V C x2 w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hI
  obtain ⟨j, rfl⟩ : ∃ j, w = raw + j := ⟨w - raw, by omega⟩
  have hjr : j ∈ region := by simpa using hI.2
  have hj : j < C.gates.length := by
    have := hreg hjr
    simpa [Circuit.size] using this
  have hinp : ∀ i ∈ (gateAt C j).inputs, V C x1 i = true → V C x2 i = true := by
    intro i hi
    rcases (hgates j hjr).2 i hi with h | h | h
    · exact hsrc i h
    · exact ih i (hrb j hj i hi) h
    · exact hent i h
  rw [V_gate C x1 raw j h1 hrb hj, V_gate C x2 raw j h2 hrb hj]
  rcases (hgates j hjr).1 with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro h b ⟨i, hi, rfl⟩
    exact hinp i hi (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hinp i hi hb⟩

def Sc {β : Type*} [Fintype β] [DecidableEq β] (Q : Finset β) (ent0 : β → Bool) (c : Bool) :
    Finset β :=
  Finset.univ.filter (fun b => b ∉ Q ∧ ent0 b = c)

noncomputable def pickT {β : Type*} [Fintype β] [DecidableEq β] (Q : Finset β)
    (ent0 : β → Bool) (t : β → Bool) (c : Bool) : Bool :=
  if h : (Sc Q ent0 c).Nonempty then t h.choose
  else if h' : (Sc Q ent0 (!c)).Nonempty then t h'.choose else false

lemma core {α β : Type*} [Fintype β] [DecidableEq β] (P : Finset α) (Q : Finset β) (d e : ℕ)
    (G' top ent : α → β → Bool)
    (hdist : ∀ a1 ∈ P, ∀ a2 ∈ P, a1 ≠ a2 →
      d ≤ (Finset.univ.filter fun b => G' a1 b ≠ G' a2 b).card)
    (hQ : Q.card < d)
    (hent : ∀ a1 ∈ P, ∀ a2 ∈ P, ∀ b, b ∉ Q → ent a1 b = ent a2 b)
    (hG : ∀ a1 ∈ P, ∀ a2 ∈ P, ∀ b, b ∉ Q → top a1 b = top a2 b → G' a1 b = G' a2 b)
    (hmono : ∀ a ∈ P, ∀ b, b ∉ Q → ∀ b', b' ∉ Q →
      (ent a b = true → ent a b' = true) → top a b = true → top a b' = true)
    (he : e = 0 → ∀ a ∈ P, ∀ b, b ∉ Q → ent a b = false) :
    P.card ≤ 2 + e := by
  rcases P.eq_empty_or_nonempty with hP | ⟨a0, ha0⟩
  · simp [hP]
  let p : α → Bool × Bool := fun a =>
    (pickT Q (ent a0) (top a) false, pickT Q (ent a0) (top a) true)
  have key : ∀ a ∈ P, ∀ b, b ∉ Q → top a b = pickT Q (ent a0) (top a) (ent a0 b) := by
    intro a ha b hb
    have hne : (Sc Q (ent a0) (ent a0 b)).Nonempty := ⟨b, by simp [Sc, hb]⟩
    rw [pickT, dif_pos hne]
    have hc := (Finset.mem_filter.mp hne.choose_spec).2
    have e1 : ent a b = ent a hne.choose := by
      rw [hent a ha a0 ha0 b hb, hent a ha a0 ha0 _ hc.1, hc.2]
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hmono a ha b hb _ hc.1 (fun h => by rwa [← e1])
    · exact hmono a ha _ hc.1 b hb (fun h => by rwa [e1])
  have hinj : Set.InjOn p P := by
    intro a1 ha1 a2 ha2 hp
    by_contra hne
    have hd := hdist a1 ha1 a2 ha2 hne
    have hsub : (Finset.univ.filter fun b => G' a1 b ≠ G' a2 b) ⊆ Q := by
      intro b hb
      by_contra hbQ
      have hb' := (Finset.mem_filter.mp hb).2
      apply hb'
      apply hG a1 ha1 a2 ha2 b hbQ
      rw [key a1 ha1 b hbQ, key a2 ha2 b hbQ]
      have h1 : pickT Q (ent a0) (top a1) false = pickT Q (ent a0) (top a2) false :=
        congrArg Prod.fst hp
      have h2 : pickT Q (ent a0) (top a1) true = pickT Q (ent a0) (top a2) true :=
        congrArg Prod.snd hp
      cases ent a0 b
      · exact h1
      · exact h2
    have := Finset.card_le_card hsub
    omega
  have himg : ∀ a ∈ P, p a ∈ Finset.univ.filter
      (fun q : Bool × Bool => q ≠ (true, false) ∧ (e = 0 → q.1 = q.2)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      have hf : pickT Q (ent a0) (top a) false = true := congrArg Prod.fst hq
      have ht : pickT Q (ent a0) (top a) true = false := congrArg Prod.snd hq
      rw [pickT] at hf ht
      by_cases h0 : (Sc Q (ent a0) false).Nonempty
      · by_cases h1 : (Sc Q (ent a0) true).Nonempty
        · rw [dif_pos h0] at hf
          rw [dif_pos h1] at ht
          have c0 := (Finset.mem_filter.mp h0.choose_spec).2
          have c1 := (Finset.mem_filter.mp h1.choose_spec).2
          have := hmono a ha _ c0.1 _ c1.1 (fun _ => by
            rw [hent a ha a0 ha0 _ c1.1, c1.2]) hf
          rw [this] at ht
          exact absurd ht (by simp)
        · rw [dif_pos h0] at hf
          rw [dif_neg h1] at ht
          simp only [Bool.not_true, dif_pos h0] at ht
          rw [hf] at ht
          exact absurd ht (by simp)
      · rw [dif_neg h0] at hf
        by_cases h1 : (Sc Q (ent a0) true).Nonempty
        · simp only [Bool.not_false, dif_pos h1] at hf
          rw [dif_pos h1] at ht
          rw [hf] at ht
          exact absurd ht (by simp)
        · simp only [Bool.not_false, dif_neg h1] at hf
          exact absurd hf (by simp)
    · intro he0
      have hS1 : ¬ (Sc Q (ent a0) true).Nonempty := by
        rintro ⟨b, hb⟩
        have hb' := (Finset.mem_filter.mp hb).2
        have := he he0 a0 ha0 b hb'.1
        rw [hb'.2] at this
        exact absurd this (by simp)
      show pickT Q (ent a0) (top a) false = pickT Q (ent a0) (top a) true
      rw [pickT, pickT, dif_neg hS1]
      simp only [Bool.not_false, Bool.not_true, dif_neg hS1]
  calc P.card ≤ (Finset.univ.filter
        (fun q : Bool × Bool => q ≠ (true, false) ∧ (e = 0 → q.1 = q.2))).card :=
        Finset.card_le_card_of_injOn p (fun a ha => himg a ha) hinj
    _ ≤ 2 + e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h
          decide
        · have hfe : (Finset.univ.filter
              (fun q : Bool × Bool => q ≠ (true, false) ∧ (e = 0 → q.1 = q.2))) =
              Finset.univ.filter (fun q : Bool × Bool => q ≠ (true, false)) := by
            ext q
            simp [show e ≠ 0 by omega]
          rw [hfe]
          have : (Finset.univ.filter (fun q : Bool × Bool => q ≠ (true, false))).card = 3 := by
            decide
          omega

open PEqualNP.Represents (oneEach Represents)

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false =
      if i < n then decide (i = u.val) else if i < n + m then decide (i - n = v.val) else false := by
  unfold oneEach
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1)]
    simp [h1, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getElem?_ofFn]
    simp [show i - n < m by omega, Fin.ext_iff]
  · apply List.getD_eq_default
    simp
    omega

lemma off_src {n m : ℕ} (R : Finset (Fin n)) (B : Finset (Fin m)) (u1 u2 : Fin n) (v1 v2 : Fin m)
    (hu : u1 = u2 ∨ (u1 ∈ R ∧ u2 ∈ R)) (hv : v1 = v2 ∨ (v1 ∈ B ∧ v2 ∈ B)) :
    ∀ i < n + m, i ∉ (R.image (fun r => r.val) ∪ B.image (fun c => n + c.val)) →
      (oneEach u1 v1).getD i false = (oneEach u2 v2).getD i false := by
  intro i hi hs
  rw [oneEach_getD, oneEach_getD]
  simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hs
  split_ifs with h1 h2
  · rcases hu with rfl | ⟨hu1, hu2⟩
    · rfl
    · have a1 : i ≠ u1.val := fun h => hs.1 u1 hu1 h.symm
      have a2 : i ≠ u2.val := fun h => hs.1 u2 hu2 h.symm
      simp [a1, a2]
  · rcases hv with rfl | ⟨hv1, hv2⟩
    · rfl
    · have a1 : i - n ≠ v1.val := fun h => hs.2 v1 hv1 (by omega)
      have a2 : i - n ≠ v2.val := fun h => hs.2 v2 hv2 (by omega)
      simp [a1, a2]

lemma on_src {n m : ℕ} (R : Finset (Fin n)) (B : Finset (Fin m)) (u1 u2 : Fin n) (v1 v2 : Fin m)
    (hu : u1 = u2 ∨ (u1 ∉ R ∧ u2 ∉ R)) (hv : v1 = v2 ∨ (v1 ∉ B ∧ v2 ∉ B)) :
    ∀ i ∈ (R.image (fun r => r.val) ∪ B.image (fun c => n + c.val)),
      (oneEach u1 v1).getD i false = (oneEach u2 v2).getD i false := by
  intro i hs
  simp only [Finset.mem_union, Finset.mem_image] at hs
  rw [oneEach_getD, oneEach_getD]
  rcases hs with ⟨r, hr, rfl⟩ | ⟨c, hc, rfl⟩
  · simp only [r.isLt, if_true]
    rcases hu with rfl | ⟨hu1, hu2⟩
    · rfl
    · have a1 : r.val ≠ u1.val := fun h => hu1 (Fin.ext h ▸ hr)
      have a2 : r.val ≠ u2.val := fun h => hu2 (Fin.ext h ▸ hr)
      simp [a1, a2]
  · have h1 : ¬ (n + c.val < n) := by omega
    have h2 : n + c.val < n + m := by omega
    simp only [h1, h2, if_false, if_true, Nat.add_sub_cancel_left]
    rcases hv with rfl | ⟨hv1, hv2⟩
    · rfl
    · have a1 : c.val ≠ v1.val := fun h => hv1 (Fin.ext h ▸ hc)
      have a2 : c.val ≠ v2.val := fun h => hv2 (Fin.ext h ▸ hc)
      simp [a1, a2]

theorem main (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ)
    (src : Finset ℕ) (hsrc : src = R.image (fun r => r.val) ∪ B.image (fun c => n + c.val))
    (hrow : ∀ firstRow secondRow : Fin n, firstRow ≠ secondRow →
      d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card)
    (hcol : ∀ firstCol secondCol : Fin m, firstCol ≠ secondCol →
      d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card)
    (hrb : ReadsBack (n + m) C) (hrep : Represents G C) (hreg : region ⊆ Finset.range C.size)
    (htop : top ∈ region) (hecard : entry.card ≤ 1)
    (hentry : ∀ w ∈ entry, w < n + m + top ∧ w ∉ src ∧ ¬ (n + m ≤ w ∧ w - (n + m) ∈ region))
    (hgates : ∀ k ∈ region,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ src ∨ (n + m ≤ w ∧ w - (n + m) ∈ region) ∨ w ∈ entry)
    (hout : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ src ∧ ((n + m ≤ w ∧ w - (n + m) ∈ region) → w = n + m + top))
    (houtput : C.output ∉ src)
    (hout2 : (n + m ≤ C.output ∧ C.output - (n + m) ∈ region) → C.output = n + m + top) :
    (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  have hsrclt : ∀ i ∈ src, i < n + m := by
    intro i hi
    rw [hsrc] at hi
    simp only [Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨r, -, rfl⟩ | ⟨c, -, rfl⟩ <;> omega

  have F1 : ∀ x1 x2 : List Bool, x1.length = n + m → x2.length = n + m →
      (∀ i < n + m, i ∉ src → x1.getD i false = x2.getD i false) →
      ∀ w ∈ entry, V C x1 w = V C x2 w := by
    intro x1 x2 h1 h2 hx w hw
    obtain ⟨hw1, hw2, hw3⟩ := hentry w hw
    exact outside_agree C (n + m) top src region x1 x2 h1 h2 hrb hout hx False
      (fun h => h.elim) w hw2 hw3 (Or.inl hw1)

  have F2 : ∀ x1 x2 : List Bool, x1.length = n + m → x2.length = n + m →
      (∀ i < n + m, i ∉ src → x1.getD i false = x2.getD i false) →
      V C x1 (n + m + top) = V C x2 (n + m + top) → C.eval x1 = C.eval x2 := by
    intro x1 x2 h1 h2 hx ht
    show V C x1 C.output = V C x2 C.output
    by_cases hI : (n + m ≤ C.output ∧ C.output - (n + m) ∈ region)
    · rw [hout2 hI]
      exact ht
    · exact outside_agree C (n + m) top src region x1 x2 h1 h2 hrb hout hx True
        (fun _ => ht) C.output houtput hI (Or.inr trivial)
  let ent' : Fin n → Fin m → Bool := fun u v => decide (∃ w ∈ entry, V C (oneEach u v) w = true)
  let topv : Fin n → Fin m → Bool := fun u v => V C (oneEach u v) (n + m + top)
  have htopin : n + m ≤ n + m + top ∧ n + m + top - (n + m) ∈ region :=
    ⟨by omega, by simpa using htop⟩

  have F3 : ∀ u1 u2 : Fin n, ∀ v1 v2 : Fin m,
      (∀ i ∈ src, (oneEach u1 v1).getD i false = (oneEach u2 v2).getD i false) →
      (ent' u1 v1 = true → ent' u2 v2 = true) → topv u1 v1 = true → topv u2 v2 = true := by
    intro u1 u2 v1 v2 hx he ht
    refine inside_mono C (n + m) src entry region (oneEach u1 v1) (oneEach u2 v2)
      (oneEach_length _ _) (oneEach_length _ _) hrb hreg hgates ?_ ?_ (n + m + top) htopin ht
    · intro w hw h
      rw [V_input C _ w (by rw [oneEach_length]; exact hsrclt w hw)] at h ⊢
      rw [← hx w hw]
      exact h
    · intro w hw h
      have h1 : ent' u1 v1 = true := decide_eq_true ⟨w, hw, h⟩
      obtain ⟨w', hw', h'⟩ := of_decide_eq_true (he h1)
      have := Finset.card_le_one.mp hecard w hw w' hw'
      subst this
      exact h'
  have F1' : ∀ u1 u2 : Fin n, ∀ v1 v2 : Fin m,
      (∀ i < n + m, i ∉ src → (oneEach u1 v1).getD i false = (oneEach u2 v2).getD i false) →
      ent' u1 v1 = ent' u2 v2 := by
    intro u1 u2 v1 v2 hx
    have := F1 _ _ (oneEach_length _ _) (oneEach_length _ _) hx
    apply Bool.eq_iff_iff.mpr
    simp only [ent', decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, by rw [← this w hw]; exact h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, by rw [this w hw]; exact h⟩
  have he0 : entry.card = 0 → ∀ u v, ent' u v = false := by
    intro h u v
    have : entry = ∅ := Finset.card_eq_zero.mp h
    simp [ent', this]
  constructor
  · intro hB
    refine core R B d entry.card G topv ent' (fun a1 _ a2 _ h => hrow a1 a2 h) hB ?_ ?_ ?_ ?_
    · intro a1 ha1 a2 ha2 b hb
      exact F1' a1 a2 b b (by rw [hsrc]; exact off_src R B a1 a2 b b (Or.inr ⟨ha1, ha2⟩) (Or.inl rfl))
    · intro a1 ha1 a2 ha2 b hb ht
      rw [← hrep a1 b, ← hrep a2 b]
      exact F2 _ _ (oneEach_length _ _) (oneEach_length _ _)
        (by rw [hsrc]; exact off_src R B a1 a2 b b (Or.inr ⟨ha1, ha2⟩) (Or.inl rfl)) ht
    · intro a ha b hb b' hb' he ht
      exact F3 a a b b' (by rw [hsrc]; exact on_src R B a a b b' (Or.inl rfl) (Or.inr ⟨hb, hb'⟩))
        he ht
    · intro h a _ b _
      exact he0 h a b
  · intro hR
    refine core B R d entry.card (fun c r => G r c) (fun c r => topv r c) (fun c r => ent' r c)
      (fun a1 _ a2 _ h => hcol a1 a2 h) hR ?_ ?_ ?_ ?_
    · intro a1 ha1 a2 ha2 b hb
      exact F1' b b a1 a2 (by rw [hsrc]; exact off_src R B b b a1 a2 (Or.inl rfl) (Or.inr ⟨ha1, ha2⟩))
    · intro a1 ha1 a2 ha2 b hb ht
      show G b a1 = G b a2
      rw [← hrep b a1, ← hrep b a2]
      exact F2 _ _ (oneEach_length _ _) (oneEach_length _ _)
        (by rw [hsrc]; exact off_src R B b b a1 a2 (Or.inl rfl) (Or.inr ⟨ha1, ha2⟩)) ht
    · intro a ha b hb b' hb' he ht
      exact F3 b b' a a (by rw [hsrc]; exact on_src R B b b' a a (Or.inr ⟨hb, hb'⟩) (Or.inl rfl))
        he ht
    · intro h a _ b _
      exact he0 h b a

end PEqualNP.Outside.L_meta_25551_aux

theorem PEqualNP.Outside.L_meta_25551 : (∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)) := by
  intro n m d G C R B region entry top raw sources inside gate hrow hcol hrb hrep hreg htop hecard hentry hgates hout houtput hout2
  exact PEqualNP.Outside.L_meta_25551_aux.main n m d G C R B region entry top sources rfl hrow hcol hrb hrep hreg htop hecard hentry hgates hout houtput hout2
