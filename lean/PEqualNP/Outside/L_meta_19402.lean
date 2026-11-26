import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19402
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and2 (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem leftRead {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [Fin.ext_iff]

theorem rightRead {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD (n+i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp [Fin.ext_iff]

structure Stage (n : ℕ) where
  gs : List Gate
  ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Read {n : ℕ} (p : Stage n) (f : Fin n → Fin n → Bool) : Prop :=
  ∃ i : ℕ, i < n + n + p.gs.length ∧ ∀ u v,
    (run p.gs (oneEach u v)).getD i false = f u v

theorem read_congr {n : ℕ} {p : Stage n} {f g : Fin n → Fin n → Bool}
    (h : Read p f) (e : ∀ u v, f u v = g u v) : Read p g := by
  obtain ⟨i, hi, hv⟩ := h
  exact ⟨i,hi,fun u v => (hv u v).trans (e u v)⟩

theorem rowBit {n : ℕ} (p : Stage n) (i : ℕ) (hi : i < n) :
    Read p (fun u v => decide (i = u.val)) := by
  refine ⟨i, by omega, fun u v => ?_⟩
  rw [getD_run _ _ _ (by simp [oneEach]; omega),leftRead u v i hi]

theorem colBit {n : ℕ} (p : Stage n) (i : ℕ) (hi : i < n) :
    Read p (fun u v => decide (i = v.val)) := by
  refine ⟨n+i,by omega, fun u v => ?_⟩
  rw [getD_run _ _ _ (by simp [oneEach]; omega),rightRead u v i hi]

def Keeps {n : ℕ} (p q : Stage n) : Prop := ∀ f, Read p f → Read q f

theorem emit {n : ℕ} {p : Stage n} {f g : Fin n → Fin n → Bool} (op : GateOp)
    (hc : op = .and ∨ op = .or) (comb : Bool → Bool → Bool)
    (hev : ∀ a b, op.eval [a,b] = comb a b) (hf : Read p f) (hg : Read p g) :
    ∃ q : Stage n, q.gs.length = p.gs.length + 1 ∧ Keeps p q ∧
      Read q (fun u v => comb (f u v) (g u v)) := by
  obtain ⟨i,hi,hvi⟩ := hf
  obtain ⟨j,hj,hvj⟩ := hg
  let gate : Gate := ⟨op,[i,j]⟩
  let q : Stage n := ⟨p.gs ++ [gate], by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact p.ok _ ht
    · have et := List.mem_singleton.mp ht
      subst t
      rcases hc with rfl | rfl <;> simp [gate]⟩
  have lens (u v : Fin n) : (run p.gs (oneEach u v)).length = n + n + p.gs.length := by
    simp [run_length,oneEach]
  refine ⟨q,by simp [q], ?_, ?_⟩
  · intro f h
    obtain ⟨o,ho,hvo⟩ := h
    refine ⟨o,by simp [q]; omega,fun u v => ?_⟩
    change (run (p.gs ++ [gate]) (oneEach u v)).getD o false = _
    rw [run_append, getD_run _ _ _ (by rw [lens]; exact ho),hvo]
  · refine ⟨n+n+p.gs.length,by simp [q],fun u v => ?_⟩
    change (run (p.gs ++ [gate]) (oneEach u v)).getD (n+n+p.gs.length) false = _
    rw [run_append, run_singleton, ← lens u v, getD_snoc_length]
    simp only [gate,List.map_cons,List.map_nil,hev,hvi,hvj]

theorem addOr {n : ℕ} {p : Stage n} {f g : Fin n → Fin n → Bool} (hf : Read p f) (hg : Read p g) :
    ∃ q : Stage n, q.gs.length = p.gs.length + 1 ∧ Keeps p q ∧
      Read q (fun u v => f u v || g u v) :=
  emit .or (.inr rfl) (· || ·) eval_or2 hf hg

theorem addAnd {n : ℕ} {p : Stage n} {f g : Fin n → Fin n → Bool} (hf : Read p f) (hg : Read p g) :
    ∃ q : Stage n, q.gs.length = p.gs.length + 1 ∧ Keeps p q ∧
      Read q (fun u v => f u v && g u v) :=
  emit .and (.inl rfl) (· && ·) eval_and2 hf hg

theorem interval {n : ℕ} (p : Stage n) (val : Fin n → Fin n → ℕ)
    (var : ∀ i, i < n → Read p (fun u v => decide (i = val u v))) (start count : ℕ)
    (hx : start + count < n) : ∃ q : Stage n, q.gs.length = p.gs.length + count ∧
      Keeps p q ∧ Read q (fun u v => decide (start ≤ val u v ∧ val u v ≤ start + count)) := by
  induction count with
  | zero =>
    refine ⟨p,by simp, fun _ h => h, read_congr (var start (by omega)) ?_⟩
    intro u v
    rw [decide_eq_decide]
    omega
  | succ k ih =>
    obtain ⟨q,hq,keep,signal⟩ := ih (by omega)
    obtain ⟨r,hr,keep',signal'⟩ := addOr signal (keep _ (var (start+k+1) (by omega)))
    refine ⟨r,by omega,fun f h => keep' _ (keep f h), read_congr signal' ?_⟩
    intro u v
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    omega

theorem finish {n b : ℕ} {p : Stage n} {f : Fin n → Fin n → Bool} (h : Read p f)
    (hl : p.gs.length ≤ b) : RepSizeAtMost f b := by
  obtain ⟨o,_,ev⟩ := h
  exact ⟨⟨p.gs,o⟩,p.ok,hl,ev⟩

end PEqualNP.Outside.L_meta_19402

open PEqualNP.Outside.L_meta_19402 PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_19402 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) (2 * n + 1) := by
  intro n hn
  let p0 : Stage n := ⟨[], by simp⟩
  have h0 : p0.gs.length = 0 := rfl
  obtain ⟨p1,h1,k1,r⟩ := interval p0 (fun u _ => u.val) (rowBit p0) 2 (n-3) (by omega)
  obtain ⟨p2,h2,k2,c⟩ := interval p1 (fun _ v => v.val) (colBit p1) 3 (n-4) (by omega)
  obtain ⟨p3,h3,k3,x⟩ := addOr (colBit p2 1 (by omega)) (colBit p2 2 (by omega))
  obtain ⟨p4,h4,k4,y⟩ := addOr (colBit p3 0 (by omega)) (k3 _ (c))
  obtain ⟨p5,h5,k5,j⟩ := addOr (colBit p4 0 (by omega)) (k4 _ (x))
  obtain ⟨p6,h6,k6,t⟩ := addAnd (rowBit p5 0 (by omega)) (k5 _ (k4 _ (x)))
  obtain ⟨p7,h7,k7,m⟩ := addAnd (rowBit p6 1 (by omega)) (k6 _ (k5 _ (y)))
  obtain ⟨p8,h8,k8,q⟩ := addAnd (k7 _ (k6 _ (k5 _ (k4 _ (k3 _ (k2 _ (r))))))) (k7 _ (k6 _ (j)))
  obtain ⟨p9,h9,k9,o⟩ := addOr (k8 _ (k7 _ (t))) (k8 _ (m))
  obtain ⟨p10,h10,k10,z⟩ := addOr (o) (k9 _ (q))
  apply finish (p := p10) (read_congr z ?_) (by omega)
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  omega
