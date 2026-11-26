import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20792

abbrev Row := Fin 3 → Fin 3 → Bool

def pool : List Row :=
  [(fun _ _ => false), (fun _ _ => true),
   (fun u _ => decide (u = 0)), (fun u _ => decide (u = 1)), (fun u _ => decide (u = 2)),
   (fun _ v => decide (v = 0)), (fun _ v => decide (v = 1)), (fun _ v => decide (v = 2))]

def nextRows (B : List Row) : List Row :=
  B ++ B.map (fun a i j => !(a i j)) ++
    B.flatMap (fun a => B.flatMap (fun b =>
      [(fun i j => a i j && b i j), (fun i j => a i j || b i j)]))

def target (u v : Fin 3) : Bool := (30 : ℕ).testBit (4*u.val+v.val)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Bank := Fin 3 → Fin 3 → List Bool

def readCol (W : Bank) (i : ℕ) : Row := fun u v => (W u v).getD i false
def Covered (S : List Row) (W : Bank) : Prop := ∀ i, readCol W i ∈ S
def falseCol : Row := fun _ _ => false
def trueCol : Row := fun _ _ => true

theorem next_old {S : List Row} {t : Row} (ht : t ∈ S) : t ∈ nextRows S :=
  List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ht)))

theorem next_not {S : List Row} {a : Row} (h : a ∈ S) :
    (fun u v => !(a u v)) ∈ nextRows S :=
  List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_map.mpr ⟨a,h,rfl⟩))))

theorem next_and {S : List Row} {a b : Row} (ha : a ∈ S) (hb : b ∈ S) :
    (fun u v => a u v && b u v) ∈ nextRows S :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
    ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩))

theorem next_or {S : List Row} {a b : Row} (ha : a ∈ S) (hb : b ∈ S) :
    (fun u v => a u v || b u v) ∈ nextRows S :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
    ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩))

def gateRow (W : Bank) (g : Gate) : Row := fun u v =>
  g.op.eval (g.inputs.map fun i => readCol W i u v)

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem gate_mem {W : Bank} {S : List Row} (cov : Covered S W)
    (hz : falseCol ∈ S) (ho : trueCol ∈ S) (g : Gate) (hg : legal g) :
    gateRow W g ∈ nextRows S := by
  rcases g with ⟨op,ins⟩
  rcases hg with ⟨hop,hl⟩
  change op = .and ∨ op = .or ∨ op = .not at hop
  change ins.length ≤ 2 at hl
  cases ins with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact next_old ho
    · exact next_old hz
    · exact next_old ho
  | cons a tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · have h : gateRow W ⟨.and,[a]⟩ = readCol W a := by
          funext u v
          change (readCol W a u v && true) = _
          simp
        rw [h]
        exact next_old (cov a)
      · have h : gateRow W ⟨.or,[a]⟩ = readCol W a := by
          funext u v
          change (readCol W a u v || false) = _
          simp
        rw [h]
        exact next_old (cov a)
      · exact next_not (cov a)
    | cons b tail =>
      cases tail with
      | nil =>
        rcases hop with rfl | rfl | rfl
        · have h : gateRow W ⟨.and,[a,b]⟩ = (fun u v => readCol W a u v && readCol W b u v) := by
            funext u v
            change (readCol W a u v && (readCol W b u v && true)) = _
            simp
          rw [h]
          exact next_and (cov a) (cov b)
        · have h : gateRow W ⟨.or,[a,b]⟩ = (fun u v => readCol W a u v || readCol W b u v) := by
            funext u v
            change (readCol W a u v || (readCol W b u v || false)) = _
            simp
          rw [h]
          exact next_or (cov a) (cov b)
        · exact next_not (cov a)
      | cons c cs => simp at hl

def appendGate (W : Bank) (g : Gate) : Bank := fun u v => W u v ++ [gateRow W g u v]

theorem read_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem append_covered {W : Bank} {n : ℕ} {S : List Row} (cov : Covered S W)
    (sz : ∀ u v, (W u v).length = n) (hz : falseCol ∈ S) (g : Gate) :
    Covered (gateRow W g :: S) (appendGate W g) := by
  intro i
  by_cases hi : i < n
  · have eq : readCol (appendGate W g) i = readCol W i := by
      funext u v
      change (W u v ++ [gateRow W g u v]).getD i false = _
      rw [read_snoc,sz]
      simp only [hi,ite_true]
      rfl
    exact eq ▸ List.mem_cons_of_mem _ (cov i)
  · by_cases he : i = n
    · have eq : readCol (appendGate W g) i = gateRow W g := by
        funext u v
        change (W u v ++ [gateRow W g u v]).getD i false = _
        rw [read_snoc,sz]
        simp [he]
      exact eq ▸ List.mem_cons_self
    · have eq : readCol (appendGate W g) i = falseCol := by
        funext u v
        change (W u v ++ [gateRow W g u v]).getD i false = false
        rw [read_snoc,sz]
        simp only [hi,he,ite_false]
      exact eq ▸ List.mem_cons_of_mem _ hz

def stage : ℕ → List Row → Row → Prop
  | 0, S, t => t ∈ S
  | k+1, S, t => ∃ a ∈ nextRows S, stage k (a :: S) t

def evalCol (gs : List Gate) (W : Bank) (out : ℕ) : Row := fun u v =>
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (W u v)).getD out false

theorem lower_from_bank (k : ℕ) (gs : List Gate) (W : Bank) (n out : ℕ) (S : List Row)
    (sz : ∀ u v, (W u v).length = n) (cov : Covered S W)
    (hz : falseCol ∈ S) (ho : trueCol ∈ S) (ops : ∀ g ∈ gs, legal g)
    (budget : gs.length ≤ k) : stage k S (evalCol gs W out) := by
  induction k generalizing gs W n S with
  | zero =>
    have hnil : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    exact cov out
  | succ k ih =>
    cases gs with
    | nil =>
      refine ⟨falseCol,next_old hz,?_⟩
      apply ih [] W n (falseCol :: S) sz
      · exact fun i => List.mem_cons_of_mem _ (cov i)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ho
      · simp
      · simp
    | cons g gs =>
      refine ⟨gateRow W g,gate_mem cov hz ho g (ops g List.mem_cons_self),?_⟩
      change stage k (gateRow W g :: S) (evalCol gs (appendGate W g) out)
      apply ih gs (appendGate W g) (n+1) (gateRow W g :: S)
      · intro u v; simp [appendGate,sz]
      · exact append_covered cov sz hz g
      · exact List.mem_cons_of_mem _ hz
      · exact List.mem_cons_of_mem _ ho
      · exact fun q h => ops q (List.mem_cons_of_mem _ h)
      · simpa using budget

theorem initial_covered : Covered pool (fun u v : Fin 3 => oneEach u.castSucc v.castSucc) := by
  intro i
  by_cases hi : i < 8
  · have finite : ∀ j : Fin 8, readCol (fun u v : Fin 3 => oneEach u.castSucc v.castSucc) j.val ∈ pool := by
      decide +kernel
    exact finite ⟨i,hi⟩
  · have eq : readCol (fun u v : Fin 3 => oneEach u.castSucc v.castSucc) i = falseCol := by
      funext u v
      simp only [readCol, falseCol, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp [oneEach]; omega)]
      rfl
    exact eq ▸ (show falseCol ∈ pool from List.mem_cons_self)

theorem lower (h : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 3 ∧ Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4*u.val+v.val)) C) :
    ∃ x ∈ nextRows pool, ∃ y ∈ nextRows (x :: pool), target ∈ nextRows (y :: x :: pool) := by
  obtain ⟨C,hops,hsize,hrep⟩ := h
  have hh := lower_from_bank 3 C.gates (fun u v : Fin 3 => oneEach u.castSucc v.castSucc) 8 C.output pool
    (by intro u v; simp [oneEach]) initial_covered (show falseCol ∈ pool from List.mem_cons_self)
    (show trueCol ∈ pool from List.mem_cons_of_mem _ List.mem_cons_self) (fun g h => by
      rcases hops g h with ⟨ha,hb⟩
      exact ⟨by simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using ha,hb⟩) hsize
  have he : evalCol C.gates (fun u v : Fin 3 => oneEach u.castSucc v.castSucc) C.output = target := by
    funext u v; exact hrep u.castSucc v.castSucc
  rw [he] at hh
  obtain ⟨x,hx,y,hy,z,hz,ht⟩ := hh
  refine ⟨x,hx,y,hy,?_⟩
  rcases List.mem_cons.mp ht with h | h
  · exact h ▸ hz
  · exact next_old h

end PEqualNP.Outside.L_meta_20792

namespace PEqualNP.Outside.L_meta_20792

abbrev Mask := BitVec 9

def mask (a : Row) : Mask :=
  BitVec.ofBool (a 0 0) ++ BitVec.ofBool (a 0 1) ++ BitVec.ofBool (a 0 2) ++
  BitVec.ofBool (a 1 0) ++ BitVec.ofBool (a 1 1) ++ BitVec.ofBool (a 1 2) ++
  BitVec.ofBool (a 2 0) ++ BitVec.ofBool (a 2 1) ++ BitVec.ofBool (a 2 2)

lemma mask_not (a : Row) : mask (fun i j => !(a i j)) = ~~~(mask a) := by
  simp only [mask, BitVec.not_append (w := 8) (v := 1), BitVec.not_append (w := 7) (v := 1), BitVec.not_append (w := 6) (v := 1), BitVec.not_append (w := 5) (v := 1), BitVec.not_append (w := 4) (v := 1), BitVec.not_append (w := 3) (v := 1), BitVec.not_append (w := 2) (v := 1), BitVec.not_append (w := 1) (v := 1), BitVec.not_ofBool]
lemma mask_and (a b : Row) : mask (fun i j => a i j && b i j) = mask a &&& mask b := by
  simp only [mask, BitVec.and_append (w := 8) (v := 1), BitVec.and_append (w := 7) (v := 1), BitVec.and_append (w := 6) (v := 1), BitVec.and_append (w := 5) (v := 1), BitVec.and_append (w := 4) (v := 1), BitVec.and_append (w := 3) (v := 1), BitVec.and_append (w := 2) (v := 1), BitVec.and_append (w := 1) (v := 1), BitVec.ofBool_and_ofBool]
lemma mask_or (a b : Row) : mask (fun i j => a i j || b i j) = mask a ||| mask b := by
  simp only [mask, BitVec.or_append (w := 8) (v := 1), BitVec.or_append (w := 7) (v := 1), BitVec.or_append (w := 6) (v := 1), BitVec.or_append (w := 5) (v := 1), BitVec.or_append (w := 4) (v := 1), BitVec.or_append (w := 3) (v := 1), BitVec.or_append (w := 2) (v := 1), BitVec.or_append (w := 1) (v := 1), BitVec.ofBool_or_ofBool]

def candidates (W : List Mask) : List Mask :=
  W ++ W.map (fun v => ~~~v) ++ W.flatMap (fun a => W.flatMap (fun b => [a &&& b,a ||| b]))

theorem transfer {B : List Row} {W : List Mask}
    (hr : ∀ t ∈ B, mask t ∈ W) {t} (ht : t ∈ nextRows B) : mask t ∈ candidates W := by
  simp only [nextRows, candidates, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at ht ⊢
  rcases ht with ((ht | ⟨a,ha,rfl⟩) | ⟨a,ha,b,hb,h⟩)
  · exact Or.inl (Or.inl (hr _ ht))
  · exact Or.inl (Or.inr ⟨mask a,hr _ ha,(mask_not a).symm⟩)
  · refine Or.inr ⟨mask a,hr _ ha,mask b,hr _ hb,?_⟩
    rcases h with rfl | rfl
    · exact Or.inl (mask_and _ _)
    · exact Or.inr (mask_or _ _)

def first : List Mask := pool.map mask

def hasLast (W : List Mask) (v : Mask) : Bool :=
  W.contains v || W.contains (~~~v) || W.any (fun a => W.any fun b => (a &&& b == v) || (a ||| b == v))

lemma last_sound {W : List Mask} {v : Mask} (hv : v ∈ candidates W) : hasLast W v = true := by
  simp only [candidates, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  simp only [hasLast, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq]
  rcases hv with ((h | ⟨a,ha,rfl⟩) | ⟨a,ha,b,hb,h⟩)
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (by simpa using ha))
  · exact Or.inr ⟨a,ha,b,hb,h.imp Eq.symm Eq.symm⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem finite_check :
  ((candidates first).eraseDups.all (fun x => (candidates (x :: first)).eraseDups.all
    (fun y => !(hasLast (y :: x :: first) (mask target))))) = true := by decide +kernel

theorem no_three : ¬ ∃ x ∈ nextRows pool, ∃ y ∈ nextRows (x :: pool), target ∈ nextRows (y :: x :: pool) := by
  rintro ⟨x,hx,y,hy,ht⟩
  have first_ok (t) (ht : t ∈ pool) : mask t ∈ first := List.mem_map_of_mem ht
  have one := transfer first_ok hx
  have next_ok (t) (ht : t ∈ x :: pool) : mask t ∈ mask x :: first := by
    rcases List.mem_cons.mp ht with rfl|h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (first_ok _ h)
  have two := transfer next_ok hy
  have last_ok (t) (ht : t ∈ y :: x :: pool) : mask t ∈ mask y :: mask x :: first := by
    rcases List.mem_cons.mp ht with rfl|h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (next_ok _ h)
  have three := last_sound (transfer last_ok ht)
  have sel := List.all_eq_true.mp (List.all_eq_true.mp finite_check (mask x) (by simpa using one))
    (mask y) (by simpa using two)
  simp [three] at sel

end PEqualNP.Outside.L_meta_20792

theorem PEqualNP.Outside.L_meta_20792 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (30 : ℕ).testBit (4 * u.val + v.val)) C)) := fun h => PEqualNP.Outside.L_meta_20792.no_three (PEqualNP.Outside.L_meta_20792.lower h)
