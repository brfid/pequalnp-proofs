import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27446_aux

open PEqualNP.CircuitLowerBounds
namespace CircuitSatBridge

def source (n i : Nat) : Nat := if i < n then i+1 else 0

def read (w : List Bool) : Nat → Bool
  | 0 => false
  | i+1 => w.getD i false

theorem read_source (w : List Bool) (i : Nat) :
    read w (source w.length i) = w.getD i false := by
  by_cases h : i < w.length
  · simp [source, h, read]
  · simp [source, h, read]

abbrev Op := Ordering
abbrev Choice := Ordering × Nat × Nat
abbrev Choice.mk (op : Op) (l r : Nat) : Choice := (op,l,r)

def Choice.eval (c : Choice) (w : List Bool) : Bool :=
  match c.1 with
  | .lt => read w c.2.1 && read w c.2.2
  | .eq => read w c.2.1 || read w c.2.2
  | .gt => !read w c.2.1

def binary (op : Op) (a b : Nat) : Choice := ⟨op, min a b, max a b⟩

def normalize (n : Nat) (g : Gate) : Choice :=
  match g.op, g.inputs with
  | .and, [] => ⟨.gt, 0, 0⟩
  | .and, a :: xs => binary .lt (source n a) (source n (xs.headD a))
  | .or, [] => ⟨.eq, 0, 0⟩
  | .or, a :: xs => binary .eq (source n a) (source n (xs.headD a))
  | .not, [] => ⟨.gt, 0, 0⟩
  | .not, a :: _ => ⟨.gt, source n a, 0⟩
  | _, _ => ⟨.eq, 0, 0⟩

def Supported (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem binary_and (a b : Nat) (w : List Bool) :
    (binary .lt a b).eval w = (read w a && read w b) := by
  rcases le_total a b with h|h <;>
    simp [binary, Choice.eval, h, Bool.and_comm]

private theorem binary_or (a b : Nat) (w : List Bool) :
    (binary .eq a b).eval w = (read w a || read w b) := by
  rcases le_total a b with h|h <;>
    simp [binary, Choice.eval, h, Bool.or_comm]

private theorem neg_eval (l r : Nat) (w : List Bool) :
    (Choice.mk .gt l r).eval w = !read w l := rfl

theorem normalize_correct (w : List Bool) (g : Gate) (h : Supported g) :
    (normalize w.length g).eval w = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change xs.length ≤ 2 at hlen
  change op = _ ∨ op = _ ∨ op = _ at hop
  cases xs with
  | nil => rcases hop with rfl|rfl|rfl <;> rfl
  | cons a xs =>
    cases xs with
    | nil => rcases hop with rfl|rfl|rfl <;>
               simp [normalize, binary_and, binary_or, neg_eval, GateOp.eval, read_source]
    | cons b xs =>
      have : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst xs
      rcases hop with rfl|rfl|rfl <;>
        simp [normalize, binary_and, binary_or, neg_eval, GateOp.eval, read_source]

def compile (n : Nat) : List Gate → List Choice
  | [] => []
  | g :: gs => normalize n g :: compile (n+1) gs

theorem compile_wires (gs : List Gate) (w : List Bool) (h : ∀ g ∈ gs, Supported g) :
    (compile w.length gs).foldl (fun v c => v ++ [c.eval v]) w =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [compile, List.foldl_cons, normalize_correct w g (h g List.mem_cons_self)]
    apply Eq.trans _ (ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha)))
    simp

def Choice.Legal (n : Nat) (c : Choice) : Prop :=
  c.2.1 ≤ n ∧ c.2.2 ≤ n ∧
    match c.1 with
    | .gt => c.2.2 = 0
    | _ => c.2.1 ≤ c.2.2

private theorem source_le (n i : Nat) : source n i ≤ n := by
  unfold source
  split <;> omega

theorem normalize_legal (n : Nat) (g : Gate) : (normalize n g).Legal n := by
  obtain ⟨op, xs⟩ := g
  cases op <;> cases xs <;>
    simp [normalize, Choice.Legal, binary, source_le]

theorem compile_length (gs : List Gate) (n : Nat) : (compile n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [compile, ih]

def operatorClauses (sa so sn a b y : Bool) : List Bool :=
  [!sa || !a || !b || y, !sa || a || !y, !sa || b || !y,
   !so || a || b || !y, !so || !a || y, !so || !b || y,
   !sn || a || y, !sn || !a || !y]

def selectors : Op → Bool × Bool × Bool
  | .lt => (true, false, false)
  | .eq => (false, true, false)
  | .gt => (false, false, true)

theorem operatorClauses_iff (c : Choice) (w : List Bool) (y : Bool) :
    (operatorClauses (selectors c.1).1 (selectors c.1).2.1 (selectors c.1).2.2
      (read w c.2.1) (read w c.2.2) y).all id = true ↔ y = c.eval w := by
  obtain ⟨op, l, r⟩ := c
  cases op <;> simp only [Choice.eval, selectors] <;>
    cases read w l <;> cases read w r <;> cases y <;> decide

def muxClauses (pick operand upstream : Bool) : List Bool :=
  [!pick || operand || !upstream, !pick || !operand || upstream]

theorem muxClauses_correct (w : List Bool) (selected candidate : Nat) :
    (muxClauses (decide (selected = candidate)) (read w selected) (read w candidate)).all id =
      true := by
  by_cases h : selected = candidate
  · subst candidate
    cases read w selected <;> simp [muxClauses, *]
  · simp [muxClauses, h]

theorem gate_rows (n : Nat) (g : Gate) (hg : Supported g) :
    ∃ c : Choice, c.Legal n ∧ ∀ w : List Bool, w.length = n →
      (∀ i, (muxClauses (decide (c.2.1 = i)) (read w c.2.1) (read w i)).all id = true ∧
            (muxClauses (decide (c.2.2 = i)) (read w c.2.2) (read w i)).all id = true) ∧
      (operatorClauses (selectors c.1).1 (selectors c.1).2.1 (selectors c.1).2.2
        (read w c.2.1) (read w c.2.2)
        (g.op.eval (g.inputs.map fun i => w.getD i false))).all id = true := by
  refine ⟨normalize n g, normalize_legal n g, ?_⟩
  intro w hw
  subst n
  exact ⟨fun i => ⟨muxClauses_correct _ _ _, muxClauses_correct _ _ _⟩,
    (operatorClauses_iff _ _ _).2 (normalize_correct w g hg).symm⟩

theorem compile_circuit (c : Circuit) (hc : PEqualNP.MetaComplexity.FanInTwo c) (n : Nat) :
    ∃ cs : List Choice, cs.length = c.size ∧ ∀ w : List Bool, w.length = n →
      (cs.foldl (fun v gate => v ++ [gate.eval v]) w).getD c.output false = c.eval w := by
  refine ⟨compile n c.gates, compile_length _ _, ?_⟩
  intro w hw
  subst n
  rw [compile_wires _ _ hc]
  rfl

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

def runChoices (gs : List Choice) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.eval v]) w

def Valid : Nat → List Choice → Prop
  | _, [] => True
  | n, c :: cs => c.Legal n ∧ Valid (n+1) cs

def copyWire (n i : Nat) : Choice := ⟨.eq, source n i, source n i⟩

private theorem copy_legal (n i : Nat) : (copyWire n i).Legal n := by
  simp [copyWire, Choice.Legal, source_le]

private theorem copy_eval (w : List Bool) (i : Nat) :
    (copyWire w.length i).eval w = w.getD i false := by
  simp [copyWire, Choice.eval, read_source]

private theorem append_at_end (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp

private theorem append_elsewhere (w : List Bool) (b : Bool) (i : Nat) (hne : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hi' : w.length ≤ i := by omega
    rw [List.getD_eq_default _ _ hi', List.getD_eq_default _ _ (by simp; omega)]

theorem fixed_slots (k n output : Nat) (gs : List Gate) (hs : ∀ g ∈ gs, Supported g)
    (hlen : gs.length ≤ k+1) :
    ∃ cs : List Choice, cs.length = k+1 ∧ Valid n cs ∧
      ∀ w : List Bool, w.length = n →
        (runChoices cs w).getD (n+k) false = (run gs w).getD output false := by
  induction k generalizing n output gs with
  | zero =>
    cases gs with
    | nil =>
      refine ⟨[copyWire n output], rfl, ⟨copy_legal _ _, trivial⟩, ?_⟩
      intro w hw
      subst n
      exact (append_at_end _ _).trans (copy_eval _ _)
    | cons g gs =>
      have : gs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst gs
      by_cases hout : output = n
      · refine ⟨[normalize n g], rfl, ⟨normalize_legal _ _, trivial⟩, ?_⟩
        intro w hw
        subst n
        subst output
        change (_ ++ [_]).getD _ _ = (_ ++ [_]).getD _ _
        rw [normalize_correct w g (hs _ List.mem_cons_self)]
        rfl
      · refine ⟨[copyWire n output], rfl, ⟨copy_legal _ _, trivial⟩, ?_⟩
        intro w hw
        subst n
        exact (append_at_end _ _).trans ((copy_eval _ _).trans
          (append_elsewhere w _ output hout).symm)
  | succ k ih =>
    cases gs with
    | cons g gs =>
      obtain ⟨cs, hsize, hvalid, heval⟩ := ih (n+1) output gs
        (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (by simpa using hlen)
      refine ⟨normalize n g :: cs, by simp [hsize], ⟨normalize_legal _ _, hvalid⟩, ?_⟩
      intro w hw
      subst n
      change (runChoices cs (w ++ [_])).getD _ _ = (run gs (w ++ [_])).getD _ _
      rw [normalize_correct w g (hs _ List.mem_cons_self)]
      simpa only [Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1 k] using
        heval (w ++ [_]) (by simp)
    | nil =>
      obtain ⟨cs, hsize, hvalid, heval⟩ := ih (output := n) (n+1) [] (by simp) (by simp)
      refine ⟨copyWire n output :: cs, by simp [hsize], ⟨copy_legal _ _, hvalid⟩, ?_⟩
      intro w hw
      subst n
      change (runChoices cs (w ++ [_])).getD _ _ = w.getD output false
      have h := heval (w ++ [(copyWire w.length output).eval w]) (by simp)
      simpa [run, copy_eval, Nat.add_assoc, Nat.add_comm 1 k] using h

end CircuitSatBridge

namespace CircuitSatBridge

def before (cs : List Choice) (w : List Bool) (j : Nat) : List Bool :=
  runChoices (cs.take j) w

private theorem runChoices_append (xs ys : List Choice) (w : List Bool) :
    runChoices (xs ++ ys) w = runChoices ys (runChoices xs w) := by
  simp [runChoices, List.foldl_append]

theorem before_length (cs : List Choice) (w : List Bool) (j : Nat) :
    (before cs w j).length = w.length + min j cs.length := by
  have len : ∀ (gs : List Choice) (x : List Bool), (runChoices gs x).length = x.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp [runChoices]
    | cons g gs ih =>
      intro x
      change (runChoices gs (x ++ [g.eval x])).length = _
      rw [ih]
      simp
      omega
  simp [before, len]

theorem before_step (cs : List Choice) (w : List Bool) (j : Nat) (hj : j < cs.length) :
    before cs w (j+1) = before cs w j ++ [cs[j].eval (before cs w j)] := by
  rw [before, List.take_add_one, List.getElem?_eq_getElem hj]
  exact runChoices_append _ _ _

private theorem keeps_prefix (cs : List Choice) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (runChoices cs w).getD i false = w.getD i false := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change (runChoices cs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem before_keeps (cs : List Choice) (w : List Bool) {a b i : Nat} (hab : a ≤ b)
    (hi : i < (before cs w a).length) :
    (before cs w b).getD i false = (before cs w a).getD i false := by
  have h : cs.take b = cs.take a ++ (cs.take b).drop a := by
    have ht : (cs.take b).take a = cs.take a := by simp [List.take_take, hab]
    rw [← ht]
    simp
  unfold before at *
  rw [h, runChoices_append, keeps_prefix _ _ _ hi]

def gateValue (cs : List Choice) (w : List Bool) (j : Nat) : Bool :=
  (before cs w (j+1)).getD (w.length+j) false

theorem gateValue_eq (cs : List Choice) (w : List Bool) (j : Nat) (hj : j < cs.length) :
    gateValue cs w j = cs[j].eval (before cs w j) := by
  rw [gateValue, before_step _ _ _ hj]
  have h := before_length cs w j
  rw [Nat.min_eq_left (by omega)] at h
  rw [← h, append_at_end]

theorem read_earlier_gate (cs : List Choice) (w : List Bool) {a b : Nat}
    (hab : a < b) (hb : b ≤ cs.length) :
    read (before cs w b) (w.length+a+1) = gateValue cs w a := by
  apply before_keeps _ _ (Nat.succ_le_of_lt hab)
  rw [before_length, Nat.min_eq_left (by omega)]
  omega

theorem read_input (cs : List Choice) (w : List Bool) (j i : Nat) (hi : i < w.length) :
    read (before cs w j) (i+1) = w.getD i false :=
  keeps_prefix _ _ _ hi

end CircuitSatBridge

namespace CircuitSatBridge

def agrees (s : Finset Nat) (x y : List Bool) := ∀ i ∈ s, x.getD i false = y.getD i false

theorem bounded_support (cs : List Choice) (n out : Nat) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ cs.length+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → agrees s x y →
        (runChoices cs x).getD out false = (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp, fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro x y hx hy _
      change x.getD out false = y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1)
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, c.2.2-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ 2 := (Finset.card_filter_le _ _).trans
            ((Finset.card_insert_le _ _).trans (by simp))
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [List.length_cons]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = c.2.2) : read x q = read y q := by
          cases q with
          | zero => rfl
          | succ q =>
            change x.getD q false = y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have ev : c.eval x = c.eval y := by
            unfold Choice.eval
            rw [readEq _ (Or.inl rfl), readEq _ (Or.inr rfl)]
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace CircuitSatBridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def IsMonotone (c : Choice) : Prop := c.1 = .gt → c.2.1 = 0

private theorem normalization_mono (n : Nat) (g : Gate) (h : g.op = .and ∨ g.op = .or) :
    IsMonotone (normalize n g) := by
  obtain ⟨op,xs⟩ := g
  rcases h with h|h <;> dsimp at h <;> subst op <;> cases xs <;> simp [normalize,binary,IsMonotone]

private theorem compile_mono (gs : List Gate) (n : Nat)
    (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    Valid n (compile n gs) ∧ ∀ c ∈ compile n gs, IsMonotone c := by
  induction gs generalizing n with
  | nil => exact ⟨trivial, by simp [compile]⟩
  | cons g gs ih =>
    obtain ⟨hv,hm⟩ := ih (n+1) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨⟨normalize_legal _ _,hv⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl|hc
    · exact normalization_mono _ _ (h g List.mem_cons_self)
    · exact hm _ hc

def falseGate : Choice := ⟨.eq,0,0⟩

private theorem pad_eval (k : Nat) (x : List Bool) (o : Nat) :
    (runChoices (List.replicate k falseGate) x).getD o false = x.getD o false := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    change (runChoices _ (x ++ [false])).getD o false = _
    rw [ih]
    by_cases ho : o < x.length
    · exact List.getD_append _ _ _ _ ho
    · have hh : x.length ≤ o := by omega
      rw [List.getD_append_right _ _ _ _ hh, List.getD_eq_default _ _ hh]
      cases o - x.length <;> rfl

private theorem pad_valid (cs : List Choice) (n k : Nat) (h : Valid n cs) :
    Valid n (cs ++ List.replicate k falseGate) := by
  induction cs generalizing n with
  | nil =>
    induction k generalizing n with
    | zero => trivial
    | succ k ih => exact ⟨by simp [falseGate,Choice.Legal], ih (n+1) trivial⟩
  | cons c cs ih => exact ⟨h.1, ih _ h.2⟩

theorem monotone_slots (n k : Nat) {c : Circuit} (hm : Monotone2 c) (hs : c.size ≤ k) :
    ∃ cs : List Choice, cs.length = k ∧ Valid n cs ∧ (∀ g ∈ cs, IsMonotone g) ∧
    ∀ w : List Bool, w.length = n → (runChoices cs w).getD c.output false = c.eval w := by
  obtain ⟨hv, hmono⟩ := compile_mono c.gates n (fun g hg => (hm g hg).1)
  let padded := List.replicate (k-c.size) falseGate
  refine ⟨compile n c.gates ++ padded, ?_, pad_valid _ _ _ hv, ?_, ?_⟩
  · simp [padded, compile_length, Circuit.size] at *
    omega
  · intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact hmono _ h
    · have he := (List.mem_replicate.mp h).2
      subst g
      simp [falseGate, IsMonotone]
  · intro w hw
    subst n
    change (List.foldl _ w (_ ++ _)).getD _ _ = _
    rw [List.foldl_append]
    change (runChoices padded (runChoices _ w)).getD _ _ = _
    rw [pad_eval]
    unfold runChoices
    rw [compile_wires]
    · rfl
    · intro g hg
      obtain ⟨hop, hb⟩ := hm g hg
      rcases hop with hop|hop
      · exact ⟨Or.inl hop,hb⟩
      · exact ⟨Or.inr (Or.inl hop),hb⟩

end CircuitSatBridge

namespace CircuitSatBridge

def remapGate (f : Nat → Nat) (c : Choice) : Choice :=
  match c.1 with
  | .lt => binary .lt (f c.2.1) (f c.2.2)
  | .eq => binary .eq (f c.2.1) (f c.2.2)
  | .gt => ⟨.gt,f c.2.1,0⟩

def liftMap (f : Nat → Nat) (n m q : Nat) := if q = n+1 then m+1 else f q

def transfer (f : Nat → Nat) (n m : Nat) (cs : List Choice) : List Choice × (Nat → Nat) :=
  match cs with
  | [] => ([],f)
  | c :: rest =>
    let (gs,last) := transfer (liftMap f n m) (n+1) (m+1) rest
    (remapGate f c :: gs,last)

def BoundedMap (m : Nat) (f : Nat → Nat) := f 0 = 0 ∧ ∀ q, f q ≤ m

private theorem lift_bounded {f : Nat → Nat} {n m : Nat} (h : BoundedMap m f) :
    BoundedMap (m+1) (liftMap f n m) := by
  refine ⟨by simp [liftMap, h.1], ?_⟩
  intro q
  have := h.2 q
  unfold liftMap; split <;> omega

private theorem remap_legal (c : Choice) {f : Nat → Nat} {m : Nat} (h : BoundedMap m f) :
    (remapGate f c).Legal m := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp [remapGate, Choice.Legal, binary, h.2]

private theorem remap_mono {c : Choice} {f : Nat → Nat} {m : Nat} (h : BoundedMap m f)
    (hc : IsMonotone c) : IsMonotone (remapGate f c) := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp_all [IsMonotone, remapGate, binary, h.1]

theorem transfer_valid (cs : List Choice) (f : Nat → Nat) (n m : Nat) (h : BoundedMap m f) :
    Valid m (transfer f n m cs).1 ∧ (transfer f n m cs).1.length = cs.length := by
  induction cs generalizing n m f with
  | nil => exact ⟨trivial,rfl⟩
  | cons c cs ih =>
    obtain ⟨hv,hl⟩ := ih _ _ _ (lift_bounded (n := n) h)
    exact ⟨⟨remap_legal _ h,hv⟩, congrArg Nat.succ hl⟩

theorem transfer_mono (cs : List Choice) (f : Nat → Nat) (n m : Nat) (h : BoundedMap m f)
    (hc : ∀ c ∈ cs, IsMonotone c) : ∀ g ∈ (transfer f n m cs).1, IsMonotone g := by
  induction cs generalizing n m f with
  | nil => simp [transfer]
  | cons c cs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hm
    · exact remap_mono h (hc _ List.mem_cons_self)
    · exact ih _ _ _ (lift_bounded (n := n) h) (fun a ha => hc _ (List.mem_cons_of_mem _ ha)) _ hm

def ReadsAs (f : Nat → Nat) (x y : List Bool) : Prop := ∀ q, read x q = read y (f q)

private theorem remap_eval {f : Nat → Nat} {x y : List Bool} (hr : ReadsAs f x y) (c : Choice) :
    (remapGate f c).eval y = c.eval x := by
  obtain ⟨op,l,r⟩ := c
  cases op <;> simp only [remapGate, Choice.eval, binary] <;>
    rcases le_total (f l) (f r) with h|h <;> simp [h, hr l, hr r, Bool.and_comm, Bool.or_comm]

private theorem read_append (x : List Bool) (q : Nat) (b : Bool) :
    read (x ++ [b]) q = if q = x.length+1 then b else read x q := by
  cases q with
  | zero => simp [CircuitSatBridge.read]
  | succ i =>
    simp only [CircuitSatBridge.read, Nat.add_right_cancel_iff]
    split
    · next h => subst i; simp
    · next h =>
      by_cases hi : i < x.length
      · exact List.getD_append _ _ _ _ hi
      · have he : x.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ he, List.getD_eq_default _ _ he,
          List.getD_eq_default _ _ (by simp; omega)]

private theorem extend_reads {f : Nat → Nat} {x y : List Bool} (h : BoundedMap y.length f)
    (hr : ReadsAs f x y) (c : Choice) :
    ReadsAs (liftMap f x.length y.length) (x ++ [c.eval x]) (y ++ [(remapGate f c).eval y]) := by
  intro q
  have hq := h.2 q
  by_cases he : q = x.length+1
  · simp [read_append, liftMap, he, remap_eval hr]
  · simp [read_append, liftMap, he, show f q ≠ y.length+1 by omega, hr q]

theorem transfer_eval (cs : List Choice) (f : Nat → Nat) (x y : List Bool)
    (h : BoundedMap y.length f) (hr : ReadsAs f x y) :
    ReadsAs (transfer f x.length y.length cs).2 (runChoices cs x)
      (runChoices (transfer f x.length y.length cs).1 y) := by
  induction cs generalizing x y f with
  | nil => exact hr
  | cons c cs ih =>
    have hd := ih _ _ _ (show BoundedMap (y ++ [(remapGate f c).eval y]).length
        (liftMap f x.length y.length) by simpa using lift_bounded (n := x.length) h) (extend_reads h hr c)
    simpa [transfer, runChoices] using hd

end CircuitSatBridge

namespace CircuitSatBridge

def pull (f : Nat → Nat) (n : Nat) (y : List Bool) :=
  List.ofFn fun i : Fin n => read y (f (i.val+1))

theorem pull_len (f : Nat → Nat) (n : Nat) (y : List Bool) : (pull f n y).length = n := by
  simp [pull]

theorem pull_at (f : Nat → Nat) (n : Nat) (y : List Bool) (i : Nat) (hi : i < n) :
    (pull f n y).getD i false = read y (f (i+1)) := by
  simp [pull, List.getElem?_eq_getElem, hi]

def SourceMap (n m : Nat) (f : Nat → Nat) := BoundedMap m f ∧ ∀ i, n ≤ i → f (i+1) = 0

theorem pull_reads {n m : Nat} {f : Nat → Nat} (h : SourceMap n m f) (y : List Bool) :
    ReadsAs f (pull f n y) y := by
  intro q
  cases q with
  | zero => rw [h.1.1]; rfl
  | succ i =>
    by_cases hi : i < n
    · exact pull_at _ _ _ _ hi
    · rw [h.2 i (by omega)]
      change (pull f n y).getD i false = false
      exact List.getD_eq_default _ _ (by rw [pull_len]; omega)

theorem transfer_pull (cs : List Choice) {f : Nat → Nat} {n m : Nat} (h : SourceMap n m f)
    (y : List Bool) (hy : y.length = m) (out : Nat) :
    read (runChoices (transfer f n m cs).1 y) ((transfer f n m cs).2 (out+1)) =
      (runChoices cs (pull f n y)).getD out false := by
  have he := transfer_eval cs f (pull f n y) y (hy ▸ h.1) (pull_reads h y) (out+1)
  rw [pull_len,hy] at he
  exact he.symm

end CircuitSatBridge

namespace FreeSupport
open CircuitSatBridge

abbrev Word := BitVec 110
abbrev Wire := Word × Word

def sample (ws : List Wire) (t : Fin 110) (side : Bool) : List Bool :=
  ws.map fun (l,r) => (if side then r else l).getLsbD t.val

def wire (ws : List Wire) : Nat → Wire
  | 0 => (0,0)
  | i+1 => ws.getD i (0,0)

def evalW (c : Choice) (ws : List Wire) : Wire :=
  let (l,r) := wire ws c.2.1
  let (l',r') := wire ws c.2.2
  match c.1 with
  | .lt => (l &&& l',r &&& r')
  | .eq => (l ||| l',r ||| r')
  | .gt => (~~~l,~~~r)

def extend (c : Choice) (ws : List Wire) := ws ++ [evalW c ws]

private theorem sample_read (ws : List Wire) (t : Fin 110) (s : Bool) (q : Nat) :
    read (sample ws t s) q = (if s then (wire ws q).2 else (wire ws q).1).getLsbD t := by
  cases q with
  | zero => cases s <;> simp [CircuitSatBridge.read, wire]
  | succ i =>
    cases s <;> simp [CircuitSatBridge.read, sample, wire, List.getElem?_map] <;>
      cases ws[i]? <;> simp

theorem sample_extend (ws : List Wire) (t : Fin 110) (s : Bool) (c : Choice) :
    sample (extend c ws) t s = sample ws t s ++ [c.eval (sample ws t s)] := by
  obtain ⟨op,l,r⟩ := c
  have hl := sample_read ws t s l
  have hr := sample_read ws t s r
  cases op <;> cases s <;> simp_all [extend, sample, evalW, Choice.eval, Fin.is_lt]

def delta (ws : List Wire) (i : Nat) : Word :=
  let w := ws.getD i (0,0)
  w.1 ^^^ w.2

def unionD (ws : List Wire) (ix : List Nat) : Word :=
  (ix.map (delta ws)).foldr (· ||| ·) 0

theorem bit_union (ws : List Wire) (ix : List Nat) (t : Fin 110) :
    (unionD ws ix).getLsbD t = true ↔ ∃ i ∈ ix, (delta ws i).getLsbD t = true := by
  induction ix with
  | nil => simp [unionD]
  | cons i ix ih =>
    change ((delta ws i ||| unionD ws ix).getLsbD t = true) ↔ _
    simp only [BitVec.getLsbD_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]

def cover (ws : List Wire) (k : Nat) : Bool :=
  decide (∃ s ∈ (Finset.range ws.length).powerset,
    s.card ≤ k ∧ unionD ws ((List.range ws.length).filter (fun i => i ∈ s)) = BitVec.allOnes 110)

def distinguished (cs : List Choice) (ws : List Wire) (out : Nat) : Prop :=
  ∀ t : Fin 110, (runChoices cs (sample ws t false)).getD out false ≠
                  (runChoices cs (sample ws t true)).getD out false

theorem suffix_cover (cs : List Choice) (ws : List Wire) (out : Nat)
    (h : distinguished cs ws out) : cover ws (cs.length+1) = true := by
  obtain ⟨s, hs, hcard, determ⟩ := bounded_support cs ws.length out
  have hbits (t : Fin 110) : ∃ i ∈ s, (delta ws i).getLsbD t = true := by
    by_contra! hn
    apply h t
    apply determ _ _ (by simp [sample]) (by simp [sample])
    intro i hi
    have hb := hn i hi
    have hii := Finset.mem_range.mp (hs hi)
    simp [delta, List.getElem?_eq_getElem hii] at hb
    simpa [sample, List.getElem?_eq_getElem hii] using hb
  have hu : unionD ws ((List.range ws.length).filter (fun i => i ∈ s)) = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨x,hx,hd⟩ := hbits ⟨i,hi⟩
    simpa only [BitVec.getLsbD_allOnes, decide_eq_true hi] using (bit_union ws ((List.range ws.length).filter (fun i => i ∈ s)) ⟨i,hi⟩).mpr
      ⟨x, by simp [hx, Finset.mem_range.mp (hs hx)], hd⟩
  exact decide_eq_true ⟨s, Finset.mem_powerset.mpr hs, hcard, hu⟩

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def scan (k : Nat) (acc : Word) (xs : List Word) : Bool :=
  match k, xs with
  | 0, _ | _, [] => acc == BitVec.allOnes 110
  | k+1, x :: rest => scan (k+1) acc rest || scan k (acc ||| x) rest

private theorem scan_complete (ws : List Wire) (s : Finset Nat) (ix : List Nat)
    (k : Nat) (acc : Word) (hk : (ix.filter (· ∈ s)).length ≤ k)
    (hu : acc ||| unionD ws (ix.filter (· ∈ s)) = BitVec.allOnes 110) :
    scan k acc (ix.map (delta ws)) = true := by
  induction ix generalizing acc k with
  | nil => cases k <;> simpa [scan, unionD] using hu
  | cons i ix ih =>
    cases k with
    | zero =>
      have hnil : ((i :: ix).filter (· ∈ s)) = [] := List.length_eq_zero_iff.mp (by omega)
      simpa [scan, hnil, unionD] using hu
    | succ k =>
      simp only [List.map_cons, scan, Bool.or_eq_true]
      by_cases h : i ∈ s
      · right
        apply ih k _ (by simpa [h] using hk)
        simpa only [List.filter_cons_of_pos (p := fun a => decide (a ∈ s)) (by simpa using h),
          unionD, List.map_cons, List.foldr_cons, BitVec.or_assoc] using hu
      · exact Or.inl (ih _ _ (by simpa [h] using hk) (by simpa [h] using hu))

def fastCover (ws : List Wire) (k : Nat) : Bool :=
  scan k 0 ((List.range ws.length).map (delta ws))

theorem fast_of_cover {ws : List Wire} {k : Nat} (h : cover ws k) : fastCover ws k := by
  obtain ⟨s, hs, hk, hu⟩ := of_decide_eq_true h
  apply scan_complete ws s
  · have hl : ((List.range ws.length).filter (· ∈ s)).toFinset = s := by
      ext i
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact and_iff_right_of_imp (fun hi => Finset.mem_range.mp (Finset.mem_powerset.mp hs hi))
    have hn := (List.nodup_range (n := ws.length)).filter (p := fun i => decide (i ∈ s))
    rwa [← List.toFinset_card_of_nodup hn, hl]
  · simpa using hu

def candidates (n : Nat) : List Choice :=
  (List.range (n+1)).flatMap fun l =>
    [(Choice.mk .gt l 0)] ++ ((List.range (n+1)).filter (l ≤ ·)).flatMap fun r =>
       [⟨.lt,l,r⟩,⟨.eq,l,r⟩]

theorem candidate_mem {c : Choice} {n : Nat} (h : c.Legal n) : c ∈ candidates n := by
  obtain ⟨op,l,r⟩ := c
  obtain ⟨hl, hr, ho⟩ := h
  change l ≤ n at hl
  change r ≤ n at hr
  apply List.mem_flatMap.mpr
  refine ⟨l,List.mem_range.mpr (by omega),?_⟩
  cases op <;> simp_all [List.mem_flatMap, List.mem_filter] <;> omega

def pass (ws : List Wire) (k : Nat) : List (List Wire) :=
  ((candidates ws.length).map (extend · ws)).filter (fastCover · k)

theorem extend_mem {c : Choice} {ws : List Wire} {cs : List Choice} {out : Nat}
    (hc : c.Legal ws.length) (h : distinguished (c :: cs) ws out) :
    extend c ws ∈ pass ws (cs.length+1) := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨c,candidate_mem hc,rfl⟩, fast_of_cover (suffix_cover cs _ out ?_)⟩
  intro t
  simpa only [sample_extend, runChoices, List.foldl_cons] using h t

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def residuals (k : Nat) (xs : List Word) (need : Word) : List Word :=
  match k, xs with
  | 0, _ | _, [] => [need]
  | k+1, x :: rest => residuals (k+1) rest need ++ residuals k rest (need &&& ~~~x)

private theorem scan_as_residual (xs : List Word) (k : Nat) (acc : Word) :
    scan k acc xs = ((residuals k xs (~~~acc)).any (· == 0)) := by
  have he (a : Word) : (a == BitVec.allOnes 110) = (~~~a == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · rintro rfl; decide
    · intro h
      have hh := congrArg (fun x : Word => ~~~x) h
      simpa [BitVec.not_not] using hh
  induction xs generalizing k acc with
  | nil => cases k <;> simp only [scan,residuals,List.any_cons,List.any_nil,Bool.or_false,he]
  | cons x xs ih =>
    cases k with
    | zero => simp only [scan,residuals,List.any_cons,List.any_nil,Bool.or_false,he]
    | succ k =>
      simp [scan,residuals, ih, BitVec.not_or]

private theorem resid_append (xs : List Word) (x : Word) (k : Nat) (need : Word) :
    (residuals (k+1) (xs ++ [x]) need).any (· == 0) =
    ((residuals (k+1) xs need).any (· == 0) ||
      (residuals k xs need).any (fun m => m &&& ~~~x == 0)) := by
  induction xs generalizing k need with
  | nil => cases k <;> simp [residuals]
  | cons y ys ih =>
    cases k with
    | zero => simp only [List.cons_append, residuals, List.any_append, ih, List.any_cons, List.any_nil, Bool.or_false]; ac_rfl
    | succ k => simp only [List.cons_append, residuals, List.any_append, ih, List.any_cons, List.any_nil, Bool.or_false]; ac_rfl

def oldCols (ws : List Wire) : List Word := ws.map fun w => w.1 ^^^ w.2

private theorem cols_eq (ws : List Wire) :
    (List.range ws.length).map (delta ws) = oldCols ws := by
  apply List.ext_getElem
  · simp [oldCols]
  · intro i h₁ h₂
    have hi : i < ws.length := by simpa [oldCols] using h₂
    simp [oldCols, delta, List.getElem?_eq_getElem hi]

def next (ws : List Wire) (k : Nat) : List (List Wire) :=
  let cols := oldCols ws
  let already := (residuals (k+1) cols (BitVec.allOnes 110)).any (· == 0)
  let rest := (residuals k cols (BitVec.allOnes 110)).eraseDups
  (((candidates ws.length).map (evalW · ws)).eraseDups.filter fun w =>
    already || rest.any (fun m => m &&& ~~~(w.1 ^^^ w.2) == 0)).map (ws ++ [·])

theorem next_mem {c : Choice} {ws : List Wire} {k : Nat} (hc : c.Legal ws.length)
    (h : fastCover (extend c ws) (k+1)) : extend c ws ∈ next ws k := by
  let w := evalW c ws
  apply List.mem_map.mpr
  refine ⟨w,List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
  · apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨c,candidate_mem hc,rfl⟩
  · unfold fastCover at h
    rw [cols_eq, scan_as_residual] at h
    change (residuals (k+1) (oldCols (ws ++ [w])) (~~~(0 : Word))).any (· == 0) = true at h
    have he : oldCols (ws ++ [w]) = oldCols ws ++ [w.1 ^^^ w.2] := by simp [oldCols]
    rw [he,resid_append] at h
    have hz : ~~~(0 : Word) = BitVec.allOnes 110 := rfl
    rw [hz] at h
    simpa only [Bool.or_eq_true, List.any_eq_true, List.mem_eraseDups, BitVec.not_zero] using h

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def Oriented (cs : List Choice) (ws : List Wire) (out : Nat) : Prop :=
  ∀ t : Fin 110, (runChoices cs (sample ws t false)).getD out false = true ∧
    (runChoices cs (sample ws t true)).getD out false = false

theorem distinguished_of_oriented {cs : List Choice} {ws : List Wire} {out : Nat}
    (h : Oriented cs ws out) : distinguished cs ws out := by
  intro t
  rw [(h t).1,(h t).2]
  decide

def attainable (k : Nat) (ws : List Wire) := ∃ cs : List Choice, ∃ o : Nat,
  cs.length = k ∧ Valid ws.length cs ∧ Oriented cs ws o

def wireMap (old new : List Wire) : Nat → Nat
  | 0 => 0
  | i+1 =>
    if hi : i < old.length then
      if old[i] ∈ new then new.idxOf old[i] + 1 else 0
    else 0

private theorem wireMap_ok (old new : List Wire) : SourceMap old.length new.length (wireMap old new) := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro q
    cases q with
    | zero => simp [wireMap]
    | succ i =>
      simp only [wireMap]
      split
      · split
        · next h => have := List.idxOf_lt_length_iff.mpr h; omega
        · omega
      · omega
  · intro i hi
    simp [wireMap, Nat.not_lt.mpr hi]

private theorem pull_sample {old new : List Wire} {i : Nat} (hi : i < old.length)
    (hm : old[i] ∈ new ∨ old[i] = (0,0)) (t : Fin 110) (s : Bool) :
    (pull (wireMap old new) old.length (sample new t s)).getD i false =
      (sample old t s).getD i false := by
  rw [pull_at _ _ _ _ hi]
  by_cases hin : old[i] ∈ new
  · cases s <;> simp [wireMap, hi, hin, CircuitSatBridge.read, sample,
      List.getElem?_idxOf hin]
  · have hz := hm.resolve_left hin
    have hmap : wireMap old new (i+1) = 0 := by simp only [wireMap, dif_pos hi, if_neg hin]
    rw [hmap]
    cases s <;> simp [CircuitSatBridge.read, sample, hi, hz]

theorem project_suffix {cs : List Choice} {old new : List Wire} {out : Nat} {s : Finset Nat}
    (hs : s ⊆ Finset.range old.length) (hd : Oriented cs old out)
    (det : ∀ x y : List Bool, x.length = old.length → y.length = old.length → agrees s x y →
      (runChoices cs x).getD out false = (runChoices cs y).getD out false)
    (hnew : ∀ i, (hi : i ∈ s) → old[i]'(Finset.mem_range.mp (hs hi)) ∈ new ∨
      old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)) : attainable cs.length new := by
  let f := wireMap old new
  let moved := transfer f old.length new.length cs
  let q := moved.2 (out+1)
  have hf := wireMap_ok old new
  have he (t : Fin 110) (b : Bool) :
      read (runChoices moved.1 (sample new t b)) q =
      (runChoices cs (sample old t b)).getD out false := by
    rw [show read (runChoices moved.1 (sample new t b)) q =
      (runChoices cs (pull f old.length (sample new t b))).getD out false from
      transfer_pull cs hf _ (by simp [sample]) out]
    have hcol (i : Nat) (hi : i ∈ s) := pull_sample (Finset.mem_range.mp (hs hi)) (hnew i hi) t b
    exact det _ _ (pull_len ..) (by simp [sample]) hcol
  have hn : q ≠ 0 := by
    intro hz
    apply distinguished_of_oriented hd 0
    rw [← he, ← he, hz]
    rfl
  obtain ⟨hv,hl⟩ := transfer_valid cs f old.length new.length hf.1
  refine ⟨moved.1,q-1,hl,hv,?_⟩
  intro t
  have hq (x : List Bool) : x.getD (q-1) false = read x q := by
    cases h : q with
    | zero => contradiction
    | succ i => rfl
  change _ = true ∧ _ = false
  rw [hq, hq, he, he]
  exact hd t

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def key (w : Wire) : Nat := (w.1.toNat <<< 110) + w.2.toNat

def live (ws : List Wire) : List Wire :=
  ((ws.filter (· != (0,0))).dedup).insertionSort (fun a b => key a ≤ key b)

theorem mem_live (ws : List Wire) (w : Wire) :
    w ∈ live ws ↔ w ∈ ws ∧ w ≠ (0,0) := by simp [live]

theorem live_nodup (ws : List Wire) : (live ws).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup _)

def coversAll (ws : List Wire) : Bool := ((oldCols ws).foldr (· ||| ·) 0) == BitVec.allOnes 110

theorem covers_of_attainable {k : Nat} {ws : List Wire} (h : attainable k ws) :
    coversAll ws = true := by
  obtain ⟨cs,out,_,_,hd⟩ := h
  obtain ⟨s, _, _, hu⟩ := of_decide_eq_true (suffix_cover cs ws out (distinguished_of_oriented hd))
  apply beq_iff_eq.mpr
  have he : (List.range ws.length).map (delta ws) = oldCols ws := by
    apply List.ext_getElem
    · simp [oldCols]
    · intro i _ hi
      have hj : i < ws.length := by simpa [oldCols] using hi
      simp [oldCols,delta,hj]
  rw [← he]
  change unionD ws (List.range ws.length) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_allOnes, decide_eq_true hi]
  apply (bit_union _ _ ⟨i,hi⟩).mpr
  have hb := congrArg (fun (v : Word) => v.getLsbD i) hu
  simp only [BitVec.getLsbD_allOnes, decide_eq_true hi] at hb
  obtain ⟨j,hj,hd⟩ := (bit_union _ _ ⟨i,hi⟩).mp hb
  exact ⟨j,(List.mem_filter.mp hj).1,hd⟩

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

def choose (n : Nat) (ws : List Wire) := List.sublistsLen (min n (live ws).length) (live ws)

private theorem pick_support {ws : List Wire} {indices : Finset Nat} {k : Nat}
    (hi : indices ⊆ Finset.range ws.length) (hk : indices.card ≤ k) :
    ∃ ys ∈ choose k ws, ∀ i, (h : i ∈ indices) →
      ws[i]'(Finset.mem_range.mp (hi h)) ∈ ys ∨ ws[i]'(Finset.mem_range.mp (hi h)) = (0,0) := by
  let pool := live ws
  let need := (indices.image (fun i => ws.getD i (0,0))).erase (0,0)
  have hh : need ⊆ pool.toFinset := by
    intro v hv
    obtain ⟨hn,hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hv
    have hl := Finset.mem_range.mp (hi h)
    apply List.mem_toFinset.mpr
    apply (mem_live ..).mpr
    exact ⟨by simp [hl],hn⟩
  have hn : need.card ≤ k := (Finset.card_erase_le ..).trans (Finset.card_image_le.trans hk)
  have hp : pool.toFinset.card = pool.length := List.toFinset_card_of_nodup (live_nodup ws)
  obtain ⟨big,ha,hb,hc⟩ := Finset.exists_subsuperset_card_eq hh
    (le_min hn (hp ▸ Finset.card_le_card hh)) (by rw [hp]; exact min_le_right _ _)
  let ys := pool.filter (fun v => v ∈ big)
  have hy : ys.toFinset = big := by
    ext v
    simp only [ys, List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hb h))
  refine ⟨ys, List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩, ?_⟩
  · rw [← List.toFinset_card_of_nodup ((live_nodup ws).filter _),hy,hc]
  · intro i h
    by_cases hz : ws[i]'(Finset.mem_range.mp (hi h)) = (0,0)
    · exact Or.inr hz
    · left
      apply List.mem_toFinset.mp
      rw [hy]
      exact ha (Finset.mem_erase.mpr ⟨hz,Finset.mem_image.mpr
        ⟨i,h,by simp [Finset.mem_range.mp (hi h)]⟩⟩)

def wordDelta (w : Wire) := w.1 ^^^ w.2
def covered (ys : List Wire) : Word := (ys.map wordDelta).foldr (· ||| ·) 0

private theorem covered_live (ws : List Wire) : covered (live ws) = covered ws := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have mem (ys : List Wire) :
      (covered ys).getLsbD i = true ↔ ∃ w ∈ ys, (wordDelta w).getLsbD i = true := by
    induction ys with
    | nil => simp [covered]
    | cons w ys ih =>
      change (wordDelta w ||| covered ys).getLsbD i = true ↔ _
      simp only [BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
  apply Bool.eq_iff_iff.mpr
  rw [mem,mem]
  constructor
  · rintro ⟨w,hw,hd⟩
    exact ⟨w,((mem_live ..).mp hw).1,hd⟩
  · rintro ⟨w,hw,hd⟩
    refine ⟨w, (mem_live ..).mpr ⟨hw,?_⟩,hd⟩
    rintro rfl
    simp [wordDelta] at hd

def gateValues (ws : List Wire) := ((candidates ws.length).map (evalW · ws)).eraseDups

def fastChildren (ws : List Wire) (k : Nat) : List (List Wire) :=
  let gs := gateValues ws
  let keep := (choose (k+1) ws).filter coversAll
  let added := (choose k ws).flatMap fun ys =>
    let old := covered ys
    (gs.filter (fun w => (wordDelta w ||| old) == BitVec.allOnes 110)).map
      (fun w => live (w :: ys))
  (keep ++ added).eraseDups

end FreeSupport

namespace FreeSupport
open CircuitSatBridge

theorem fast_complete {ws : List Wire} {k : Nat} (h : attainable (k+1) ws) :
    ∃ zs ∈ fastChildren ws k, attainable k zs := by
  obtain ⟨all,out,hl,hv,hd⟩ := h
  cases all with
  | nil => simp at hl
  | cons c cs =>
    have hk : cs.length = k := by simpa using hl
    let v := evalW c ws
    let old := ws ++ [v]
    have hd' : Oriented cs old out := by
      intro t
      simpa only [show old = extend c ws from rfl,sample_extend,runChoices,List.foldl_cons] using hd t
    obtain ⟨s,hs,hcard,det⟩ := bounded_support cs old.length out
    have hlen : old.length = ws.length + 1 := by simp [old]
    have hs' : s.erase ws.length ⊆ Finset.range ws.length := by
      intro i hi
      obtain ⟨hn,hi⟩ := Finset.mem_erase.mp hi
      have hb := Finset.mem_range.mp (hs hi)
      exact Finset.mem_range.mpr (by omega)
    have hval : v ∈ gateValues ws := by
      apply List.mem_eraseDups.mpr
      exact List.mem_map.mpr ⟨c,candidate_mem hv.1,rfl⟩
    have hread (i : Nat) (hi : i < ws.length) :
        old[i]'(by omega) = ws[i] := List.getElem_append_left hi
    have last : old[ws.length]'(by omega) = v := by simp [old]
    by_cases use : ws.length ∈ s
    · have small : (s.erase ws.length).card ≤ k := by
        rw [Finset.card_erase_of_mem use]; omega
      obtain ⟨ys,hys,hy⟩ := pick_support hs' small
      let zs := live (v :: ys)
      have hat : attainable k zs := by
        rw [← hk]
        apply project_suffix hs hd' det
        intro i hi
        by_cases hz : old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)
        · exact Or.inr hz
        · left
          apply (mem_live ..).mpr
          refine ⟨?_,hz⟩
          by_cases eq : i = ws.length
          · subst i; simp [last]
          · have ins := Finset.mem_erase.mpr ⟨eq,hi⟩
            rw [hread i (Finset.mem_range.mp (hs' ins))] at hz ⊢
            exact List.mem_cons_of_mem _ ((hy _ ins).resolve_right hz)
      have covered' : covered zs = BitVec.allOnes 110 := eq_of_beq (covers_of_attainable hat)
      rw [show zs = live (v :: ys) from rfl, covered_live] at covered'
      refine ⟨zs,List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨ys,hys,List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨hval,?_⟩,rfl⟩⟩)),hat⟩
      exact beq_iff_eq.mpr covered'
    · have small : (s.erase ws.length).card ≤ k+1 :=
        (Finset.card_erase_le ..).trans (hk ▸ hcard)
      obtain ⟨ys,hys,hy⟩ := pick_support hs' small
      have hat : attainable k ys := by
        rw [← hk]
        apply project_suffix hs hd' det
        intro i hi
        have neq : i ≠ ws.length := fun e => use (e ▸ hi)
        have ins := Finset.mem_erase.mpr ⟨neq,hi⟩
        rw [hread i (Finset.mem_range.mp (hs' ins))]
        exact hy _ ins
      exact ⟨ys,List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_filter.mpr
        ⟨hys,covers_of_attainable hat⟩)),hat⟩

end FreeSupport

namespace FreeSupport
def advance (states : List (List Wire)) (k : Nat) := (states.flatMap (fastChildren · k)).eraseDups
theorem advance_complete {states : List (List Wire)} {k : Nat}
    (h : ∃ ws ∈ states, attainable (k+1) ws) : ∃ ys ∈ advance states k, attainable k ys := by
  obtain ⟨ws,hw,ha⟩ := h
  obtain ⟨ys,hy,hb⟩ := fast_complete ha
  exact ⟨ys,List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨ws,hw,hy⟩),hb⟩

def fastExplore (k : Nat) (states : List (List Wire)) : Nat → List (List Wire)
  | 0 => states
  | d+1 => fastExplore (k-1) (advance states (k-1)) d

theorem fastExplore_complete (d k : Nat) (states : List (List Wire)) (hd : d ≤ k)
    (h : ∃ ws ∈ states, attainable k ws) :
    ∃ ws ∈ fastExplore k states d, attainable (k-d) ws := by
  induction d generalizing k states with
  | zero => exact h
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => simpa [fastExplore] using ih k (advance states k) (by omega) (advance_complete h)

theorem fast_exclude {k d : Nat} {ws : List Wire} (hd : d ≤ k)
    (h : fastExplore k [ws] d = []) : ¬ attainable k ws := by
  intro a
  obtain ⟨y,hy,_⟩ := fastExplore_complete d k [ws] hd ⟨ws,by simp,a⟩
  rw [h] at hy
  exact List.not_mem_nil hy
end FreeSupport

namespace CircuitSatBridge

private theorem and_le (a b c d : Bool) (ha : a ≤ c) (hb : b ≤ d) : (a && b) ≤ (c && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all
private theorem or_le (a b c d : Bool) (ha : a ≤ c) (hb : b ≤ d) : (a || b) ≤ (c || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def belowOn (s : Finset Nat) (x y : List Bool) := ∀ i ∈ s, x.getD i false ≤ y.getD i false

theorem bounded_monotone_support (cs : List Choice) (n out : Nat) (hm : ∀ c ∈ cs, IsMonotone c) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ cs.length+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → belowOn s x y →
        (runChoices cs x).getD out false ≤ (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp, fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro x y hx hy _
      change x.getD out false ≤ y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1) (fun g hg => hm _ (List.mem_cons_of_mem _ hg))
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, c.2.2-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ 2 := (Finset.card_filter_le _ _).trans
            ((Finset.card_insert_le _ _).trans (by simp))
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [List.length_cons]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = c.2.2) : read x q ≤ read y q := by
          cases q with
          | zero => exact le_rfl
          | succ q =>
            change x.getD q false ≤ y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have hl := readEq c.2.1 (Or.inl rfl)
          have hr := readEq c.2.2 (Or.inr rfl)
          have hmono := hm c List.mem_cons_self
          have ev : c.eval x ≤ c.eval y := by
            unfold Choice.eval
            cases he : c.1 with
            | lt => exact and_le _ _ _ _ hl hr
            | eq => exact or_le _ _ _ _ hl hr
            | gt => rw [hmono he]; exact le_rfl
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace CircuitSatBridge
def effectiveRight (c : Choice) := match c.1 with
  | .gt => c.2.1
  | _ => c.2.2

def gateCost (c : Choice) := match c.1 with
  | .gt => 0
  | _ => 1

def binaryCount : List Choice → Nat
  | [] => 0
  | c :: cs => gateCost c + binaryCount cs

theorem count_le_length (cs : List Choice) : binaryCount cs ≤ cs.length := by
  induction cs with
  | nil => decide
  | cons c cs ih => cases h : c.1 <;> simp [binaryCount,gateCost,h] <;> omega

theorem count_lt_of_nonmono {cs : List Choice} (hn : ¬ ∀ c ∈ cs, IsMonotone c) :
    binaryCount cs < cs.length := by
  induction cs with
  | nil => simp at hn
  | cons c cs ih =>
    by_cases h : IsMonotone c
    · have h' := ih (fun hm => hn (by simpa using And.intro h hm))
      cases he : c.1 <;> simp [binaryCount,gateCost,he] <;> omega
    · have hh := count_le_length cs
      cases he : c.1 <;> simp_all [IsMonotone,gateCost,binaryCount]

theorem bounded_unary_support (cs : List Choice) (n out : Nat) :
    ∃ s : Finset Nat, s ⊆ Finset.range n ∧ s.card ≤ binaryCount cs+1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n → agrees s x y →
        (runChoices cs x).getD out false = (runChoices cs y).getD out false := by
  induction cs generalizing n with
  | nil =>
    by_cases h : out < n
    · exact ⟨{out}, by simpa, by simp [binaryCount], fun x y _ _ ha => ha out (by simp)⟩
    · refine ⟨∅, by simp, by simp [binaryCount], ?_⟩
      intro x y hx hy _
      change x.getD out false = y.getD out false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons c cs ih =>
    obtain ⟨s, hs, hcard, he⟩ := ih (n+1)
    by_cases h : n ∈ s
    · let t := ({c.2.1-1, effectiveRight c-1} : Finset Nat).filter (· < n)
      refine ⟨s.erase n ∪ t, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with h₁|h₂
        · obtain ⟨hne,his⟩ := Finset.mem_erase.mp h₁
          have hh := Finset.mem_range.mp (hs his)
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp h₂).2
      · have ht : t.card ≤ gateCost c + 1 := by
          apply (Finset.card_filter_le _ _).trans
          cases hop : c.1 <;> simp [effectiveRight, gateCost, hop] <;>
            exact (Finset.card_insert_le _ _).trans (by simp)
        have hb := Finset.card_union_le (s.erase n) t
        rw [Finset.card_erase_of_mem h] at hb
        have hp := Finset.card_pos.mpr ⟨n,h⟩
        simp only [binaryCount]
        omega
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have readEq (q : Nat) (hq : q = c.2.1 ∨ q = effectiveRight c) : read x q = read y q := by
          cases q with
          | zero => rfl
          | succ q =>
            change x.getD q false = y.getD q false
            by_cases hq' : q < n
            · apply ha
              apply Finset.mem_union_right
              apply Finset.mem_filter.mpr
              refine ⟨?_, hq'⟩
              rcases hq with hq|hq <;> simp [← hq]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        by_cases hi' : i = n
        · subst i
          have ev : c.eval x = c.eval y := by
            unfold Choice.eval
            have hl := readEq _ (Or.inl rfl)
            have hr := readEq _ (Or.inr rfl)
            cases hop : c.1 <;> simp_all [effectiveRight]
          convert ev using 1
          · rw [← hx]; simp
          · rw [← hy]; simp
        · have hh := Finset.mem_range.mp (hs hi)
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact ha _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hi',hi⟩))
    · refine ⟨s, ?_, by simp only [binaryCount]; omega, ?_⟩
      · intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        exact Finset.mem_range.mpr (by omega)
      · intro x y hx hy ha
        apply he _ _ (by simp [hx]) (by simp [hy])
        intro i hi
        have hh := Finset.mem_range.mp (hs hi)
        have hn : i ≠ n := fun e => h (e ▸ hi)
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ha _ hi

end CircuitSatBridge

namespace SharpSupport
open FreeSupport CircuitSatBridge
private theorem pick_support {ws : List Wire} {indices : Finset Nat} {k : Nat}
    (hi : indices ⊆ Finset.range ws.length) (hk : indices.card ≤ k) :
    ∃ ys ∈ choose k ws, ∀ i, (h : i ∈ indices) →
      ws[i]'(Finset.mem_range.mp (hi h)) ∈ ys ∨ ws[i]'(Finset.mem_range.mp (hi h)) = (0,0) := by
  let pool := live ws
  let need := (indices.image (fun i => ws.getD i (0,0))).erase (0,0)
  have hh : need ⊆ pool.toFinset := by
    intro v hv
    obtain ⟨hn,hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hv
    have hl := Finset.mem_range.mp (hi h)
    apply List.mem_toFinset.mpr
    apply (mem_live ..).mpr
    exact ⟨by simp [hl],hn⟩
  have hn : need.card ≤ k := (Finset.card_erase_le ..).trans (Finset.card_image_le.trans hk)
  have hp : pool.toFinset.card = pool.length := List.toFinset_card_of_nodup (live_nodup ws)
  obtain ⟨big,ha,hb,hc⟩ := Finset.exists_subsuperset_card_eq hh
    (le_min hn (hp ▸ Finset.card_le_card hh)) (by rw [hp]; exact min_le_right _ _)
  let ys := pool.filter (fun v => v ∈ big)
  have hy : ys.toFinset = big := by
    ext v
    simp only [ys, List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact and_iff_right_of_imp (fun h => List.mem_toFinset.mp (hb h))
  refine ⟨ys, List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩, ?_⟩
  · rw [← List.toFinset_card_of_nodup ((live_nodup ws).filter _),hy,hc]
  · intro i h
    by_cases hz : ws[i]'(Finset.mem_range.mp (hi h)) = (0,0)
    · exact Or.inr hz
    · left
      apply List.mem_toFinset.mp
      rw [hy]
      exact ha (Finset.mem_erase.mpr ⟨hz,Finset.mem_image.mpr
        ⟨i,h,by simp [Finset.mem_range.mp (hi h)]⟩⟩)

def diff (ord : Bool) (w : Wire) : Word :=
  if ord then w.1 &&& ~~~w.2 else w.1 ^^^ w.2

def coverage (ord : Bool) (ws : List Wire) : Word := (ws.map (diff ord)).foldr (· ||| ·) 0

private theorem bit_cover (ord : Bool) (ws : List Wire) (t : Fin 110) :
    (coverage ord ws).getLsbD t = true ↔ ∃ w ∈ ws, (diff ord w).getLsbD t = true := by
  induction ws with
  | nil => simp [coverage]
  | cons w ws ih =>
    change (diff ord w ||| coverage ord ws).getLsbD t = true ↔ _
    simp only [BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

def childrenUsing (ws : List Wire) (slots : Nat) (ord : Bool) : List (List Wire) :=
  let keep := (choose slots ws).filter (fun ys => coverage ord ys == BitVec.allOnes 110)
  let add := if slots = 0 then [] else (choose (slots-1) ws).flatMap fun ys =>
    let old := coverage ord ys
    ((gateValues ws).filter (fun w => (diff ord w ||| old) == BitVec.allOnes 110)).map
      (fun w => live (w :: ys))
  keep ++ add

private theorem select_support {ws : List Wire} {c : Choice} {cs : List Choice} {out slots : Nat}
    {ord : Bool} (hleg : c.Legal ws.length)
    (hd : Oriented cs (extend c ws) out) {s : Finset Nat}
    (hs : s ⊆ Finset.range (extend c ws).length) (bound : s.card ≤ slots)
    (det : ∀ x y : List Bool, x.length = (extend c ws).length → y.length = (extend c ws).length →
      agrees s x y → (runChoices cs x).getD out false = (runChoices cs y).getD out false)
    (bits : ∀ t : Fin 110, ∃ i, ∃ hi : i ∈ s,
      (diff ord ((extend c ws)[i]'(Finset.mem_range.mp (hs hi)))).getLsbD t = true) :
    ∃ zs ∈ childrenUsing ws slots ord, attainable cs.length zs := by
  let v := evalW c ws
  let old := extend c ws
  have hlen : old.length = ws.length+1 := by simp [old,extend]
  change s ⊆ Finset.range old.length at hs
  have hs' : s.erase ws.length ⊆ Finset.range ws.length := by
    intro i hi
    obtain ⟨hn,hi⟩ := Finset.mem_erase.mp hi
    have hb := Finset.mem_range.mp (hs hi)
    exact Finset.mem_range.mpr (by omega)
  have hval : v ∈ gateValues ws := List.mem_eraseDups.mpr (List.mem_map.mpr ⟨c,candidate_mem hleg,rfl⟩)
  have hread (i : Nat) (hi : i < ws.length) :
      old[i]'(by omega) = ws[i] := List.getElem_append_left hi
  have last : old[ws.length]'(by omega) = v := by simp [old,extend,v]
  have cov (ys : List Wire)
      (hc : ∀ i, (hi : i ∈ s) → old[i]'(Finset.mem_range.mp (hs hi)) ∈ ys ∨
        old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)) : coverage ord ys = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_allOnes,decide_eq_true hj]
    obtain ⟨i,hi,hbit⟩ := bits ⟨j,hj⟩
    change (diff ord (old[i]'(Finset.mem_range.mp (hs hi)))).getLsbD j = true at hbit
    rcases hc i hi with hm|hz
    · exact (bit_cover _ _ ⟨j,hj⟩).mpr ⟨_,hm,hbit⟩
    · rw [hz] at hbit
      cases ord <;> simp [diff] at hbit
  by_cases use : ws.length ∈ s
  · have pos := Finset.card_pos.mpr ⟨_,use⟩
    have small : (s.erase ws.length).card ≤ slots-1 := by rw [Finset.card_erase_of_mem use]; omega
    obtain ⟨ys,hys,hy⟩ := pick_support hs' small
    have hc (i : Nat) (hi : i ∈ s) :
        old[i]'(Finset.mem_range.mp (hs hi)) ∈ v :: ys ∨ old[i]'(Finset.mem_range.mp (hs hi)) = (0,0) := by
      by_cases eq : i = ws.length
      · subst i; simp [last]
      · have ins := Finset.mem_erase.mpr ⟨eq,hi⟩
        rw [hread i (Finset.mem_range.mp (hs' ins))]
        exact (hy i ins).imp (List.mem_cons_of_mem _) id
    refine ⟨live (v :: ys), ?_, project_suffix hs hd det ?_⟩
    · apply List.mem_append_right
      simp only [if_neg (show slots ≠ 0 by omega)]
      exact List.mem_flatMap.mpr ⟨ys,hys,List.mem_map.mpr
        ⟨v,List.mem_filter.mpr ⟨hval,beq_iff_eq.mpr (cov _ hc)⟩,rfl⟩⟩
    · intro i hi
      by_cases hz : old[i]'(Finset.mem_range.mp (hs hi)) = (0,0)
      · exact Or.inr hz
      · exact Or.inl ((mem_live ..).mpr ⟨(hc _ hi).resolve_right hz,hz⟩)
  · obtain ⟨ys,hys,hy⟩ := pick_support hs' ((Finset.card_erase_le ..).trans bound)
    have hc (i : Nat) (hi : i ∈ s) : old[i]'(Finset.mem_range.mp (hs hi)) ∈ ys ∨
        old[i]'(Finset.mem_range.mp (hs hi)) = (0,0) := by
      have neq : i ≠ ws.length := fun e => use (e ▸ hi)
      have ins := Finset.mem_erase.mpr ⟨neq,hi⟩
      rw [hread i (Finset.mem_range.mp (hs' ins))]
      exact hy _ ins
    exact ⟨ys,List.mem_append_left _ (List.mem_filter.mpr ⟨hys,beq_iff_eq.mpr (cov _ hc)⟩),
      project_suffix hs hd det hc⟩

def children (ws : List Wire) (k : Nat) :=
  childrenUsing ws k false ++ childrenUsing ws (k+1) true

theorem complete {ws : List Wire} {k : Nat} (ha : attainable (k+1) ws) :
    ∃ zs ∈ children ws k, attainable k zs := by
  obtain ⟨all,out,hlen,hv,hd⟩ := ha
  cases all with
  | nil => simp at hlen
  | cons c cs =>
    have hk : cs.length = k := by simpa using hlen
    subst k
    let old := extend c ws
    have ho : Oriented cs old out := by
      intro t
      simpa only [old,sample_extend,runChoices,List.foldl_cons] using hd t
    by_cases hm : ∀ g ∈ cs, IsMonotone g
    · obtain ⟨s,hs,hb,mono⟩ := bounded_monotone_support cs old.length out hm
      have eqdet (x y : List Bool) (hx : x.length = old.length) (hy : y.length = old.length)
          (h : agrees s x y) := le_antisymm (mono x y hx hy (fun i hi => (h i hi).le))
            (mono y x hy hx (fun i hi => (h i hi).ge))
      obtain ⟨zs,hz,hatt⟩ := select_support (ord := true) hv.1 ho hs hb eqdet (by
        intro t
        by_contra! hn
        have bad := mono (sample old t false) (sample old t true) (by simp [sample]) (by simp [sample]) (by
          intro i hi
          have hh := hn i hi
          have hin := Finset.mem_range.mp (hs hi)
          simp [sample,List.getElem?_eq_getElem hin]
          simpa [diff, t.isLt, Bool.le_iff_imp] using hh)
        rw [(ho t).1,(ho t).2] at bad
        contradiction)
      exact ⟨zs,List.mem_append_right _ hz,hatt⟩
    · obtain ⟨s,hs,hc,det⟩ := bounded_unary_support cs old.length out
      have hlt := count_lt_of_nonmono hm
      obtain ⟨zs,hz,hatt⟩ := select_support (ord := false) hv.1 ho hs (show s.card ≤ cs.length by omega) det (by
        intro t
        by_contra! hn
        apply distinguished_of_oriented ho t
        apply det _ _ (by simp [sample]) (by simp [sample])
        intro i hi
        have hh := hn i hi
        have hin := Finset.mem_range.mp (hs hi)
        simpa [sample,List.getElem?_eq_getElem hin,diff] using hh)
      exact ⟨zs,List.mem_append_left _ hz,hatt⟩
end SharpSupport

namespace FreeSupport
open CircuitSatBridge

theorem zero_wire {ws : List Wire} (ha : attainable 0 ws) :
    (BitVec.allOnes 110, (0 : Word)) ∈ ws := by
  obtain ⟨cs,out,hlen,_,h⟩ := ha
  have hnil := List.length_eq_zero_iff.mp hlen
  subst cs
  have hout : out < ws.length := by
    by_contra! hbad
    have hh := (h 0).1
    change (sample ws 0 false).getD out false = true at hh
    rw [List.getD_eq_default _ _ (by simpa [sample] using hbad)] at hh
    contradiction
  have hl : ws[out].1 = BitVec.allOnes 110 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_allOnes,decide_eq_true hi]
    have hh := (h ⟨i,hi⟩).1
    simpa [runChoices,sample,List.getElem?_eq_getElem hout] using hh
  have hr : ws[out].2 = (0 : Word) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := (h ⟨i,hi⟩).2
    simpa [runChoices,sample,List.getElem?_eq_getElem hout] using hh
  have he : ws[out] = (BitVec.allOnes 110, (0 : Word)) := Prod.ext hl hr
  exact he ▸ List.getElem_mem hout

end FreeSupport

namespace FourCheck
open FreeSupport CircuitSatBridge PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def excluded : Nat → List Wire → Bool
  | 0, ws => !(ws.contains (BitVec.allOnes 110, (0 : Word)))
  | k+1, ws => (SharpSupport.children ws k).eraseDups.all (excluded k)

theorem excluded_sound (k : Nat) (ws : List Wire) (h : excluded k ws) : ¬ attainable k ws := by
  induction k generalizing ws with
  | zero =>
    intro ha
    have hw := List.contains_iff_mem.mpr (zero_wire ha)
    change (!(ws.contains (BitVec.allOnes 110, (0 : Word)))) = true at h
    rw [hw] at h
    contradiction
  | succ k ih =>
    intro ha
    obtain ⟨zs, hz, hza⟩ := SharpSupport.complete ha
    exact ih zs (List.all_eq_true.mp h zs (List.mem_eraseDups.mpr hz)) hza

def graph (m : Nat) (i j : Fin 4) := m.testBit (4*i.val+j.val)

def Samples (ws : List Wire) (m : Nat) :=
  ∀ t : Fin 110, ∀ b : Bool, ∃ i j : Fin 4, sample ws t b = oneEach i j ∧ graph m i j = !b

theorem attainable_of_circuit (k : Nat) (m : Nat) (ws : List Wire) (hw : ws.length = 8)
    (hp : Samples ws m) (c : Circuit) (hc : FanInTwo c) (hs : c.size ≤ k)
    (hr : Represents (graph m) c) : attainable k ws := by
  cases k with
  | zero =>
    have hn : c.gates = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
    refine ⟨[],c.output,rfl,trivial,?_⟩
    intro t
    have side (b : Bool) : (runChoices [] (sample ws t b)).getD c.output false = !b := by
      obtain ⟨i,j,he,hg⟩ := hp t b
      rw [he]
      have hh := (hr i j).trans hg
      simpa [Circuit.eval, Circuit.wires, hn, runChoices] using hh
    exact ⟨side false,side true⟩
  | succ k =>
    obtain ⟨cs,hl,hv,he⟩ := fixed_slots k 8 c.output c.gates hc hs
    refine ⟨cs,8+k,hl,hw ▸ hv,?_⟩
    intro t
    have side (b : Bool) : (runChoices cs (sample ws t b)).getD (8+k) false = !b := by
      obtain ⟨i,j,ha,hb⟩ := hp t b
      rw [ha]
      exact (he _ (by simp [oneEach])).trans ((hr i j).trans hb)
    exact ⟨side false,side true⟩

theorem refute (k m : Nat) (ws : List Wire) (hw : ws.length = 8) (hp : Samples ws m)
    (hx : excluded k ws) :
    ¬ ∃ c : Circuit, FanInTwo c ∧ c.size ≤ k ∧ Represents (graph m) c := by
  rintro ⟨c,hc,hs,hr⟩
  exact excluded_sound k ws hx (attainable_of_circuit k m ws hw hp c hc hs hr)
end FourCheck
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitSatBridge FreeSupport

def target (x : Fin 9 → Bool) : Bool := ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
def test (t : Fin 110) (b : Bool) : Fin 9 → Bool :=
  let pts : List Nat := if b then [272, 257, 17, 160, 129, 33, 264, 258, 10, 96, 66, 34, 136, 132, 12, 80, 68, 20, 151, 438, 121, 63, 466, 504, 79, 438, 63, 219, 365, 455, 484, 457, 365, 484, 455, 438, 186, 63, 151, 219, 365, 316, 365, 63, 455, 79, 79, 151, 295, 455, 484, 316, 438, 295, 316, 63, 186, 466, 151, 121, 316, 457, 466, 121, 79, 484, 457, 438, 295, 365, 484, 295, 466, 466, 457, 63, 79, 438, 219, 455, 438, 79, 186, 457, 484, 484, 186, 121, 295, 455, 151, 316, 504, 79, 151, 365, 219, 457, 121, 484, 151, 295, 121, 316, 466, 295, 186, 79, 219, 466] else [273, 273, 273, 161, 161, 161, 266, 266, 266, 98, 98, 98, 140, 140, 140, 84, 84, 84, 84, 273, 266, 266, 84, 266, 266, 140, 273, 84, 140, 266, 161, 266, 161, 273, 84, 84, 84, 140, 98, 273, 266, 273, 84, 98, 140, 140, 98, 161, 84, 98, 84, 266, 266, 266, 98, 161, 266, 140, 273, 161, 140, 84, 273, 98, 84, 266, 98, 161, 273, 98, 492, 423, 470, 498, 489, 191, 335, 502, 223, 487, 446, 95, 190, 459, 486, 500, 442, 123, 359, 471, 159, 380, 505, 207, 407, 493, 475, 461, 249, 485, 183, 303, 125, 317, 467, 311, 187, 111, 251, 474]
  fun i => (pts.getD t.val 0).testBit i.val
def wires : List FreeSupport.Wire := [((563782090815 <<< 0) + (947447955586 <<< 40) + (536868746 <<< 80), (986721812534 <<< 0) + (947940795389 <<< 40) + (444065674 <<< 80)), ((277590577088 <<< 0) + (1080830294601 <<< 40) + (1060202463 <<< 80), (1083127369088 <<< 0) + (1080608404472 <<< 40) + (1060202311 <<< 80)), ((258138959872 <<< 0) + (1072688137524 <<< 40) + (184217399 <<< 80), (478740963328 <<< 0) + (794486439935 <<< 40) + (179892019 <<< 80)), ((140453638592 <<< 0) + (396245547057 <<< 40) + (1021820111 <<< 80), (762854789440 <<< 0) + (395769923695 <<< 40) + (482851022 <<< 80)), ((678811369479 <<< 0) + (459853268230 <<< 40) + (936730343 <<< 80), (1065403449349 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80)), ((280246619704 <<< 0) + (751292695240 <<< 40) + (519870965 <<< 80), (254857972264 <<< 0) + (176003087631 <<< 40) + (116169205 <<< 80)), ((395275898368 <<< 0) + (1062561924940 <<< 40) + (961526714 <<< 80), (584011843072 <<< 0) + (925161358965 <<< 40) + (961524410 <<< 80)), ((143109681208 <<< 0) + (1029854363824 <<< 40) + (891287165 <<< 80), (957421989912 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80)), ((561126048199 <<< 0) + (789506766851 <<< 40) + (598465401 <<< 80), (68497703107 <<< 0) + (721528454935 <<< 40) + (598383417 <<< 80)), ((535729536960 <<< 0) + (152063672189 <<< 40) + (536873077 <<< 80), (112789815241 <<< 0) + (151570832386 <<< 40) + (629676149 <<< 80)), ((274877910528 <<< 0) + (732904309320 <<< 40) + (506462677 <<< 80), (240621455360 <<< 0) + (174348939528 <<< 40) + (102760773 <<< 80))]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem samples : ∀ t : Fin 110, ∀ b : Bool,
    sample wires t b = run [⟨.not, [0]⟩, ⟨.and, [1, 5]⟩] (List.ofFn (test t b)) ∧ target (test t b) = !b := by decide +kernel

theorem attainable_suffix (rest : List Gate) (o : Nat)
    (hs : ∀ g ∈ rest, Supported g) (hlen : rest.length ≤ 10)
    (hfun : ∀ x : Fin 9 → Bool, (run ([⟨.not, [0]⟩, ⟨.and, [1, 5]⟩] ++ rest) (List.ofFn x)).getD o false = target x) :
    attainable 10 wires := by
  obtain ⟨cs,hl,hv,he⟩ := fixed_slots 9 11 o rest hs hlen
  refine ⟨cs,20,hl,?_,?_⟩
  · exact hv
  intro t
  have h (b : Bool) :
      (runChoices cs (sample wires t b)).getD 20 false = !b := by
    rw [(samples t b).1, he]
    · exact (hfun (test t b)).trans (samples t b).2
    · simp [run]
  exact ⟨h false, h true⟩

theorem rejectNil (k : Nat) : ∀ t ∈ ([] : List (List FreeSupport.Wire)), ¬ FreeSupport.attainable k t := by simp

theorem rejectCons {k : Nat} {w : List FreeSupport.Wire} {ws : List (List FreeSupport.Wire)}
    (hw : ¬ FreeSupport.attainable k w) (hs : ∀ t ∈ ws, ¬ FreeSupport.attainable k t) :
    ∀ t ∈ w :: ws, ¬ FreeSupport.attainable k t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | hh
  · exact hw
  · exact hs t hh

theorem stepCover {k : Nat} {ws : List FreeSupport.Wire} (dst : List (List FreeSupport.Wire))
    (hn : (SharpSupport.children ws k).all (fun t => dst.contains t) = true)
    (he : ∀ t ∈ dst, ¬ FreeSupport.attainable k t) : ¬ FreeSupport.attainable (k+1) ws := by
  intro h
  obtain ⟨t, ht, ha⟩ := SharpSupport.complete h
  exact he t (List.contains_iff_mem.mp (List.all_eq_true.mp hn t ht)) ha
def wire0 : FreeSupport.Wire := ((274877910528 <<< 0) + (696397087304 <<< 40) + (402653584 <<< 80), (0 <<< 0) + (0 <<< 40) + (0 <<< 80))
def wire1 : FreeSupport.Wire := ((137740972032 <<< 0) + (1003949785136 <<< 40) + (1762869 <<< 80), (336652410880 <<< 0) + (688436549264 <<< 40) + (1590833 <<< 80))
def wire2 : FreeSupport.Wire := ((274877910528 <<< 0) + (714650698312 <<< 40) + (407673264 <<< 80), (14236516864 <<< 0) + (1653081093 <<< 40) + (5017776 <<< 80))
def wire3 : FreeSupport.Wire := ((2712666560 <<< 0) + (87006722049 <<< 40) + (547592265 <<< 80), (6719275072 <<< 0) + (17787013127 <<< 40) + (8558600 <<< 80))
def wire4 : FreeSupport.Wire := ((258138959872 <<< 0) + (142827717940 <<< 40) + (2101 <<< 80), (44057714688 <<< 0) + (138681539586 <<< 40) + (8914993 <<< 80))
def wire5 : FreeSupport.Wire := ((120397987840 <<< 0) + (450990441732 <<< 40) + (47205927 <<< 80), (446780276736 <<< 0) + (171934275722 <<< 40) + (9456641 <<< 80))
def wire6 : FreeSupport.Wire := ((258138959872 <<< 0) + (1003968660788 <<< 40) + (47902263 <<< 80), (474160701440 <<< 0) + (722797387418 <<< 40) + (9981489 <<< 80))
def wire7 : FreeSupport.Wire := ((821921050687 <<< 0) + (18681333174 <<< 40) + (13539360 <<< 80), (16384258687 <<< 0) + (18903223303 <<< 40) + (13539512 <<< 80))
def wire8 : FreeSupport.Wire := ((0 <<< 0) + (586263035904 <<< 40) + (506462592 <<< 80), (137508159488 <<< 0) + (36775698696 <<< 40) + (35651840 <<< 80))
def wire9 : FreeSupport.Wire := ((0 <<< 0) + (697932185600 <<< 40) + (35651921 <<< 80), (34393817088 <<< 0) + (139989102848 <<< 40) + (35651841 <<< 80))
def wire10 : FreeSupport.Wire := ((0 <<< 0) + (723701989376 <<< 40) + (170918165 <<< 80), (171901976576 <<< 0) + (174348873992 <<< 40) + (35651841 <<< 80))
def wire11 : FreeSupport.Wire := ((558413381639 <<< 0) + (638075535362 <<< 40) + (61592328 <<< 80), (24427626498 <<< 0) + (569957688085 <<< 40) + (35816200 <<< 80))
def wire12 : FreeSupport.Wire := ((5368709176 <<< 0) + (603577680000 <<< 40) + (519868800 <<< 80), (142072610848 <<< 0) + (37321482509 <<< 40) + (40141184 <<< 80))
def wire13 : FreeSupport.Wire := ((563782090815 <<< 0) + (672570048642 <<< 40) + (536859528 <<< 80), (161936834594 <<< 0) + (604326372125 <<< 40) + (40272776 <<< 80))
def wire14 : FreeSupport.Wire := ((280246619704 <<< 0) + (751292695240 <<< 40) + (519870896 <<< 80), (151744676384 <<< 0) + (38428779789 <<< 40) + (40669616 <<< 80))
def wire15 : FreeSupport.Wire := ((561126048199 <<< 0) + (639182911491 <<< 40) + (598465353 <<< 80), (24436015170 <<< 0) + (569958755095 <<< 40) + (44210952 <<< 80))
def wire16 : FreeSupport.Wire := ((0 <<< 0) + (724775731200 <<< 40) + (184060213 <<< 80), (186129055744 <<< 0) + (175994109199 <<< 40) + (44599601 <<< 80))
def wire17 : FreeSupport.Wire := ((0 <<< 0) + (763430436864 <<< 40) + (44747569 <<< 80), (66337636352 <<< 0) + (691390152471 <<< 40) + (44600113 <<< 80))
def wire18 : FreeSupport.Wire := ((0 <<< 0) + (716185796608 <<< 40) + (44603761 <<< 80), (48629284864 <<< 0) + (141634338055 <<< 40) + (44603697 <<< 80))
def wire19 : FreeSupport.Wire := ((0 <<< 0) + (34359738368 <<< 40) + (471859397 <<< 80), (206227636224 <<< 0) + (34359836680 <<< 40) + (67108932 <<< 80))
def wire20 : FreeSupport.Wire := ((0 <<< 0) + (732291923968 <<< 40) + (336592981 <<< 80), (103113293824 <<< 0) + (137573240832 <<< 40) + (67108933 <<< 80))
def wire21 : FreeSupport.Wire := ((274877910528 <<< 0) + (146641273416 <<< 40) + (85 <<< 80), (103113295872 <<< 0) + (137573240832 <<< 40) + (67108933 <<< 80))
def wire22 : FreeSupport.Wire := ((0 <<< 0) + (180388626432 <<< 40) + (370147525 <<< 80), (240621453312 <<< 0) + (171933011976 <<< 40) + (67108933 <<< 80))
def wire23 : FreeSupport.Wire := ((5368709176 <<< 0) + (750680309888 <<< 40) + (337416309 <<< 80), (112785358856 <<< 0) + (138680538112 <<< 40) + (67637365 <<< 80))
def wire24 : FreeSupport.Wire := ((143109681208 <<< 0) + (1029854363824 <<< 40) + (337573493 <<< 80), (405380276232 <<< 0) + (688436614800 <<< 40) + (68703861 <<< 80))
def wire25 : FreeSupport.Wire := ((280246619704 <<< 0) + (751292695240 <<< 40) + (475830773 <<< 80), (117349810696 <<< 0) + (139226321925 <<< 40) + (72126709 <<< 80))
def wire26 : FreeSupport.Wire := ((140453638592 <<< 0) + (1108555825 <<< 40) + (536873029 <<< 80), (68727886144 <<< 0) + (1132546 <<< 40) + (75503684 <<< 80))
def wire27 : FreeSupport.Wire := ((274877910528 <<< 0) + (147715015240 <<< 40) + (2165 <<< 80), (112785361416 <<< 0) + (138681605122 <<< 40) + (76028021 <<< 80))
def wire28 : FreeSupport.Wire := ((0 <<< 0) + (180388626432 <<< 40) + (382998757 <<< 80), (240630890496 <<< 0) + (171942991882 <<< 40) + (79960261 <<< 80))
def wire29 : FreeSupport.Wire := ((0 <<< 0) + (52613349376 <<< 40) + (484743365 <<< 80), (210800476160 <<< 0) + (34906687503 <<< 40) + (79993028 <<< 80))
def wire30 : FreeSupport.Wire := ((274877910528 <<< 0) + (732904309320 <<< 40) + (506462677 <<< 80), (240621455360 <<< 0) + (174348939528 <<< 40) + (102760773 <<< 80))
def wire31 : FreeSupport.Wire := ((280246619704 <<< 0) + (751292695240 <<< 40) + (507286005 <<< 80), (250293520392 <<< 0) + (175456236808 <<< 40) + (103289205 <<< 80))
def wire32 : FreeSupport.Wire := ((280246619704 <<< 0) + (750218953416 <<< 40) + (519868885 <<< 80), (245185906720 <<< 0) + (174894723341 <<< 40) + (107250117 <<< 80))
def wire33 : FreeSupport.Wire := ((704235729407 <<< 0) + (36949702835 <<< 40) + (112215109 <<< 80), (515499784703 <<< 0) + (174350268810 <<< 40) + (112217413 <<< 80))
def wire34 : FreeSupport.Wire := ((280246619704 <<< 0) + (751292695240 <<< 40) + (519870965 <<< 80), (254857972264 <<< 0) + (176003087631 <<< 40) + (116169205 <<< 80))
def wire35 : FreeSupport.Wire := ((420700258296 <<< 0) + (751327509241 <<< 40) + (1056741877 <<< 80), (254857993064 <<< 0) + (176003087631 <<< 40) + (116169205 <<< 80))
def wire36 : FreeSupport.Wire := ((538385579576 <<< 0) + (755607717884 <<< 40) + (519870965 <<< 80), (254858193448 <<< 0) + (176003087631 <<< 40) + (116169205 <<< 80))
def wire37 : FreeSupport.Wire := ((120397987840 <<< 0) + (1036179735812 <<< 40) + (139111218 <<< 80), (31960662016 <<< 0) + (620136236661 <<< 40) + (134783538 <<< 80))
def wire38 : FreeSupport.Wire := ((395275898368 <<< 0) + (1045382055756 <<< 40) + (407546802 <<< 80), (31960662016 <<< 0) + (620136236661 <<< 40) + (134783538 <<< 80))
def wire39 : FreeSupport.Wire := ((258138959872 <<< 0) + (1072688137524 <<< 40) + (140177207 <<< 80), (341232656384 <<< 0) + (757709674229 <<< 40) + (135849523 <<< 80))
def wire40 : FreeSupport.Wire := ((395275898368 <<< 0) + (1062561924940 <<< 40) + (407813042 <<< 80), (31970099712 <<< 0) + (620145149557 <<< 40) + (139244210 <<< 80))
def wire41 : FreeSupport.Wire := ((137740972032 <<< 0) + (379032043568 <<< 40) + (149072903 <<< 80), (142088355840 <<< 0) + (103633963119 <<< 40) + (142649346 <<< 80))
def wire42 : FreeSupport.Wire := ((140453638592 <<< 0) + (396245547057 <<< 40) + (686013519 <<< 80), (144244228160 <<< 0) + (120883038319 <<< 40) + (142784522 <<< 80))
def wire43 : FreeSupport.Wire := ((258138959872 <<< 0) + (520784839988 <<< 40) + (149072951 <<< 80), (186146054144 <<< 0) + (242314435695 <<< 40) + (143173683 <<< 80))
def wire44 : FreeSupport.Wire := ((258138959872 <<< 0) + (1070540653876 <<< 40) + (149598007 <<< 80), (169468837888 <<< 0) + (654497074815 <<< 40) + (143174194 <<< 80))
def wire45 : FreeSupport.Wire := ((258138959872 <<< 0) + (1036180915508 <<< 40) + (139111223 <<< 80), (66354634752 <<< 0) + (757710478967 <<< 40) + (143174195 <<< 80))
def wire46 : FreeSupport.Wire := ((258138959872 <<< 0) + (520784839988 <<< 40) + (183692839 <<< 80), (451360473088 <<< 0) + (241207400687 <<< 40) + (143715331 <<< 80))
def wire47 : FreeSupport.Wire := ((420700258296 <<< 0) + (639658359545 <<< 40) + (137011480 <<< 80), (34108178426 <<< 0) + (639801239413 <<< 40) + (170566458 <<< 80))
def wire48 : FreeSupport.Wire := ((0 <<< 0) + (1071594340352 <<< 40) + (170944279 <<< 80), (464513662976 <<< 0) + (792841204728 <<< 40) + (170944259 <<< 80))
def wire49 : FreeSupport.Wire := ((0 <<< 0) + (929860419584 <<< 40) + (184215298 <<< 80), (434683248640 <<< 0) + (655804900349 <<< 40) + (170977026 <<< 80))
def wire50 : FreeSupport.Wire := ((258138959872 <<< 0) + (1072688137524 <<< 40) + (184217399 <<< 80), (478740963328 <<< 0) + (794486439935 <<< 40) + (179892019 <<< 80))
def wire51 : FreeSupport.Wire := ((258138959872 <<< 0) + (1081278072116 <<< 40) + (184217463 <<< 80), (478740963328 <<< 0) + (794486439935 <<< 40) + (179892019 <<< 80))
def wire52 : FreeSupport.Wire := ((533016870400 <<< 0) + (1081890457468 <<< 40) + (452652983 <<< 80), (478740963328 <<< 0) + (794486439935 <<< 40) + (179892019 <<< 80))
def wire53 : FreeSupport.Wire := ((258138959872 <<< 0) + (1072688137524 <<< 40) + (519761847 <<< 80), (478740963328 <<< 0) + (794486439935 <<< 40) + (179892019 <<< 80))
def wire54 : FreeSupport.Wire := ((258138959872 <<< 0) + (1098457941300 <<< 40) + (184221559 <<< 80), (478749351936 <<< 0) + (794486439935 <<< 40) + (179896115 <<< 80))
def wire55 : FreeSupport.Wire := ((956401946567 <<< 0) + (69657263951 <<< 40) + (182454658 <<< 80), (142089637863 <<< 0) + (106058803567 <<< 40) + (182757762 <<< 80))
def wire56 : FreeSupport.Wire := ((140453638592 <<< 0) + (379065677873 <<< 40) + (685943879 <<< 80), (210816225600 <<< 0) + (103634028655 <<< 40) + (209762374 <<< 80))
def wire57 : FreeSupport.Wire := ((533016870400 <<< 0) + (1081890457468 <<< 40) + (519761911 <<< 80), (547460442112 <<< 0) + (794486505471 <<< 40) + (247000951 <<< 80))
def wire58 : FreeSupport.Wire := ((538385579576 <<< 0) + (1099205101564 <<< 40) + (520028151 <<< 80), (547469879848 <<< 0) + (794495418367 <<< 40) + (251461623 <<< 80))
def wire59 : FreeSupport.Wire := ((5368709176 <<< 0) + (878455586944 <<< 40) + (354416136 <<< 80), (844632424464 <<< 0) + (841883058832 <<< 40) + (269698568 <<< 80))
def wire60 : FreeSupport.Wire := ((143109681208 <<< 0) + (1021264429232 <<< 40) + (354416189 <<< 80), (888689926160 <<< 0) + (980563531408 <<< 40) + (270222905 <<< 80))
def wire61 : FreeSupport.Wire := ((558413381639 <<< 0) + (309510537218 <<< 40) + (399857282 <<< 80), (962277408772 <<< 0) + (309246853256 <<< 40) + (274023552 <<< 80))
def wire62 : FreeSupport.Wire := ((563782090815 <<< 0) + (878728478850 <<< 40) + (400553610 <<< 80), (982141632532 <<< 0) + (876251742872 <<< 40) + (274155144 <<< 80))
def wire63 : FreeSupport.Wire := ((678811369479 <<< 0) + (451263333638 <<< 40) + (399859367 <<< 80), (996671356932 <<< 0) + (446821095562 <<< 40) + (282414209 <<< 80))
def wire64 : FreeSupport.Wire := ((563782090815 <<< 0) + (947447955586 <<< 40) + (398456584 <<< 80), (849195827218 <<< 0) + (844835857301 <<< 40) + (305383176 <<< 80))
def wire65 : FreeSupport.Wire := ((563782090815 <<< 0) + (878728478850 <<< 40) + (536729474 <<< 80), (966840811556 <<< 0) + (312199651725 <<< 40) + (309708160 <<< 80))
def wire66 : FreeSupport.Wire := ((137740972032 <<< 0) + (327492436016 <<< 40) + (872920141 <<< 80), (620765384704 <<< 0) + (292127047680 <<< 40) + (335745100 <<< 80))
def wire67 : FreeSupport.Wire := ((143109681208 <<< 0) + (1025559396528 <<< 40) + (874493053 <<< 80), (664822878216 <<< 0) + (430807520256 <<< 40) + (336269437 <<< 80))
def wire68 : FreeSupport.Wire := ((143109681208 <<< 0) + (879530508464 <<< 40) + (891287117 <<< 80), (913360293904 <<< 0) + (841883124368 <<< 40) + (336811596 <<< 80))
def wire69 : FreeSupport.Wire := ((140453638592 <<< 0) + (396245547057 <<< 40) + (883407949 <<< 80), (625328787520 <<< 0) + (292664985607 <<< 40) + (344168524 <<< 80))
def wire70 : FreeSupport.Wire := ((0 <<< 0) + (309237645312 <<< 40) + (885333191 <<< 80), (756127105024 <<< 0) + (309247723530 <<< 40) + (348461252 <<< 80))
def wire71 : FreeSupport.Wire := ((0 <<< 0) + (395136991232 <<< 40) + (484947082 <<< 80), (694126903296 <<< 0) + (395768791149 <<< 40) + (407347338 <<< 80))
def wire72 : FreeSupport.Wire := ((0 <<< 0) + (910533066752 <<< 40) + (424653706 <<< 80), (574335483904 <<< 0) + (911164834421 <<< 40) + (407347850 <<< 80))
def wire73 : FreeSupport.Wire := ((0 <<< 0) + (361850994688 <<< 40) + (944224394 <<< 80), (556627132416 <<< 0) + (361409020005 <<< 40) + (407351434 <<< 80))
def wire74 : FreeSupport.Wire := ((0 <<< 0) + (929860419584 <<< 40) + (523331466 <<< 80), (980009877504 <<< 0) + (930145936376 <<< 40) + (439445250 <<< 80))
def wire75 : FreeSupport.Wire := ((563782090815 <<< 0) + (947447955586 <<< 40) + (536868746 <<< 80), (986721812534 <<< 0) + (947940795389 <<< 40) + (444065674 <<< 80))
def wire76 : FreeSupport.Wire := ((838660001343 <<< 0) + (1094089229002 <<< 40) + (536868762 <<< 80), (986721812534 <<< 0) + (947940795389 <<< 40) + (444065674 <<< 80))
def wire77 : FreeSupport.Wire := ((821921050687 <<< 0) + (1090275673526 <<< 40) + (536870847 <<< 80), (1030779527222 <<< 0) + (1086622334975 <<< 40) + (452980667 <<< 80))
def wire78 : FreeSupport.Wire := ((2712666560 <<< 0) + (377990756353 <<< 40) + (1008805071 <<< 80), (756134445312 <<< 0) + (377973997672 <<< 40) + (469835846 <<< 80))
def wire79 : FreeSupport.Wire := ((140453638592 <<< 0) + (396245547057 <<< 40) + (1009235151 <<< 80), (758290321664 <<< 0) + (395223072872 <<< 40) + (469971022 <<< 80))
def wire80 : FreeSupport.Wire := ((538385579576 <<< 0) + (310004860924 <<< 40) + (475276422 <<< 80), (1031013924668 <<< 0) + (377983172840 <<< 40) + (475358406 <<< 80))
def wire81 : FreeSupport.Wire := ((140453638592 <<< 0) + (379065677873 <<< 40) + (1008807119 <<< 80), (756142854464 <<< 0) + (377975064682 <<< 40) + (478230598 <<< 80))
def wire82 : FreeSupport.Wire := ((140453638592 <<< 0) + (379065677873 <<< 40) + (1021553871 <<< 80), (760697864448 <<< 0) + (378511935599 <<< 40) + (478259270 <<< 80))
def wire83 : FreeSupport.Wire := ((140453638592 <<< 0) + (396245547057 <<< 40) + (1021820111 <<< 80), (762854789440 <<< 0) + (395769923695 <<< 40) + (482851022 <<< 80))
def wire84 : FreeSupport.Wire := ((415331549120 <<< 0) + (1092642634361 <<< 40) + (1021820383 <<< 80), (762854789440 <<< 0) + (395769923695 <<< 40) + (482851022 <<< 80))
def wire85 : FreeSupport.Wire := ((277590577088 <<< 0) + (1076535327305 <<< 40) + (1043408351 <<< 80), (790528264448 <<< 0) + (517963100520 <<< 40) + (505487687 <<< 80))
def wire86 : FreeSupport.Wire := ((838660001343 <<< 0) + (1094089229002 <<< 40) + (536868831 <<< 80), (1089835108406 <<< 0) + (1085514036221 <<< 40) + (511174607 <<< 80))
def wire87 : FreeSupport.Wire := ((415331549120 <<< 0) + (1094790118009 <<< 40) + (1056423391 <<< 80), (797248608576 <<< 0) + (535759026543 <<< 40) + (518502863 <<< 80))
def wire88 : FreeSupport.Wire := ((420700258296 <<< 0) + (1094924892921 <<< 40) + (1056947711 <<< 80), (806912285544 <<< 0) + (536866323823 <<< 40) + (519027199 <<< 80))
def wire89 : FreeSupport.Wire := ((704235729407 <<< 0) + (948556511411 <<< 40) + (1073741775 <<< 80), (1055449698678 <<< 0) + (947941927935 <<< 40) + (519569358 <<< 80))
def wire90 : FreeSupport.Wire := ((838660001343 <<< 0) + (1095162970826 <<< 40) + (536870911 <<< 80), (1099507173950 <<< 0) + (1086622400511 <<< 40) + (520093695 <<< 80))
def wire91 : FreeSupport.Wire := ((260851626432 <<< 0) + (1089901641013 <<< 40) + (1056964607 <<< 80), (1099507396928 <<< 0) + (1086622400511 <<< 40) + (520093695 <<< 80))
def wire92 : FreeSupport.Wire := ((395275898368 <<< 0) + (152028858188 <<< 40) + (536873008 <<< 80), (9676359168 <<< 0) + (13996524544 <<< 40) + (554176560 <<< 80))
def wire93 : FreeSupport.Wire := ((395275898368 <<< 0) + (701784672076 <<< 40) + (939526576 <<< 80), (9676359168 <<< 0) + (13996524544 <<< 40) + (554176560 <<< 80))
def wire94 : FreeSupport.Wire := ((0 <<< 0) + (720480763904 <<< 40) + (554422905 <<< 80), (63934300160 <<< 0) + (718574589456 <<< 40) + (554308153 <<< 80))
def wire95 : FreeSupport.Wire := ((0 <<< 0) + (787052756992 <<< 40) + (554408760 <<< 80), (34103885824 <<< 0) + (581538285077 <<< 40) + (554340920 <<< 80))
def wire96 : FreeSupport.Wire := ((395275898368 <<< 0) + (787684017996 <<< 40) + (554408760 <<< 80), (34103985664 <<< 0) + (581538285077 <<< 40) + (554340920 <<< 80))
def wire97 : FreeSupport.Wire := ((395275898368 <<< 0) + (718964541260 <<< 40) + (944544176 <<< 80), (14240810496 <<< 0) + (14542308357 <<< 40) + (558665904 <<< 80))
def wire98 : FreeSupport.Wire := ((558413381639 <<< 0) + (150596747266 <<< 40) + (595679841 <<< 80), (34406400001 <<< 0) + (150463469570 <<< 40) + (562042881 <<< 80))
def wire99 : FreeSupport.Wire := ((561126048199 <<< 0) + (237603469315 <<< 40) + (597940841 <<< 80), (41117286465 <<< 0) + (168249415687 <<< 40) + (562206729 <<< 80))
def wire100 : FreeSupport.Wire := ((2712666560 <<< 0) + (151431231489 <<< 40) + (536873073 <<< 80), (44070076609 <<< 0) + (151570766850 <<< 40) + (562567217 <<< 80))
def wire101 : FreeSupport.Wire := ((678811369479 <<< 0) + (459853268230 <<< 40) + (600923751 <<< 80), (446792859649 <<< 0) + (184823502986 <<< 40) + (563108865 <<< 80))
def wire102 : FreeSupport.Wire := ((2712666560 <<< 0) + (770980263937 <<< 40) + (589382489 <<< 80), (52114751616 <<< 0) + (702634144528 <<< 40) + (589300481 <<< 80))
def wire103 : FreeSupport.Wire := ((561126048199 <<< 0) + (788433025027 <<< 40) + (598463321 <<< 80), (58825638018 <<< 0) + (720420090645 <<< 40) + (589464329 <<< 80))
def wire104 : FreeSupport.Wire := ((959057989183 <<< 0) + (703266080718 <<< 40) + (51921712 <<< 80), (336656838335 <<< 0) + (703741704080 <<< 40) + (590890801 <<< 80))
def wire105 : FreeSupport.Wire := ((561126048199 <<< 0) + (771253155843 <<< 40) + (597777273 <<< 80), (52123140225 <<< 0) + (702635211538 <<< 40) + (597695233 <<< 80))
def wire106 : FreeSupport.Wire := ((561126048199 <<< 0) + (789506766851 <<< 40) + (598465401 <<< 80), (68497703107 <<< 0) + (721528454935 <<< 40) + (598383417 <<< 80))
def wire107 : FreeSupport.Wire := ((836003958727 <<< 0) + (790119152203 <<< 40) + (1001118713 <<< 80), (68497703107 <<< 0) + (721528454935 <<< 40) + (598383417 <<< 80))
def wire108 : FreeSupport.Wire := ((956401946567 <<< 0) + (790138027855 <<< 40) + (598465401 <<< 80), (68497802947 <<< 0) + (721528454935 <<< 40) + (598383417 <<< 80))
def wire109 : FreeSupport.Wire := ((819265008071 <<< 0) + (789526822199 <<< 40) + (598465405 <<< 80), (68497924291 <<< 0) + (721528454935 <<< 40) + (598383417 <<< 80))
def wire110 : FreeSupport.Wire := ((836003958727 <<< 0) + (790119152203 <<< 40) + (1005575161 <<< 80), (68498752195 <<< 0) + (721537367831 <<< 40) + (602839993 <<< 80))
def wire111 : FreeSupport.Wire := ((277590577088 <<< 0) + (150969875017 <<< 40) + (536870997 <<< 80), (103117491584 <<< 0) + (150462468096 <<< 40) + (620757061 <<< 80))
def wire112 : FreeSupport.Wire := ((137740972032 <<< 0) + (151398776880 <<< 40) + (536871029 <<< 80), (112789565448 <<< 0) + (151569765376 <<< 40) + (621285493 <<< 80))
def wire113 : FreeSupport.Wire := ((120397987840 <<< 0) + (150342731012 <<< 40) + (536873061 <<< 80), (103126040577 <<< 0) + (150463535106 <<< 40) + (629151813 <<< 80))
def wire114 : FreeSupport.Wire := ((535729536960 <<< 0) + (152063672189 <<< 40) + (536873077 <<< 80), (112789815241 <<< 0) + (151570832386 <<< 40) + (629676149 <<< 80))
def wire115 : FreeSupport.Wire := ((277590577088 <<< 0) + (805952387657 <<< 40) + (1060193245 <<< 80), (258342389888 <<< 0) + (736993981208 <<< 40) + (656409413 <<< 80))
def wire116 : FreeSupport.Wire := ((535729536960 <<< 0) + (738326708093 <<< 40) + (1043335669 <<< 80), (250297974729 <<< 0) + (188346531082 <<< 40) + (665327989 <<< 80))
def wire117 : FreeSupport.Wire := ((1094142918599 <<< 0) + (790139207551 <<< 40) + (598465405 <<< 80), (137217441739 <<< 0) + (721528520471 <<< 40) + (665492349 <<< 80))
def wire118 : FreeSupport.Wire := ((836003958727 <<< 0) + (824478890571 <<< 40) + (1069276157 <<< 80), (274725341379 <<< 0) + (755888291615 <<< 40) + (665492349 <<< 80))
def wire119 : FreeSupport.Wire := ((541098246136 <<< 0) + (755641352189 <<< 40) + (1056741877 <<< 80), (254862426089 <<< 0) + (188892314895 <<< 40) + (669817333 <<< 80))
def wire120 : FreeSupport.Wire := ((841372667903 <<< 0) + (824613665483 <<< 40) + (1073732605 <<< 80), (274726390507 <<< 0) + (755897204511 <<< 40) + (669948925 <<< 80))
def wire121 : FreeSupport.Wire := ((395275898368 <<< 0) + (1045382055756 <<< 40) + (675982130 <<< 80), (31973279232 <<< 0) + (633025463925 <<< 40) + (688435762 <<< 80))
def wire122 : FreeSupport.Wire := ((819265008071 <<< 0) + (1098764467511 <<< 40) + (737935231 <<< 80), (480901030083 <<< 0) + (824624742399 <<< 40) + (733675323 <<< 80))
def wire123 : FreeSupport.Wire := ((535729536960 <<< 0) + (1081924091773 <<< 40) + (721088375 <<< 80), (547473063881 <<< 0) + (807375732735 <<< 40) + (800653175 <<< 80))
def wire124 : FreeSupport.Wire := ((0 <<< 0) + (993211187200 <<< 40) + (823112248 <<< 80), (579430514688 <<< 0) + (855879321104 <<< 40) + (822809144 <<< 80))
def wire125 : FreeSupport.Wire := ((120397987840 <<< 0) + (425220637956 <<< 40) + (826612386 <<< 80), (549903695872 <<< 0) + (287776047104 <<< 40) + (826609792 <<< 80))
def wire126 : FreeSupport.Wire := ((395275898368 <<< 0) + (975588837196 <<< 40) + (960830386 <<< 80), (549903695872 <<< 0) + (287776047104 <<< 40) + (826609792 <<< 80))
def wire127 : FreeSupport.Wire := ((395275898368 <<< 0) + (993842448204 <<< 40) + (961387442 <<< 80), (564130775552 <<< 0) + (289420215301 <<< 40) + (827166896 <<< 80))
def wire128 : FreeSupport.Wire := ((678811369479 <<< 0) + (459853268230 <<< 40) + (936730274 <<< 80), (962290024452 <<< 0) + (322136080520 <<< 40) + (827675776 <<< 80))
def wire129 : FreeSupport.Wire := ((678811369479 <<< 0) + (425493529862 <<< 40) + (868571875 <<< 80), (584297512961 <<< 0) + (425350289410 <<< 40) + (835000449 <<< 80))
def wire130 : FreeSupport.Wire := ((0 <<< 0) + (459561500672 <<< 40) + (923879111 <<< 80), (1065393848320 <<< 0) + (459700408456 <<< 40) + (890324037 <<< 80))
def wire131 : FreeSupport.Wire := ((0 <<< 0) + (1011464798208 <<< 40) + (890332765 <<< 80), (945602428928 <<< 0) + (975096451728 <<< 40) + (890324549 <<< 80))
def wire132 : FreeSupport.Wire := ((0 <<< 0) + (459561500672 <<< 40) + (890590821 <<< 80), (927894077440 <<< 0) + (425340637312 <<< 40) + (890328133 <<< 80))
def wire133 : FreeSupport.Wire := ((143109681208 <<< 0) + (1029854363824 <<< 40) + (891287165 <<< 80), (957421989912 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80))
def wire134 : FreeSupport.Wire := ((417987591736 <<< 0) + (1030466749176 <<< 40) + (1025505277 <<< 80), (957421989912 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80))
def wire135 : FreeSupport.Wire := ((417987591736 <<< 0) + (1030466749176 <<< 40) + (891287165 <<< 80), (957421991960 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80))
def wire136 : FreeSupport.Wire := ((420700258296 <<< 0) + (1030500383481 <<< 40) + (891287165 <<< 80), (957421993368 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80))
def wire137 : FreeSupport.Wire := ((538385579576 <<< 0) + (1030485624828 <<< 40) + (891289213 <<< 80), (957422089752 <<< 0) + (993452824208 <<< 40) + (890984061 <<< 80))
def wire138 : FreeSupport.Wire := ((841372667903 <<< 0) + (26823490251 <<< 40) + (889524424 <<< 80), (620770664447 <<< 0) + (305025187840 <<< 40) + (893849804 <<< 80))
def wire139 : FreeSupport.Wire := ((541098246136 <<< 0) + (1030519259133 <<< 40) + (891289213 <<< 80), (957422239705 <<< 0) + (993453891218 <<< 40) + (899374717 <<< 80))
def wire140 : FreeSupport.Wire := ((678811369479 <<< 0) + (459853268230 <<< 40) + (936730343 <<< 80), (1065403449349 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire141 : FreeSupport.Wire := ((678811369479 <<< 0) + (1011756565766 <<< 40) + (936730359 <<< 80), (1065403449349 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire142 : FreeSupport.Wire := ((953689280007 <<< 0) + (1010221467470 <<< 40) + (1070948343 <<< 80), (1065403449349 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire143 : FreeSupport.Wire := ((678811369479 <<< 0) + (459853268230 <<< 40) + (1073045223 <<< 80), (1065403449349 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire144 : FreeSupport.Wire := ((953689280007 <<< 0) + (460465653582 <<< 40) + (936730359 <<< 80), (1065403451397 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire145 : FreeSupport.Wire := ((956401946567 <<< 0) + (460499287887 <<< 40) + (936730359 <<< 80), (1065403452805 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire146 : FreeSupport.Wire := ((819265008071 <<< 0) + (460961824055 <<< 40) + (936730343 <<< 80), (1065403470149 <<< 0) + (459710388362 <<< 40) + (903175365 <<< 80))
def wire147 : FreeSupport.Wire := ((816552341511 <<< 0) + (478108058934 <<< 40) + (936902383 <<< 80), (1067550937093 <<< 0) + (476959463562 <<< 40) + (903306445 <<< 80))
def wire148 : FreeSupport.Wire := ((1094142918599 <<< 0) + (461574209407 <<< 40) + (936730359 <<< 80), (1075067224013 <<< 0) + (460817685642 <<< 40) + (903699701 <<< 80))
def wire149 : FreeSupport.Wire := ((821921050687 <<< 0) + (1030146131382 <<< 40) + (937426687 <<< 80), (1094931361821 <<< 0) + (1027822575258 <<< 40) + (903831293 <<< 80))
def wire150 : FreeSupport.Wire := ((417987591736 <<< 0) + (1030466749176 <<< 40) + (1061156861 <<< 80), (1094930151448 <<< 0) + (1030228522904 <<< 40) + (926635901 <<< 80))
def wire151 : FreeSupport.Wire := ((704235729407 <<< 0) + (1098880366771 <<< 40) + (935329661 <<< 80), (961985392859 <<< 0) + (996406689687 <<< 40) + (935059325 <<< 80))
def wire152 : FreeSupport.Wire := ((953689280007 <<< 0) + (1012368951118 <<< 40) + (1073045495 <<< 80), (1065403451397 <<< 0) + (462126315914 <<< 40) + (938827205 <<< 80))
def wire153 : FreeSupport.Wire := ((959057989183 <<< 0) + (1030757337038 <<< 40) + (1073602551 <<< 80), (1079630531117 <<< 0) + (463770484111 <<< 40) + (939384309 <<< 80))
def wire154 : FreeSupport.Wire := ((417987591736 <<< 0) + (1030466749176 <<< 40) + (1073741821 <<< 80), (1099494603320 <<< 0) + (1030775373727 <<< 40) + (939515901 <<< 80))
def wire155 : FreeSupport.Wire := ((681524036039 <<< 0) + (1098763287815 <<< 40) + (939515903 <<< 80), (1099494752455 <<< 0) + (1030775373727 <<< 40) + (939515901 <<< 80))
def wire156 : FreeSupport.Wire := ((274877910528 <<< 0) + (1044289438280 <<< 40) + (956375962 <<< 80), (567627744256 <<< 0) + (906259202672 <<< 40) + (956375554 <<< 80))
def wire157 : FreeSupport.Wire := ((395275898368 <<< 0) + (1045382055756 <<< 40) + (956378042 <<< 80), (577299908096 <<< 0) + (907366499952 <<< 40) + (956903986 <<< 80))
def wire158 : FreeSupport.Wire := ((395275898368 <<< 0) + (1045382055756 <<< 40) + (961260474 <<< 80), (581854888960 <<< 0) + (907903370869 <<< 40) + (956932658 <<< 80))
def wire159 : FreeSupport.Wire := ((819265008071 <<< 0) + (348218932535 <<< 40) + (553870858 <<< 80), (844653655511 <<< 0) + (923508540144 <<< 40) + (957572618 <<< 80))
def wire160 : FreeSupport.Wire := ((395275898368 <<< 0) + (1044308313932 <<< 40) + (960838586 <<< 80), (567637214208 <<< 0) + (906268115568 <<< 40) + (960836226 <<< 80))
def wire161 : FreeSupport.Wire := ((395275898368 <<< 0) + (1062561924940 <<< 40) + (961526714 <<< 80), (584011843072 <<< 0) + (925161358965 <<< 40) + (961524410 <<< 80))
def wire162 : FreeSupport.Wire := ((824633717247 <<< 0) + (366607318455 <<< 40) + (567279146 <<< 80), (858890172415 <<< 0) + (925162688247 <<< 40) + (970981050 <<< 80))
def wire163 : FreeSupport.Wire := ((277590577088 <<< 0) + (1046470556233 <<< 40) + (992043995 <<< 80), (602021561472 <<< 0) + (1046248305520 <<< 40) + (992027395 <<< 80))
def wire164 : FreeSupport.Wire := ((959057989183 <<< 0) + (1099476813774 <<< 40) + (1073741754 <<< 80), (996398171702 <<< 0) + (961937319933 <<< 40) + (998242234 <<< 80))
def wire165 : FreeSupport.Wire := ((956401946567 <<< 0) + (1065015934799 <<< 40) + (1005583355 <<< 80), (618405660355 <<< 0) + (1065151528823 <<< 40) + (1005566907 <<< 80))
def wire166 : FreeSupport.Wire := ((566494757375 <<< 0) + (1098879187075 <<< 40) + (1073741819 <<< 80), (1030791889143 <<< 0) + (1099511562239 <<< 40) + (1006632891 <<< 80))
def wire167 : FreeSupport.Wire := ((533016870400 <<< 0) + (1099070326652 <<< 40) + (1006632895 <<< 80), (1030792144384 <<< 0) + (1099511562239 <<< 40) + (1006632891 <<< 80))
def wire168 : FreeSupport.Wire := ((277590577088 <<< 0) + (528926997065 <<< 40) + (1008805087 <<< 80), (790532459904 <<< 0) + (528436400232 <<< 40) + (1023483975 <<< 80))
def wire169 : FreeSupport.Wire := ((277590577088 <<< 0) + (1078682810953 <<< 40) + (1025583071 <<< 80), (773855380736 <<< 0) + (940619039352 <<< 40) + (1023484486 <<< 80))
def wire170 : FreeSupport.Wire := ((277590577088 <<< 0) + (1044323072585 <<< 40) + (956376031 <<< 80), (670741040512 <<< 0) + (1043832443504 <<< 40) + (1023484487 <<< 80))
def wire171 : FreeSupport.Wire := ((533016870400 <<< 0) + (1096922843004 <<< 40) + (1028636671 <<< 80), (652731323904 <<< 0) + (925161424501 <<< 40) + (1028633342 <<< 80))
def wire172 : FreeSupport.Wire := ((538385579576 <<< 0) + (1099205101564 <<< 40) + (1029701631 <<< 80), (962003318296 <<< 0) + (1062734862069 <<< 40) + (1029699327 <<< 80))
def wire173 : FreeSupport.Wire := ((535729536960 <<< 0) + (547200663421 <<< 40) + (1021820159 <<< 80), (806916718537 <<< 0) + (547339623535 <<< 40) + (1037023487 <<< 80))
def wire174 : FreeSupport.Wire := ((535729536960 <<< 0) + (1096956477309 <<< 40) + (1039122431 <<< 80), (790239500096 <<< 0) + (959522262655 <<< 40) + (1037023998 <<< 80))
def wire175 : FreeSupport.Wire := ((535729536960 <<< 0) + (1062596738941 <<< 40) + (961526783 <<< 80), (687125299145 <<< 0) + (1062735666807 <<< 40) + (1037023999 <<< 80))
def wire176 : FreeSupport.Wire := ((819265008071 <<< 0) + (546861169975 <<< 40) + (1073217263 <<< 80), (1072131133765 <<< 0) + (546232588527 <<< 40) + (1037565135 <<< 80))
def wire177 : FreeSupport.Wire := ((145822347768 <<< 0) + (1098607474865 <<< 40) + (1040187135 <<< 80), (1099511394648 <<< 0) + (1097095700223 <<< 40) + (1038089983 <<< 80))
def wire178 : FreeSupport.Wire := ((953689280007 <<< 0) + (1097194555214 <<< 40) + (1071644671 <<< 80), (1099511596549 <<< 0) + (1097095700223 <<< 40) + (1038089983 <<< 80))
def wire179 : FreeSupport.Wire := ((277590577088 <<< 0) + (1080830294601 <<< 40) + (1060202463 <<< 80), (1083127369088 <<< 0) + (1080608404472 <<< 40) + (1060202311 <<< 80))
def wire180 : FreeSupport.Wire := ((420700258296 <<< 0) + (1099219860217 <<< 40) + (1061156863 <<< 80), (1094946930072 <<< 0) + (1098964776952 <<< 40) + (1060861823 <<< 80))
def wire181 : FreeSupport.Wire := ((395275898368 <<< 0) + (1099069146956 <<< 40) + (1065335807 <<< 80), (824633298432 <<< 0) + (1099510298493 <<< 40) + (1064285183 <<< 80))
def wire182 : FreeSupport.Wire := ((841372667903 <<< 0) + (1098417830603 <<< 40) + (1073739743 <<< 80), (1089839304118 <<< 0) + (1098403263485 <<< 40) + (1064822735 <<< 80))
def wire183 : FreeSupport.Wire := ((701523062847 <<< 0) + (1098846732466 <<< 40) + (1073739775 <<< 80), (1099511377982 <<< 0) + (1099510560765 <<< 40) + (1065351167 <<< 80))
def wire184 : FreeSupport.Wire := ((397988564928 <<< 0) + (1099102781261 <<< 40) + (1065353215 <<< 80), (1099511467904 <<< 0) + (1099510560765 <<< 40) + (1065351167 <<< 80))
def wire185 : FreeSupport.Wire := ((535729536960 <<< 0) + (1081924091773 <<< 40) + (1060204543 <<< 80), (1092799692745 <<< 0) + (1081716768762 <<< 40) + (1069121399 <<< 80))
def wire186 : FreeSupport.Wire := ((535729536960 <<< 0) + (1081924091773 <<< 40) + (1073475583 <<< 80), (1097354669440 <<< 0) + (1082253639679 <<< 40) + (1069150071 <<< 80))
def wire187 : FreeSupport.Wire := ((836003958727 <<< 0) + (1099356797515 <<< 40) + (1069285375 <<< 80), (1099510320579 <<< 0) + (1099502714879 <<< 40) + (1069285247 <<< 80))
def wire188 : FreeSupport.Wire := ((263507669048 <<< 0) + (1098592716212 <<< 40) + (1073741695 <<< 80), (1099510542360 <<< 0) + (1099502714879 <<< 40) + (1069285247 <<< 80))
def wire189 : FreeSupport.Wire := ((698867020231 <<< 0) + (1098745591859 <<< 40) + (1072693247 <<< 80), (824633217475 <<< 0) + (1099511365503 <<< 40) + (1072675839 <<< 80))
def wire190 : FreeSupport.Wire := ((400644607544 <<< 0) + (1099203921868 <<< 40) + (1073724415 <<< 80), (824633298472 <<< 0) + (1099511365503 <<< 40) + (1072675839 <<< 80))
def wire191 : FreeSupport.Wire := ((956401946567 <<< 0) + (1081122062159 <<< 40) + (1073053695 <<< 80), (1083136970117 <<< 0) + (1080618384378 <<< 40) + (1073053639 <<< 80))
def wire192 : FreeSupport.Wire := ((415331549120 <<< 0) + (1099085085305 <<< 40) + (1073217503 <<< 80), (1089847713216 <<< 0) + (1098404330495 <<< 40) + (1073217487 <<< 80))
def wire193 : FreeSupport.Wire := ((684180078655 <<< 0) + (1097790686598 <<< 40) + (1073741807 <<< 80), (1089847853111 <<< 0) + (1098404330495 <<< 40) + (1073217487 <<< 80))
def wire194 : FreeSupport.Wire := ((282959286264 <<< 0) + (1099218680521 <<< 40) + (1073610751 <<< 80), (1097363885992 <<< 0) + (1082262552575 <<< 40) + (1073610743 <<< 80))
def wire195 : FreeSupport.Wire := ((816552341511 <<< 0) + (1081550964022 <<< 40) + (1073741815 <<< 80), (1097364135941 <<< 0) + (1082262552575 <<< 40) + (1073610743 <<< 80))
def wire196 : FreeSupport.Wire := ((1099511627775 <<< 0) + (1099511627775 <<< 40) + (1073741823 <<< 80), (1099511627775 <<< 0) + (1099511627775 <<< 40) + (1073741823 <<< 80))
def node1_0 : List FreeSupport.Wire := [wire1, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_1 : List FreeSupport.Wire := [wire4, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_2 : List FreeSupport.Wire := [wire5, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_3 : List FreeSupport.Wire := [wire7, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83]
def node1_4 : List FreeSupport.Wire := [wire7, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_5 : List FreeSupport.Wire := [wire7, wire50, wire34, wire114, wire106, wire133, wire140, wire161, wire83]
def node1_6 : List FreeSupport.Wire := [wire9, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_7 : List FreeSupport.Wire := [wire10, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_8 : List FreeSupport.Wire := [wire11, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_9 : List FreeSupport.Wire := [wire16, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_10 : List FreeSupport.Wire := [wire17, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_11 : List FreeSupport.Wire := [wire18, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_12 : List FreeSupport.Wire := [wire21, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_13 : List FreeSupport.Wire := [wire27, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_14 : List FreeSupport.Wire := [wire33, wire50, wire34, wire75, wire106, wire133, wire140, wire83, wire179]
def node1_15 : List FreeSupport.Wire := [wire33, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_16 : List FreeSupport.Wire := [wire33, wire50, wire34, wire114, wire106, wire133, wire140, wire83, wire179]
def node1_17 : List FreeSupport.Wire := [wire34, wire75, wire106, wire138, wire133, wire140, wire161, wire83, wire179]
def node1_18 : List FreeSupport.Wire := [wire34, wire114, wire106, wire138, wire133, wire140, wire161, wire83, wire179]
def node1_19 : List FreeSupport.Wire := [wire37, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_20 : List FreeSupport.Wire := [wire41, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_21 : List FreeSupport.Wire := [wire47, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_22 : List FreeSupport.Wire := [wire47, wire50, wire34, wire75, wire106, wire133, wire161, wire83, wire179]
def node1_23 : List FreeSupport.Wire := [wire47, wire50, wire34, wire114, wire106, wire133, wire161, wire83, wire179]
def node1_24 : List FreeSupport.Wire := [wire48, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_25 : List FreeSupport.Wire := [wire49, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_26 : List FreeSupport.Wire := [wire50, wire0, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_27 : List FreeSupport.Wire := [wire50, wire2, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_28 : List FreeSupport.Wire := [wire50, wire8, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_29 : List FreeSupport.Wire := [wire50, wire12, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_30 : List FreeSupport.Wire := [wire50, wire19, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_31 : List FreeSupport.Wire := [wire50, wire20, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_32 : List FreeSupport.Wire := [wire50, wire22, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_33 : List FreeSupport.Wire := [wire50, wire23, wire30, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_34 : List FreeSupport.Wire := [wire50, wire23, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_35 : List FreeSupport.Wire := [wire50, wire28, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_36 : List FreeSupport.Wire := [wire50, wire29, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_37 : List FreeSupport.Wire := [wire50, wire30, wire12, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_38 : List FreeSupport.Wire := [wire50, wire30, wire34, wire75, wire102, wire106, wire133, wire140, wire161, wire83]
def node1_39 : List FreeSupport.Wire := [wire50, wire30, wire34, wire75, wire106, wire133, wire140, wire161, wire78, wire83]
def node1_40 : List FreeSupport.Wire := [wire50, wire30, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_41 : List FreeSupport.Wire := [wire50, wire30, wire75, wire106, wire133, wire140, wire161, wire83, wire119, wire179]
def node1_42 : List FreeSupport.Wire := [wire50, wire30, wire75, wire106, wire133, wire140, wire161, wire83, wire194]
def node1_43 : List FreeSupport.Wire := [wire50, wire30, wire114, wire106, wire133, wire140, wire161, wire83, wire194]
def node1_44 : List FreeSupport.Wire := [wire50, wire34, wire58, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_45 : List FreeSupport.Wire := [wire50, wire34, wire74, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_46 : List FreeSupport.Wire := [wire50, wire34, wire75, wire3, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_47 : List FreeSupport.Wire := [wire50, wire34, wire75, wire26, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_48 : List FreeSupport.Wire := [wire50, wire34, wire75, wire77, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_49 : List FreeSupport.Wire := [wire50, wire34, wire75, wire86, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_50 : List FreeSupport.Wire := [wire50, wire34, wire75, wire90, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_51 : List FreeSupport.Wire := [wire50, wire34, wire75, wire92, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_52 : List FreeSupport.Wire := [wire50, wire34, wire75, wire94, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_53 : List FreeSupport.Wire := [wire50, wire34, wire75, wire95, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_54 : List FreeSupport.Wire := [wire50, wire34, wire75, wire98, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_55 : List FreeSupport.Wire := [wire50, wire34, wire75, wire100, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_56 : List FreeSupport.Wire := [wire50, wire34, wire75, wire102, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_57 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire66, wire133, wire140, wire161, wire83, wire179]
def node1_58 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire70, wire133, wire140, wire161, wire83, wire179]
def node1_59 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire117, wire133, wire140, wire161, wire83, wire179]
def node1_60 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire122, wire133, wire140, wire161, wire83, wire179]
def node1_61 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire123, wire133, wire140, wire161, wire83, wire179]
def node1_62 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire124, wire133, wire140, wire161, wire83, wire179]
def node1_63 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire125, wire133, wire140, wire161, wire83, wire179]
def node1_64 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire131, wire133, wire140, wire161, wire83, wire179]
def node1_65 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire132, wire133, wire140, wire161, wire83, wire179]
def node1_66 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire130, wire140, wire161, wire83, wire179]
def node1_67 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire139, wire140, wire161, wire83, wire179]
def node1_68 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire73, wire161, wire83, wire179]
def node1_69 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire148, wire161, wire83, wire179]
def node1_70 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire149, wire161, wire83, wire179]
def node1_71 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire155, wire161, wire83, wire179]
def node1_72 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire156, wire161, wire83, wire179]
def node1_73 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire78, wire83, wire179]
def node1_74 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire87, wire179]
def node1_75 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire88, wire179]
def node1_76 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire91, wire179]
def node1_77 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire116, wire179]
def node1_78 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire119, wire179]
def node1_79 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire172, wire179]
def node1_80 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire173, wire179]
def node1_81 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire174, wire179]
def node1_82 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire177, wire179]
def node2_41 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_84 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire89]
def node1_85 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire118]
def node1_86 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire120]
def node1_87 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire150]
def node1_88 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire152]
def node1_89 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire153]
def node1_90 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire154]
def node1_91 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire164]
def node1_92 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire166]
def node1_93 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire176]
def node1_94 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire178]
def node1_95 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire180]
def node1_96 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire181]
def node1_97 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire182]
def node1_98 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire183]
def node1_99 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire184]
def node1_100 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire185]
def node1_101 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire186]
def node1_102 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire187]
def node1_103 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire188]
def node1_104 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire189]
def node1_105 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire190]
def node1_106 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire191]
def node1_107 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire192]
def node1_108 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire193]
def node1_109 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire194]
def node1_110 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire195]
def node1_111 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179, wire196]
def node1_112 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire165, wire83, wire179]
def node1_113 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire167, wire83, wire179]
def node1_114 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire175, wire83, wire179]
def node1_115 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire151, wire140, wire161, wire83, wire179]
def node1_116 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire138, wire133, wire140, wire161, wire83, wire179]
def node1_117 : List FreeSupport.Wire := [wire50, wire34, wire75, wire111, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_118 : List FreeSupport.Wire := [wire50, wire34, wire75, wire112, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_119 : List FreeSupport.Wire := [wire50, wire34, wire75, wire113, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_120 : List FreeSupport.Wire := [wire50, wire34, wire75, wire114, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_121 : List FreeSupport.Wire := [wire50, wire34, wire75, wire159, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_122 : List FreeSupport.Wire := [wire50, wire34, wire75, wire162, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_123 : List FreeSupport.Wire := [wire50, wire34, wire114, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_124 : List FreeSupport.Wire := [wire50, wire57, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_125 : List FreeSupport.Wire := [wire50, wire59, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_126 : List FreeSupport.Wire := [wire50, wire61, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_127 : List FreeSupport.Wire := [wire50, wire71, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_128 : List FreeSupport.Wire := [wire50, wire72, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_129 : List FreeSupport.Wire := [wire50, wire75, wire159, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_130 : List FreeSupport.Wire := [wire50, wire80, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_131 : List FreeSupport.Wire := [wire50, wire80, wire34, wire75, wire133, wire140, wire161, wire83, wire179]
def node1_132 : List FreeSupport.Wire := [wire50, wire80, wire34, wire114, wire133, wire140, wire161, wire83, wire179]
def node1_133 : List FreeSupport.Wire := [wire50, wire114, wire159, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_134 : List FreeSupport.Wire := [wire55, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_135 : List FreeSupport.Wire := [wire55, wire50, wire34, wire75, wire106, wire140, wire161, wire83, wire179]
def node1_136 : List FreeSupport.Wire := [wire55, wire50, wire34, wire114, wire106, wire140, wire161, wire83, wire179]
def node1_137 : List FreeSupport.Wire := [wire104, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node1_138 : List FreeSupport.Wire := [wire104, wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire179]
def node1_139 : List FreeSupport.Wire := [wire104, wire50, wire34, wire114, wire106, wire133, wire140, wire161, wire179]
def node2_0 : List FreeSupport.Wire := [wire6, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_1 : List FreeSupport.Wire := [wire39, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_2 : List FreeSupport.Wire := [wire43, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_3 : List FreeSupport.Wire := [wire44, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_4 : List FreeSupport.Wire := [wire45, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_5 : List FreeSupport.Wire := [wire46, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_6 : List FreeSupport.Wire := [wire50, wire14, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_7 : List FreeSupport.Wire := [wire50, wire24, wire34, wire75, wire106, wire140, wire161, wire83, wire179]
def node2_8 : List FreeSupport.Wire := [wire50, wire25, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_9 : List FreeSupport.Wire := [wire50, wire31, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_10 : List FreeSupport.Wire := [wire50, wire32, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_11 : List FreeSupport.Wire := [wire50, wire34, wire13, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_12 : List FreeSupport.Wire := [wire50, wire34, wire65, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_13 : List FreeSupport.Wire := [wire50, wire34, wire75, wire15, wire133, wire140, wire161, wire83, wire179]
def node2_14 : List FreeSupport.Wire := [wire50, wire34, wire75, wire96, wire106, wire133, wire140, wire83, wire179]
def node2_15 : List FreeSupport.Wire := [wire50, wire34, wire75, wire99, wire133, wire140, wire161, wire83, wire179]
def node2_16 : List FreeSupport.Wire := [wire50, wire34, wire75, wire103, wire133, wire140, wire161, wire83, wire179]
def node2_17 : List FreeSupport.Wire := [wire50, wire34, wire75, wire105, wire133, wire140, wire161, wire83, wire179]
def node2_18 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire42, wire133, wire140, wire161, wire179]
def node2_19 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire56, wire133, wire140, wire161, wire179]
def node2_20 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire67, wire140, wire161, wire83, wire179]
def node2_21 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire68, wire140, wire161, wire83, wire179]
def node2_22 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire69, wire133, wire140, wire161, wire179]
def node2_23 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire101, wire133, wire161, wire83, wire179]
def node2_24 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire121, wire133, wire140, wire83, wire179]
def node2_25 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire129, wire133, wire161, wire83, wire179]
def node2_26 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire128, wire161, wire83, wire179]
def node2_27 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire83, wire171, wire179]
def node2_28 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire93, wire83, wire179]
def node2_29 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire97, wire83, wire179]
def node2_30 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire126, wire83, wire179]
def node2_31 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire127, wire83, wire179]
def node2_32 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire157, wire83, wire179]
def node2_33 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire158, wire83, wire179]
def node2_34 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire160, wire83, wire179]
def node2_35 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire79, wire179]
def node2_36 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire81, wire179]
def node2_37 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire82, wire179]
def node2_38 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire85]
def node2_39 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire115]
def node2_40 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire169]
def node2_42 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire84, wire179]
def node2_43 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire163, wire83]
def node2_44 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire161, wire168, wire83]
def node2_45 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire140, wire170, wire161, wire83]
def node2_46 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire141, wire161, wire83, wire179]
def node2_47 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire144, wire161, wire83, wire179]
def node2_48 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire145, wire161, wire83, wire179]
def node2_49 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire146, wire161, wire83, wire179]
def node2_50 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire147, wire161, wire83, wire179]
def node2_51 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire161, wire83, wire179, wire142]
def node2_52 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire133, wire161, wire83, wire179, wire143]
def node2_53 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire135, wire140, wire161, wire83, wire179]
def node2_54 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire136, wire140, wire161, wire83, wire179]
def node2_55 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire137, wire140, wire161, wire83, wire179]
def node2_56 : List FreeSupport.Wire := [wire50, wire34, wire75, wire106, wire140, wire161, wire83, wire134, wire179]
def node2_57 : List FreeSupport.Wire := [wire50, wire34, wire75, wire108, wire133, wire140, wire161, wire83, wire179]
def node2_58 : List FreeSupport.Wire := [wire50, wire34, wire75, wire109, wire133, wire140, wire161, wire83, wire179]
def node2_59 : List FreeSupport.Wire := [wire50, wire34, wire75, wire133, wire140, wire161, wire107, wire83, wire179]
def node2_60 : List FreeSupport.Wire := [wire50, wire34, wire75, wire133, wire140, wire161, wire110, wire83, wire179]
def node2_61 : List FreeSupport.Wire := [wire50, wire34, wire76, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_62 : List FreeSupport.Wire := [wire50, wire36, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_63 : List FreeSupport.Wire := [wire50, wire38, wire34, wire75, wire106, wire133, wire140, wire83, wire179]
def node2_64 : List FreeSupport.Wire := [wire50, wire40, wire34, wire75, wire106, wire133, wire140, wire83, wire179]
def node2_65 : List FreeSupport.Wire := [wire50, wire60, wire34, wire75, wire106, wire140, wire161, wire83, wire179]
def node2_66 : List FreeSupport.Wire := [wire50, wire62, wire34, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_67 : List FreeSupport.Wire := [wire50, wire63, wire34, wire75, wire106, wire133, wire161, wire83, wire179]
def node2_68 : List FreeSupport.Wire := [wire50, wire64, wire34, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_69 : List FreeSupport.Wire := [wire50, wire75, wire106, wire133, wire140, wire161, wire83, wire35, wire179]
def node2_70 : List FreeSupport.Wire := [wire51, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_71 : List FreeSupport.Wire := [wire52, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_72 : List FreeSupport.Wire := [wire53, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
def node2_73 : List FreeSupport.Wire := [wire54, wire34, wire75, wire106, wire133, wire140, wire161, wire83, wire179]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_0 : ¬ FreeSupport.attainable 8 node2_0 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_1 : ¬ FreeSupport.attainable 8 node2_1 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_2 : ¬ FreeSupport.attainable 8 node2_2 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_3 : ¬ FreeSupport.attainable 8 node2_3 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_4 : ¬ FreeSupport.attainable 8 node2_4 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_5 : ¬ FreeSupport.attainable 8 node2_5 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_6 : ¬ FreeSupport.attainable 8 node2_6 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_7 : ¬ FreeSupport.attainable 8 node2_7 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_8 : ¬ FreeSupport.attainable 8 node2_8 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_9 : ¬ FreeSupport.attainable 8 node2_9 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_10 : ¬ FreeSupport.attainable 8 node2_10 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_11 : ¬ FreeSupport.attainable 8 node2_11 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_12 : ¬ FreeSupport.attainable 8 node2_12 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_13 : ¬ FreeSupport.attainable 8 node2_13 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_14 : ¬ FreeSupport.attainable 8 node2_14 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_15 : ¬ FreeSupport.attainable 8 node2_15 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_16 : ¬ FreeSupport.attainable 8 node2_16 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_17 : ¬ FreeSupport.attainable 8 node2_17 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_18 : ¬ FreeSupport.attainable 8 node2_18 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_19 : ¬ FreeSupport.attainable 8 node2_19 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_20 : ¬ FreeSupport.attainable 8 node2_20 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_21 : ¬ FreeSupport.attainable 8 node2_21 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_22 : ¬ FreeSupport.attainable 8 node2_22 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_23 : ¬ FreeSupport.attainable 8 node2_23 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_24 : ¬ FreeSupport.attainable 8 node2_24 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_25 : ¬ FreeSupport.attainable 8 node2_25 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_26 : ¬ FreeSupport.attainable 8 node2_26 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_27 : ¬ FreeSupport.attainable 8 node2_27 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_28 : ¬ FreeSupport.attainable 8 node2_28 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_29 : ¬ FreeSupport.attainable 8 node2_29 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_30 : ¬ FreeSupport.attainable 8 node2_30 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_31 : ¬ FreeSupport.attainable 8 node2_31 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_32 : ¬ FreeSupport.attainable 8 node2_32 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_33 : ¬ FreeSupport.attainable 8 node2_33 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_34 : ¬ FreeSupport.attainable 8 node2_34 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_35 : ¬ FreeSupport.attainable 8 node2_35 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_36 : ¬ FreeSupport.attainable 8 node2_36 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_37 : ¬ FreeSupport.attainable 8 node2_37 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_38 : ¬ FreeSupport.attainable 8 node2_38 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_39 : ¬ FreeSupport.attainable 8 node2_39 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_40 : ¬ FreeSupport.attainable 8 node2_40 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_41 : ¬ FreeSupport.attainable 8 node2_41 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_42 : ¬ FreeSupport.attainable 8 node2_42 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_43 : ¬ FreeSupport.attainable 8 node2_43 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_44 : ¬ FreeSupport.attainable 8 node2_44 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_45 : ¬ FreeSupport.attainable 8 node2_45 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_46 : ¬ FreeSupport.attainable 8 node2_46 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_47 : ¬ FreeSupport.attainable 8 node2_47 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_48 : ¬ FreeSupport.attainable 8 node2_48 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_49 : ¬ FreeSupport.attainable 8 node2_49 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_50 : ¬ FreeSupport.attainable 8 node2_50 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_51 : ¬ FreeSupport.attainable 8 node2_51 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_52 : ¬ FreeSupport.attainable 8 node2_52 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_53 : ¬ FreeSupport.attainable 8 node2_53 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_54 : ¬ FreeSupport.attainable 8 node2_54 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_55 : ¬ FreeSupport.attainable 8 node2_55 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_56 : ¬ FreeSupport.attainable 8 node2_56 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_57 : ¬ FreeSupport.attainable 8 node2_57 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_58 : ¬ FreeSupport.attainable 8 node2_58 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_59 : ¬ FreeSupport.attainable 8 node2_59 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_60 : ¬ FreeSupport.attainable 8 node2_60 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_61 : ¬ FreeSupport.attainable 8 node2_61 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_62 : ¬ FreeSupport.attainable 8 node2_62 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_63 : ¬ FreeSupport.attainable 8 node2_63 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_64 : ¬ FreeSupport.attainable 8 node2_64 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_65 : ¬ FreeSupport.attainable 8 node2_65 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_66 : ¬ FreeSupport.attainable 8 node2_66 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_67 : ¬ FreeSupport.attainable 8 node2_67 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_68 : ¬ FreeSupport.attainable 8 node2_68 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_69 : ¬ FreeSupport.attainable 8 node2_69 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_70 : ¬ FreeSupport.attainable 8 node2_70 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_71 : ¬ FreeSupport.attainable 8 node2_71 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_72 : ¬ FreeSupport.attainable 8 node2_72 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject2_node2_73 : ¬ FreeSupport.attainable 8 node2_73 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_0 : ¬ FreeSupport.attainable 9 node1_0 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_1 : ¬ FreeSupport.attainable 9 node1_1 := by
  apply stepCover [node2_41, node2_58, node2_62] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_58 (rejectCons reject2_node2_62 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_2 : ¬ FreeSupport.attainable 9 node1_2 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_3 : ¬ FreeSupport.attainable 9 node1_3 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_4 : ¬ FreeSupport.attainable 9 node1_4 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_5 : ¬ FreeSupport.attainable 9 node1_5 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_6 : ¬ FreeSupport.attainable 9 node1_6 := by
  apply stepCover [node2_41, node2_70] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_70 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_7 : ¬ FreeSupport.attainable 9 node1_7 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_8 : ¬ FreeSupport.attainable 9 node1_8 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_9 : ¬ FreeSupport.attainable 9 node1_9 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_10 : ¬ FreeSupport.attainable 9 node1_10 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_11 : ¬ FreeSupport.attainable 9 node1_11 := by
  apply stepCover [node2_41, node2_73] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_73 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_12 : ¬ FreeSupport.attainable 9 node1_12 := by
  apply stepCover [node2_41, node2_47, node2_53] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_47 (rejectCons reject2_node2_53 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_13 : ¬ FreeSupport.attainable 9 node1_13 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_14 : ¬ FreeSupport.attainable 9 node1_14 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_15 : ¬ FreeSupport.attainable 9 node1_15 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_16 : ¬ FreeSupport.attainable 9 node1_16 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_17 : ¬ FreeSupport.attainable 9 node1_17 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_18 : ¬ FreeSupport.attainable 9 node1_18 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_19 : ¬ FreeSupport.attainable 9 node1_19 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_20 : ¬ FreeSupport.attainable 9 node1_20 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_21 : ¬ FreeSupport.attainable 9 node1_21 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_22 : ¬ FreeSupport.attainable 9 node1_22 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_23 : ¬ FreeSupport.attainable 9 node1_23 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_24 : ¬ FreeSupport.attainable 9 node1_24 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_25 : ¬ FreeSupport.attainable 9 node1_25 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_26 : ¬ FreeSupport.attainable 9 node1_26 := by
  apply stepCover [node2_41, node2_42, node2_51, node2_56, node2_59, node2_61, node2_71] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_42 (rejectCons reject2_node2_51 (rejectCons reject2_node2_56 (rejectCons reject2_node2_59 (rejectCons reject2_node2_61 (rejectCons reject2_node2_71 (rejectNil 8)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_27 : ¬ FreeSupport.attainable 9 node1_27 := by
  apply stepCover [node2_41, node2_60] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_60 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_28 : ¬ FreeSupport.attainable 9 node1_28 := by
  apply stepCover [node2_41, node2_72] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_72 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_29 : ¬ FreeSupport.attainable 9 node1_29 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_30 : ¬ FreeSupport.attainable 9 node1_30 := by
  apply stepCover [node2_41, node2_52] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_52 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_31 : ¬ FreeSupport.attainable 9 node1_31 := by
  apply stepCover [node2_41, node2_46] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_46 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_32 : ¬ FreeSupport.attainable 9 node1_32 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_33 : ¬ FreeSupport.attainable 9 node1_33 := by
  apply stepCover [node2_9] (by decide +kernel)
  exact rejectCons reject2_node2_9 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_34 : ¬ FreeSupport.attainable 9 node1_34 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_35 : ¬ FreeSupport.attainable 9 node1_35 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_36 : ¬ FreeSupport.attainable 9 node1_36 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_37 : ¬ FreeSupport.attainable 9 node1_37 := by
  apply stepCover [node2_10] (by decide +kernel)
  exact rejectCons reject2_node2_10 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_38 : ¬ FreeSupport.attainable 9 node1_38 := by
  apply stepCover [node2_39] (by decide +kernel)
  exact rejectCons reject2_node2_39 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_39 : ¬ FreeSupport.attainable 9 node1_39 := by
  apply stepCover [node2_38] (by decide +kernel)
  exact rejectCons reject2_node2_38 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_40 : ¬ FreeSupport.attainable 9 node1_40 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_41 : ¬ FreeSupport.attainable 9 node1_41 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_42 : ¬ FreeSupport.attainable 9 node1_42 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_43 : ¬ FreeSupport.attainable 9 node1_43 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_44 : ¬ FreeSupport.attainable 9 node1_44 := by
  apply stepCover [node2_7, node2_41, node2_64] (by decide +kernel)
  exact rejectCons reject2_node2_7 (rejectCons reject2_node2_41 (rejectCons reject2_node2_64 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_45 : ¬ FreeSupport.attainable 9 node1_45 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_46 : ¬ FreeSupport.attainable 9 node1_46 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_47 : ¬ FreeSupport.attainable 9 node1_47 := by
  apply stepCover [node2_41, node2_49, node2_69] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_49 (rejectCons reject2_node2_69 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_48 : ¬ FreeSupport.attainable 9 node1_48 := by
  apply stepCover [node2_41, node2_65, node2_67] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_65 (rejectCons reject2_node2_67 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_49 : ¬ FreeSupport.attainable 9 node1_49 := by
  apply stepCover [node2_10, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_10 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_50 : ¬ FreeSupport.attainable 9 node1_50 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_51 : ¬ FreeSupport.attainable 9 node1_51 := by
  apply stepCover [node2_41, node2_55, node2_57] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_55 (rejectCons reject2_node2_57 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_52 : ¬ FreeSupport.attainable 9 node1_52 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_53 : ¬ FreeSupport.attainable 9 node1_53 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_54 : ¬ FreeSupport.attainable 9 node1_54 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_55 : ¬ FreeSupport.attainable 9 node1_55 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_56 : ¬ FreeSupport.attainable 9 node1_56 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_57 : ¬ FreeSupport.attainable 9 node1_57 := by
  apply stepCover [node2_27, node2_41, node2_50] (by decide +kernel)
  exact rejectCons reject2_node2_27 (rejectCons reject2_node2_41 (rejectCons reject2_node2_50 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_58 : ¬ FreeSupport.attainable 9 node1_58 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_59 : ¬ FreeSupport.attainable 9 node1_59 := by
  apply stepCover [node2_14, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_14 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_60 : ¬ FreeSupport.attainable 9 node1_60 := by
  apply stepCover [node2_18, node2_23, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_18 (rejectCons reject2_node2_23 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_61 : ¬ FreeSupport.attainable 9 node1_61 := by
  apply stepCover [node2_19, node2_24, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_19 (rejectCons reject2_node2_24 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_62 : ¬ FreeSupport.attainable 9 node1_62 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_63 : ¬ FreeSupport.attainable 9 node1_63 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_64 : ¬ FreeSupport.attainable 9 node1_64 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_65 : ¬ FreeSupport.attainable 9 node1_65 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_66 : ¬ FreeSupport.attainable 9 node1_66 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_67 : ¬ FreeSupport.attainable 9 node1_67 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_68 : ¬ FreeSupport.attainable 9 node1_68 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_69 : ¬ FreeSupport.attainable 9 node1_69 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_70 : ¬ FreeSupport.attainable 9 node1_70 := by
  apply stepCover [node2_0, node2_41, node2_66] (by decide +kernel)
  exact rejectCons reject2_node2_0 (rejectCons reject2_node2_41 (rejectCons reject2_node2_66 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_71 : ¬ FreeSupport.attainable 9 node1_71 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_72 : ¬ FreeSupport.attainable 9 node1_72 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_73 : ¬ FreeSupport.attainable 9 node1_73 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_74 : ¬ FreeSupport.attainable 9 node1_74 := by
  apply stepCover [node2_38, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_38 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_75 : ¬ FreeSupport.attainable 9 node1_75 := by
  apply stepCover [node2_20, node2_38, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_20 (rejectCons reject2_node2_38 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_76 : ¬ FreeSupport.attainable 9 node1_76 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_77 : ¬ FreeSupport.attainable 9 node1_77 := by
  apply stepCover [node2_28, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_28 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_78 : ¬ FreeSupport.attainable 9 node1_78 := by
  apply stepCover [node2_29, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_29 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_79 : ¬ FreeSupport.attainable 9 node1_79 := by
  apply stepCover [node2_1, node2_8, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_1 (rejectCons reject2_node2_8 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_80 : ¬ FreeSupport.attainable 9 node1_80 := by
  apply stepCover [node2_2, node2_41, node2_44] (by decide +kernel)
  exact rejectCons reject2_node2_2 (rejectCons reject2_node2_41 (rejectCons reject2_node2_44 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_81 : ¬ FreeSupport.attainable 9 node1_81 := by
  apply stepCover [node2_3, node2_40, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_3 (rejectCons reject2_node2_40 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_82 : ¬ FreeSupport.attainable 9 node1_82 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node2_41 : ¬ FreeSupport.attainable 9 node2_41 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_84 : ¬ FreeSupport.attainable 9 node1_84 := by
  apply stepCover [node2_13, node2_21, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_13 (rejectCons reject2_node2_21 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_85 : ¬ FreeSupport.attainable 9 node1_85 := by
  apply stepCover [node2_39, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_39 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_86 : ¬ FreeSupport.attainable 9 node1_86 := by
  apply stepCover [node2_11, node2_39, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_11 (rejectCons reject2_node2_39 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_87 : ¬ FreeSupport.attainable 9 node1_87 := by
  apply stepCover [node2_9, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_9 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_88 : ¬ FreeSupport.attainable 9 node1_88 := by
  apply stepCover [node2_30, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_30 (rejectCons reject2_node2_41 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_89 : ¬ FreeSupport.attainable 9 node1_89 := by
  apply stepCover [node2_12, node2_31, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_12 (rejectCons reject2_node2_31 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_90 : ¬ FreeSupport.attainable 9 node1_90 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_91 : ¬ FreeSupport.attainable 9 node1_91 := by
  apply stepCover [node2_6, node2_26, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_6 (rejectCons reject2_node2_26 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_92 : ¬ FreeSupport.attainable 9 node1_92 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_93 : ¬ FreeSupport.attainable 9 node1_93 := by
  apply stepCover [node2_5, node2_15, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_5 (rejectCons reject2_node2_15 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_94 : ¬ FreeSupport.attainable 9 node1_94 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_95 : ¬ FreeSupport.attainable 9 node1_95 := by
  apply stepCover [node2_9, node2_35, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_9 (rejectCons reject2_node2_35 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_96 : ¬ FreeSupport.attainable 9 node1_96 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_97 : ¬ FreeSupport.attainable 9 node1_97 := by
  apply stepCover [node2_10, node2_16, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_10 (rejectCons reject2_node2_16 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_98 : ¬ FreeSupport.attainable 9 node1_98 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_99 : ¬ FreeSupport.attainable 9 node1_99 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_100 : ¬ FreeSupport.attainable 9 node1_100 := by
  apply stepCover [node2_32, node2_36, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_32 (rejectCons reject2_node2_36 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_101 : ¬ FreeSupport.attainable 9 node1_101 := by
  apply stepCover [node2_33, node2_37, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_33 (rejectCons reject2_node2_37 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_102 : ¬ FreeSupport.attainable 9 node1_102 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_103 : ¬ FreeSupport.attainable 9 node1_103 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_104 : ¬ FreeSupport.attainable 9 node1_104 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_105 : ¬ FreeSupport.attainable 9 node1_105 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_106 : ¬ FreeSupport.attainable 9 node1_106 := by
  apply stepCover [node2_17, node2_34, node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_17 (rejectCons reject2_node2_34 (rejectCons reject2_node2_41 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_107 : ¬ FreeSupport.attainable 9 node1_107 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_108 : ¬ FreeSupport.attainable 9 node1_108 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_109 : ¬ FreeSupport.attainable 9 node1_109 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_110 : ¬ FreeSupport.attainable 9 node1_110 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_111 : ¬ FreeSupport.attainable 9 node1_111 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_112 : ¬ FreeSupport.attainable 9 node1_112 := by
  apply stepCover [node2_25, node2_41, node2_43] (by decide +kernel)
  exact rejectCons reject2_node2_25 (rejectCons reject2_node2_41 (rejectCons reject2_node2_43 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_113 : ¬ FreeSupport.attainable 9 node1_113 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_114 : ¬ FreeSupport.attainable 9 node1_114 := by
  apply stepCover [node2_4, node2_41, node2_45] (by decide +kernel)
  exact rejectCons reject2_node2_4 (rejectCons reject2_node2_41 (rejectCons reject2_node2_45 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_115 : ¬ FreeSupport.attainable 9 node1_115 := by
  apply stepCover [node2_22, node2_41, node2_68] (by decide +kernel)
  exact rejectCons reject2_node2_22 (rejectCons reject2_node2_41 (rejectCons reject2_node2_68 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_116 : ¬ FreeSupport.attainable 9 node1_116 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_117 : ¬ FreeSupport.attainable 9 node1_117 := by
  apply stepCover [node2_41, node2_48, node2_54] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_48 (rejectCons reject2_node2_54 (rejectNil 8)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_118 : ¬ FreeSupport.attainable 9 node1_118 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_119 : ¬ FreeSupport.attainable 9 node1_119 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_120 : ¬ FreeSupport.attainable 9 node1_120 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_121 : ¬ FreeSupport.attainable 9 node1_121 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_122 : ¬ FreeSupport.attainable 9 node1_122 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_123 : ¬ FreeSupport.attainable 9 node1_123 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_124 : ¬ FreeSupport.attainable 9 node1_124 := by
  apply stepCover [node2_41, node2_63] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectCons reject2_node2_63 (rejectNil 8))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_125 : ¬ FreeSupport.attainable 9 node1_125 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_126 : ¬ FreeSupport.attainable 9 node1_126 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_127 : ¬ FreeSupport.attainable 9 node1_127 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_128 : ¬ FreeSupport.attainable 9 node1_128 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_129 : ¬ FreeSupport.attainable 9 node1_129 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_130 : ¬ FreeSupport.attainable 9 node1_130 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_131 : ¬ FreeSupport.attainable 9 node1_131 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_132 : ¬ FreeSupport.attainable 9 node1_132 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_133 : ¬ FreeSupport.attainable 9 node1_133 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_134 : ¬ FreeSupport.attainable 9 node1_134 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_135 : ¬ FreeSupport.attainable 9 node1_135 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_136 : ¬ FreeSupport.attainable 9 node1_136 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_137 : ¬ FreeSupport.attainable 9 node1_137 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_138 : ¬ FreeSupport.attainable 9 node1_138 := by
  apply stepCover [node2_41] (by decide +kernel)
  exact rejectCons reject2_node2_41 (rejectNil 8)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject1_node1_139 : ¬ FreeSupport.attainable 9 node1_139 := by
  apply stepCover [] (by decide +kernel)
  simp
set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
theorem reject0_wires : ¬ FreeSupport.attainable 10 wires := by
  apply stepCover [node1_0, node1_1, node1_2, node1_3, node1_4, node1_5, node1_6, node1_7, node1_8, node1_9, node1_10, node1_11, node1_12, node1_13, node1_14, node1_15, node1_16, node1_17, node1_18, node1_19, node1_20, node1_21, node1_22, node1_23, node1_24, node1_25, node1_26, node1_27, node1_28, node1_29, node1_30, node1_31, node1_32, node1_33, node1_34, node1_35, node1_36, node1_37, node1_38, node1_39, node1_40, node1_41, node1_42, node1_43, node1_44, node1_45, node1_46, node1_47, node1_48, node1_49, node1_50, node1_51, node1_52, node1_53, node1_54, node1_55, node1_56, node1_57, node1_58, node1_59, node1_60, node1_61, node1_62, node1_63, node1_64, node1_65, node1_66, node1_67, node1_68, node1_69, node1_70, node1_71, node1_72, node1_73, node1_74, node1_75, node1_76, node1_77, node1_78, node1_79, node1_80, node1_81, node1_82, node2_41, node1_84, node1_85, node1_86, node1_87, node1_88, node1_89, node1_90, node1_91, node1_92, node1_93, node1_94, node1_95, node1_96, node1_97, node1_98, node1_99, node1_100, node1_101, node1_102, node1_103, node1_104, node1_105, node1_106, node1_107, node1_108, node1_109, node1_110, node1_111, node1_112, node1_113, node1_114, node1_115, node1_116, node1_117, node1_118, node1_119, node1_120, node1_121, node1_122, node1_123, node1_124, node1_125, node1_126, node1_127, node1_128, node1_129, node1_130, node1_131, node1_132, node1_133, node1_134, node1_135, node1_136, node1_137, node1_138, node1_139] (by decide +kernel)
  exact rejectCons reject1_node1_0 (rejectCons reject1_node1_1 (rejectCons reject1_node1_2 (rejectCons reject1_node1_3 (rejectCons reject1_node1_4 (rejectCons reject1_node1_5 (rejectCons reject1_node1_6 (rejectCons reject1_node1_7 (rejectCons reject1_node1_8 (rejectCons reject1_node1_9 (rejectCons reject1_node1_10 (rejectCons reject1_node1_11 (rejectCons reject1_node1_12 (rejectCons reject1_node1_13 (rejectCons reject1_node1_14 (rejectCons reject1_node1_15 (rejectCons reject1_node1_16 (rejectCons reject1_node1_17 (rejectCons reject1_node1_18 (rejectCons reject1_node1_19 (rejectCons reject1_node1_20 (rejectCons reject1_node1_21 (rejectCons reject1_node1_22 (rejectCons reject1_node1_23 (rejectCons reject1_node1_24 (rejectCons reject1_node1_25 (rejectCons reject1_node1_26 (rejectCons reject1_node1_27 (rejectCons reject1_node1_28 (rejectCons reject1_node1_29 (rejectCons reject1_node1_30 (rejectCons reject1_node1_31 (rejectCons reject1_node1_32 (rejectCons reject1_node1_33 (rejectCons reject1_node1_34 (rejectCons reject1_node1_35 (rejectCons reject1_node1_36 (rejectCons reject1_node1_37 (rejectCons reject1_node1_38 (rejectCons reject1_node1_39 (rejectCons reject1_node1_40 (rejectCons reject1_node1_41 (rejectCons reject1_node1_42 (rejectCons reject1_node1_43 (rejectCons reject1_node1_44 (rejectCons reject1_node1_45 (rejectCons reject1_node1_46 (rejectCons reject1_node1_47 (rejectCons reject1_node1_48 (rejectCons reject1_node1_49 (rejectCons reject1_node1_50 (rejectCons reject1_node1_51 (rejectCons reject1_node1_52 (rejectCons reject1_node1_53 (rejectCons reject1_node1_54 (rejectCons reject1_node1_55 (rejectCons reject1_node1_56 (rejectCons reject1_node1_57 (rejectCons reject1_node1_58 (rejectCons reject1_node1_59 (rejectCons reject1_node1_60 (rejectCons reject1_node1_61 (rejectCons reject1_node1_62 (rejectCons reject1_node1_63 (rejectCons reject1_node1_64 (rejectCons reject1_node1_65 (rejectCons reject1_node1_66 (rejectCons reject1_node1_67 (rejectCons reject1_node1_68 (rejectCons reject1_node1_69 (rejectCons reject1_node1_70 (rejectCons reject1_node1_71 (rejectCons reject1_node1_72 (rejectCons reject1_node1_73 (rejectCons reject1_node1_74 (rejectCons reject1_node1_75 (rejectCons reject1_node1_76 (rejectCons reject1_node1_77 (rejectCons reject1_node1_78 (rejectCons reject1_node1_79 (rejectCons reject1_node1_80 (rejectCons reject1_node1_81 (rejectCons reject1_node1_82 (rejectCons reject1_node2_41 (rejectCons reject1_node1_84 (rejectCons reject1_node1_85 (rejectCons reject1_node1_86 (rejectCons reject1_node1_87 (rejectCons reject1_node1_88 (rejectCons reject1_node1_89 (rejectCons reject1_node1_90 (rejectCons reject1_node1_91 (rejectCons reject1_node1_92 (rejectCons reject1_node1_93 (rejectCons reject1_node1_94 (rejectCons reject1_node1_95 (rejectCons reject1_node1_96 (rejectCons reject1_node1_97 (rejectCons reject1_node1_98 (rejectCons reject1_node1_99 (rejectCons reject1_node1_100 (rejectCons reject1_node1_101 (rejectCons reject1_node1_102 (rejectCons reject1_node1_103 (rejectCons reject1_node1_104 (rejectCons reject1_node1_105 (rejectCons reject1_node1_106 (rejectCons reject1_node1_107 (rejectCons reject1_node1_108 (rejectCons reject1_node1_109 (rejectCons reject1_node1_110 (rejectCons reject1_node1_111 (rejectCons reject1_node1_112 (rejectCons reject1_node1_113 (rejectCons reject1_node1_114 (rejectCons reject1_node1_115 (rejectCons reject1_node1_116 (rejectCons reject1_node1_117 (rejectCons reject1_node1_118 (rejectCons reject1_node1_119 (rejectCons reject1_node1_120 (rejectCons reject1_node1_121 (rejectCons reject1_node1_122 (rejectCons reject1_node1_123 (rejectCons reject1_node1_124 (rejectCons reject1_node1_125 (rejectCons reject1_node1_126 (rejectCons reject1_node1_127 (rejectCons reject1_node1_128 (rejectCons reject1_node1_129 (rejectCons reject1_node1_130 (rejectCons reject1_node1_131 (rejectCons reject1_node1_132 (rejectCons reject1_node1_133 (rejectCons reject1_node1_134 (rejectCons reject1_node1_135 (rejectCons reject1_node1_136 (rejectCons reject1_node1_137 (rejectCons reject1_node1_138 (rejectCons reject1_node1_139 (rejectNil 9))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end PEqualNP.Outside.L_meta_27446_aux

theorem PEqualNP.Outside.L_meta_27446 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩) := by
  rintro ⟨⟨gs,o⟩,hf,hs,hr,_,_,_,_,hfirst,hsecond⟩
  cases gs with
  | nil => contradiction
  | cons g gs =>
    cases gs with
    | nil => contradiction
    | cons h rest =>
      change some g = some ⟨.not, [0]⟩ at hfirst
      change some h = some ⟨.and, [1, 5]⟩ at hsecond
      obtain rfl := Option.some.inj hfirst
      obtain rfl := Option.some.inj hsecond
      apply PEqualNP.Outside.L_meta_27446_aux.reject0_wires
      apply PEqualNP.Outside.L_meta_27446_aux.attainable_suffix rest o
      · intro g hg
        apply hf
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
      · change (rest.length + 1 + 1) ≤ 12 at hs
        omega
      · exact hr
