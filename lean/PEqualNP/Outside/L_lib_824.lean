import PEqualNP.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_824_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def Back (n : Nat) (gs : List Gate) : Prop := ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < n+j

theorem back_cons (n : Nat) (g : Gate) (gs : List Gate) :
    Back n (g :: gs) ↔ (∀ i ∈ g.inputs, i < n) ∧ Back (n+1) gs := by
  constructor
  · intro h
    constructor
    · simpa using h 0 (by simp)
    · intro j hj i hi
      have h' := h (j+1) (by simpa using hj) i (by simpa using hi)
      omega
  · rintro ⟨h, t⟩ j hj i hi
    cases j with
    | zero => simpa using h i (by simpa using hi)
    | succ j =>
      have h' := t j (by simpa using hj) i (by simpa using hi)
      omega

theorem back_replace (pre post : List Gate) (g h : Gate) (hs : ∀ i ∈ h.inputs, i ∈ g.inputs)
    (n : Nat) (hb : Back n (pre ++ g :: post)) : Back n (pre ++ h :: post) := by
  induction pre generalizing n with
  | nil =>
    obtain ⟨ha,ht⟩ := (back_cons ..).mp hb
    exact (back_cons ..).mpr ⟨fun i hi => ha i (hs i hi), ht⟩
  | cons a pre ih =>
    obtain ⟨ha,ht⟩ := (back_cons ..).mp hb
    exact (back_cons ..).mpr ⟨ha,ih (n+1) ht⟩

noncomputable def paid (g : Gate) : Bool := @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def LegalGate (g : Gate) : Prop := g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def sig (v : Bool) : Int := if v then -1 else 1

def evalGate (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def choices (isAnd : Bool) (a b : Nat) : Fin 4 → Gate :=
  ![⟨.or,[a]⟩, ⟨.or,[b]⟩, if isAnd then ⟨.mod 2,[a,b]⟩ else ⟨.and,[]⟩, if isAnd then ⟨.and,[]⟩ else ⟨.mod 2,[a,b]⟩]

theorem admissible (s : Bool) (a b : Nat) (j : Fin 4) :
    LegalGate (choices s a b j) ∧ paid (choices s a b j) = false ∧
      ∀ i ∈ (choices s a b j).inputs, i ∈ [a,b] := by
  fin_cases j <;> cases s <;> simp [choices,LegalGate,paid]

theorem identity (s : Bool) (a b : Nat) (w : List Bool) (h : Bool → Bool) :
    2 * sig (h (evalGate w ⟨if s then .and else .or, [a,b]⟩)) =
      sig (h (evalGate w (choices s a b 0))) + sig (h (evalGate w (choices s a b 1))) +
      sig (h (evalGate w (choices s a b 2))) - sig (h (evalGate w (choices s a b 3))) := by
  cases s <;> cases ha : (w[a]?).getD false <;> cases hb : (w[b]?).getD false <;>
    simp [evalGate,choices,GateOp.eval,List.getD,ha,hb] <;> ring

theorem replace (n : Nat) (C : Circuit) (hb : Back n C.gates) (hl : ∀ g ∈ C.gates, LegalGate g)
    (hc : 0 < C.gates.countP paid) : ∃ D : Fin 4 → Circuit,
    (∀ i, (Back n (D i).gates ∧ ∀ g ∈ (D i).gates, LegalGate g) ∧ (D i).gates.countP paid < C.gates.countP paid) ∧
    ∀ x : Fin n → Bool, 2 * sig (C.eval (List.ofFn x)) = sig ((D 0).eval (List.ofFn x)) +
      sig ((D 1).eval (List.ofFn x)) + sig ((D 2).eval (List.ofFn x)) - sig ((D 3).eval (List.ofFn x)) := by
  classical
  obtain ⟨gs,o⟩ := C
  obtain ⟨g,hg,hpaid⟩ := List.countP_pos_iff.mp hc
  obtain ⟨pre,post,hs⟩ := List.append_of_mem hg
  change gs = _ at hs
  subst gs
  obtain ⟨op,ins⟩ := g
  have hh : (op = .and ∨ op = .or) ∧ ins.length = 2 := by simpa [paid] using hpaid
  obtain ⟨a,b,rfl⟩ : ∃ a b, ins = [a,b] := by
    cases ins with
    | nil => simp at hh
    | cons a as => cases as with
      | nil => simp at hh
      | cons b bs => exact ⟨a,b,by have := hh.2; simp_all⟩
  obtain ⟨s, rfl⟩ : ∃ s : Bool, op = (if s then .and else .or) := by
    rcases hh.1 with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  refine ⟨fun j => ⟨pre ++ choices s a b j :: post, o⟩, ?_, ?_⟩
  · intro j
    obtain ⟨hlegal,hfree,hinputs⟩ := admissible s a b j
    refine ⟨⟨back_replace pre post _ _ hinputs n hb, ?_⟩, ?_⟩
    · intro g hg
      change g ∈ pre ++ choices s a b j :: post at hg
      simp only [List.mem_append,List.mem_cons] at hg
      rcases hg with h | rfl | h
      · exact hl g (List.mem_append_left _ h)
      · exact hlegal
      · exact hl g (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    · change (pre ++ choices s a b j :: post).countP paid < (pre ++ _ :: post).countP paid
      simp [List.countP_append,hpaid,hfree]
  · intro x
    let step := fun (w : List Bool) (g : Gate) => w ++ [evalGate w g]
    let w := pre.foldl step (List.ofFn x)
    let h := fun (v : Bool) => (post.foldl step (w ++ [v])).getD o false
    simpa only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, h,w,step,evalGate] using identity s a b w h

end PEqualNP.Outside.L_lib_824_aux

theorem PEqualNP.Outside.L_lib_824 : ∀ n : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let sig := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ C : Circ, legal n C → 0 < cost C →
    ∃ D : Fin 4 → Circ,
      (∀ i, legal n (D i) ∧ cost (D i) < cost C) ∧
      ∀ x : Fin n → Bool,
        let bits := List.ofFn x
        2*sig (C.eval bits) = sig ((D 0).eval bits) + sig ((D 1).eval bits) +
          sig ((D 2).eval bits) - sig ((D 3).eval bits) := by
  intro n
  dsimp only
  intro C h hc
  exact PEqualNP.Outside.L_lib_824_aux.replace n C h.1 h.2 hc
