import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_828_aux
open Finset

def level (q E k : Nat) (j : Fin q) : ℤ :=
  ((2^k * E / q : Nat) : ℤ) -
    (if j.val < E - (2^k * E % q) then 1 else 0)

theorem step_up {q E k : Nat} (hq : 0 < q) (j : Fin q) :
    2 * level q E k j ≤ level q E (k+1) j := by
  let v := 2^k * E
  have he : 2^(k+1)*E = 2*v := by simp [v,pow_succ]; ring
  have split : 2*v / q = 2*(v/q) + 2*(v%q)/q := by
    have e := Nat.div_add_mod v q
    conv_lhs => rw [← e]
    rw [Nat.mul_add]
    have heq : 2*(q*(v/q)) = q*(2*(v/q)) := by ring
    rw [heq,Nat.mul_add_div hq]
  have red : 2*v%q = 2*(v%q)%q := by simp [Nat.mul_mod]
  by_cases h : 2*(v%q)<q
  · have ht := Nat.div_eq_of_lt h
    have hm := Nat.mod_eq_of_lt h
    simp only [level,he,split,red,ht,hm,Nat.add_zero,Nat.cast_mul,Nat.cast_ofNat]
    change (2 : ℤ) * (↑(v/q) - (if j.val < E - v%q then 1 else 0)) ≤ _
    split_ifs <;> omega
  · have carry : 1 ≤ 2*(v%q)/q := Nat.le_div_iff_mul_le hq |>.mpr (by omega)
    simp only [level,he,split,red,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change (2 : ℤ) * (↑(v/q) - (if j.val < E - v%q then 1 else 0)) ≤ _
    split_ifs <;> omega

theorem cut_card (q a : Nat) (h : a ≤ q) :
    (∑ j : Fin q, (if j.val < a then (1 : ℤ) else 0)) = a := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < a then (1 : ℤ) else 0)]
  induction q with
  | zero => simp_all
  | succ q ih =>
    rw [Finset.sum_range_succ]
    by_cases ha : a ≤ q
    · rw [ih ha, ite_eq_right (by omega)]
      simp
    · have eq : a = q+1 := by omega
      subst a
      have eq : (∑ i ∈ range q, if i < q+1 then (1:ℤ) else 0) = (∑ _i ∈ range q, (1:ℤ)) :=
        Finset.sum_congr rfl fun i hi => ite_eq_left (by have := Finset.mem_range.mp hi; omega)
      rw [eq]
      simp

theorem level_sum {q E k : Nat} (hq : E < q) (h : 2^k * E % q ≤ E) :
    (∑ j : Fin q, level q E k j) = ((2:ℤ)^k-1) * E := by
  simp only [level,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [cut_card _ _ (by omega)]
  have hd := Nat.div_add_mod (2^k*E) q
  have hh : (q : ℤ) * ↑(2^k*E/q) + ↑(2^k*E%q) = (2:ℤ)^k * ↑E := by exact_mod_cast hd
  rw [Int.natCast_sub h]
  linarith

theorem geom_copies (w : ℕ → ℕ) (k : Nat) (E : Nat) (hw : ∀ i < k, w i = E) :
    (∑ i ∈ Finset.range k, 2^i * w i) + E = 2^k * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, hw k (by omega),pow_succ]
    have := ih (fun i hi => hw i (by omega))
    rw [show 2^k*2*E = 2*(2^k*E) by ring]
    omega

theorem necessary {q E p : Nat} (hq : 1 < q) (hE : 0 < E) (hp : 0 < p)
    (v : Fin p → Fin q → Nat) (row : ∀ i, ∑ j, v i j = E)
    (col : ∀ j, q * (∑ i : Fin p, 2^i.val * v i j) = (2^p-1)*E)
    (b : Nat) (hb : b < p) : 2^b*E % q ≤ E := by
  let : NeZero p := ⟨by omega⟩
  let w (i : Nat) := v (Fin.ofNat p i)
  have wrow (i : Nat) : ∑ j, w i j = E := row _
  have wcol (j : Fin q) : q * (∑ i ∈ range p, 2^i*w i j) = (2^p-1)*E := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => 2^i*w i j)]
    simpa [w,Fin.ofNat_eq_cast] using col j
  let a := p-b
  have eq : p = a+b := by dsimp [a]; omega
  let H (j : Fin q) := ∑ i ∈ range b, 2^i * w (a+i) j
  have bound (j : Fin q) : H j ≤ 2^b*E/q := by
    have mulpart : ∑ i ∈ range b, 2^(a+i)*w (a+i) j = 2^a * H j := by
      simp only [H,Finset.mul_sum,pow_add,Nat.mul_assoc]
    have sub : 2^a * H j ≤ ∑ i ∈ range p, 2^i*w i j := by
      rw [eq,Finset.sum_range_add,mulpart]
      omega
    have hpow : 0 < 2^p := by positivity
    have hlt : (2^p-1)*E < 2^p*E := (Nat.mul_lt_mul_right hE).mpr (by omega)
    have hmul := (Nat.mul_le_mul_left q sub).trans_lt ((wcol j).trans_lt hlt)
    have reorder : q*(2^a*H j) = 2^a*(q*H j) := by ring
    rw [reorder,eq,pow_add,Nat.mul_assoc] at hmul
    exact (Nat.le_div_iff_mul_le (by omega : 0 < q)).mpr (by rw [Nat.mul_comm]; exact (Nat.lt_of_mul_lt_mul_left hmul).le)
  have summed : (∑ j, H j) + E = 2^b*E := by
    simp only [H]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,wrow]
    exact geom_copies (fun _ => E) b E (by simp)
  have upper : (∑ j, H j) ≤ q * (2^b*E/q) := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin q))) (fun j _ => bound j)
  have hqr := Nat.div_add_mod (2^b*E) q
  omega

theorem weighted_telescope (p : Nat) (f : Nat → ℤ) :
    (∑ i ∈ range p, (2:ℤ)^i * (f i - 2*f (i+1))) = f 0 - (2:ℤ)^p * f p := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    ring

theorem sufficient {q E p : Nat} (hq : 1 < q) (he : E < q)
    (period : 2^p % q = 1) (res : ∀ b < p, 2^b*E%q ≤ E) :
    ∃ v : Fin p → Fin q → Nat, (∀ i, ∑ j, v i j = E) ∧
      ∀ j, q*(∑ i : Fin p, 2^i.val * v i j) = (2^p-1)*E := by
  classical
  have close : 2^p*E%q = E := by
    rw [Nat.mul_mod,period,Nat.mod_eq_of_lt he,one_mul,Nat.mod_eq_of_lt he]
  have valid (k : Nat) (hk : k ≤ p) : 2^k*E%q ≤ E := by
    rcases hk.eq_or_lt with rfl|h
    · exact close.le
    · exact res k h
  let f (i : Nat) := level q E (p-i)
  let digit (i : Nat) (j : Fin q) := f i j - 2*f (i+1) j
  have nonneg (i : Nat) (hi : i < p) (j : Fin q) : 0 ≤ digit i j := by
    have hh : p-i = p-(i+1)+1 := by omega
    dsimp [digit,f]
    rw [hh]
    exact sub_nonneg.mpr (step_up (by omega) _)
  have dsum (i : Nat) (hi : i < p) : (∑ j, digit i j) = (E:ℤ) := by
    simp only [digit,f,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [level_sum he (valid _ (by omega)),level_sum he (valid _ (by omega))]
    rw [show p-i = p-(i+1)+1 from by omega,pow_succ]
    ring
  refine ⟨fun i j => (digit i.val j).toNat,?_,?_⟩
  · intro i
    apply Int.ofNat_inj.mp
    push_cast
    simp only [Int.toNat_of_nonneg (nonneg _ i.isLt _)]
    exact dsum _ i.isLt
  · intro j
    have sumint : (∑ i : Fin p, (2:ℤ)^i.val * digit i.val j) = f 0 j := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (2:ℤ)^i * digit i j)]
      change (∑ i ∈ range p, (2:ℤ)^i * (f i j-2*f (i+1) j)) = _
      rw [weighted_telescope p (fun i => f i j)]
      simp [f,level,Nat.mod_eq_of_lt he,Nat.div_eq_of_lt he]
    have target : (q:ℤ)*f 0 j = ((2:ℤ)^p-1)*E := by
      simp only [f,Nat.sub_zero,level,close,Nat.sub_self,Nat.not_lt_zero,ite_false,sub_zero]
      have hd := Nat.div_add_mod (2^p*E) q
      rw [close] at hd
      have hz : (q:ℤ)*↑(2^p*E/q) + ↑E = (2:ℤ)^p * E := by exact_mod_cast hd
      linarith
    have hp0 : 1 ≤ 2^p := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    apply Int.ofNat_inj.mp
    push_cast [Int.natCast_sub hp0]
    simp only [Int.toNat_of_nonneg (nonneg _ (Fin.isLt _) _)]
    rw [sumint,target]

end PEqualNP.Outside.L_lib_828_aux

theorem PEqualNP.Outside.L_lib_828 : ∀ (q E p : ℕ), 1 < q → 0 < E → E < q → 0 < p → 2^p % q = 1 →
  ((∃ v : Fin p → Fin q → ℕ,
    (∀ i, (∑ j, v i j) = E) ∧
    ∀ j, q*(∑ i : Fin p, 2^i.val * v i j) = (2^p-1)*E) ↔
   ∀ b < p, (2^b*E) % q ≤ E) := by
  intro q E p hq hE he hp period
  constructor
  · rintro ⟨v,hrow,hcol⟩
    exact PEqualNP.Outside.L_lib_828_aux.necessary hq hE hp v hrow hcol
  · exact PEqualNP.Outside.L_lib_828_aux.sufficient hq he period
