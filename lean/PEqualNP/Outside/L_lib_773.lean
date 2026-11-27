import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem PEqualNP.Outside.L_lib_773 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool),
  (∀ a b : Fin n, a ≠ b → ∀ c d : Fin m, c ≠ d →
    ¬ (G a c = true ∧ G a d = true ∧ G b c = true ∧ G b d = true)) →
  (∑ c : Fin m, Nat.choose (Finset.univ.filter (fun a : Fin n => G a c = true)).card 2) ≤ Nat.choose n 2) := by
  intro n m G h
  let rows (c : Fin m) := Finset.univ.filter (fun a : Fin n => G a c = true)
  let pairs (c : Fin m) := (rows c).powersetCard 2
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint pairs := by
    intro c hc d hd hcd
    apply Finset.disjoint_left.mpr
    intro s hsc hsd
    obtain ⟨sc, htwo⟩ := Finset.mem_powersetCard.mp hsc
    have sd := (Finset.mem_powersetCard.mp hsd).1
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
    exact h a b hab c d hcd
      ⟨(Finset.mem_filter.mp (sc ha)).2, (Finset.mem_filter.mp (sd ha)).2,
       (Finset.mem_filter.mp (sc hb)).2, (Finset.mem_filter.mp (sd hb)).2⟩
  have sub : Finset.univ.biUnion pairs ⊆ (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro s hs
    obtain ⟨c, _, hsc⟩ := Finset.mem_biUnion.mp hs
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hsc).2⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_biUnion hd] at count
  simpa only [pairs, rows, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using count
