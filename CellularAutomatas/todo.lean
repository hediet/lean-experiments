import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca


variable [Alphabet]


/-

noncomputable def t_max [DefinesTime CA] (ca: CA) (n: ℕ): WithTop ℕ :=
  Finset.max' ((time ca '' { w: Word | w.length = n }).toFinset) (by sorry)

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

def with_time { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))


syntax "t⦃" term "⦄" : term
macro_rules | `(t⦃ $expr ⦄) => `(with_time { fun $(Lean.mkIdent `n) => $expr })

def RT := tCellAutomatas |> t⦃ n - 1 ⦄







--instance : Fintype { w: List α | w.length = n } where
--  elems := (Fintype.elems (Vector α n)).image (λ v => ⟨v.toList, by simp⟩)







noncomputable def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
  (t_max ca n).get (by simp_all[h, halts, Option.isSome_iff_ne_none])

def OCA_L { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.left_independent ca

def OCA_R { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.right_independent ca








theorem OCA_L_equiv_FCA: ℒ (FCellAutomatas) = ℒ (FCellAutomatas |> OCA_L) := sorry

-- Open problems!
theorem X: ℒ (RT) ≠ ℒ (FCellAutomatas |> t⦃ 2 * n ⦄) := sorry

-/
