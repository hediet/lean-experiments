import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca


variable [Alphabet]


@[simp]
lemma comp0 (C: LCellAutomata) (c: Config C.Q): C.nextt c 0 = c := by sorry
@[simp]
lemma comp1 (C: LCellAutomata) (c: Config C.Q): C.nextt c 1 = C.next c := by sorry




def φ {C: tCellAutomata} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)


def Sp (C: tCellAutomata): tCellAutomata := by
  have x := C.inv_fin_q
  have y := C.inv_decidable_q

  exact {
    Q := C.Q × (C.Q → C.Q)
    δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
    border := φ C.border C.border,
    embed := fun a => φ (C.embed a) C.border,
    t := C.t ∘ Nat.pred,
    F_pos := { q | q.fst ∈ C.F_pos },
  }


lemma foo1 {C: tCellAutomata} (t: ℕ) (i: ℤ):
  ((Sp C).comp w t i).fst = C.comp w t i := by

  induction t generalizing i with
  | zero =>
    simp [LCellAutomata.embed_word, Sp, φ]
    split
    · simp
    · simp
  | succ t ih =>
    rw [CellAutomata.comp_succ_eq]
    set c := (Sp C).comp w t
    rw [CellAutomata.comp_succ_eq, CellAutomata.next]
    simp [Sp, ih, φ]
    rw [←CellAutomata.next]


lemma foo {C: tCellAutomata} (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
  ((Sp C).comp w t i).snd (C.comp w t (i - 1)) = C.comp w (t + 1) i := by

  induction t generalizing i with
  | zero =>
    rw [CellAutomata.comp_succ_eq]
    set c := C.comp w 0

    simp [LCellAutomata.comp]
    simp [LCellAutomata.embed_word, Sp]

    have cp1_border : c (i+1) = C.border := by
      have: i + 1 ∉ w.range := by
        simp [Word.range]
        omega
      simp [c, LCellAutomata.embed_word, this]

    split
    case zero.isTrue h' =>
      have h1 : C.embed (w.get' i h') = c i := by
        simp [c, LCellAutomata.embed_word, h']

      simp [φ, h1, cp1_border, CellAutomata.next]
    case zero.isFalse h' =>
      have : c i = C.border := by simp [c, LCellAutomata.embed_word, h']
      simp [φ, this, cp1_border, CellAutomata.next]

  | succ t ih =>
    rw [CellAutomata.comp_succ_eq, CellAutomata.next]
    set c' := (Sp C).comp w t
    conv =>
      pattern (Sp C).δ
      simp [Sp]
    set c := C.comp w t

    simp [c', foo1]
    rw [←CellAutomata.next]

    have ih := ih (i + 1) (by omega)
    simp [c'] at ih
    rw [ih]
    unfold φ
    simp
    rw [←CellAutomata.comp_succ_eq]
    rw [←CellAutomata.next]
    rw [←CellAutomata.comp_succ_eq]










theorem const_speed_up (k: ℕ): ℒ (tCellAutomatas |> t⦃ n + k ⦄) = ℒ (RT) := sorry


theorem const_speed_up1: ℒ (tCellAutomatas |> t⦃ n - 1 + k + 1 ⦄) = ℒ (tCellAutomatas |> t⦃ n - 1 + k ⦄) := sorry





--instance : Fintype { w: List α | w.length = n } where
--  elems := (Fintype.elems (Vector α n)).image (λ v => ⟨v.toList, by simp⟩)







noncomputable def t_max [DefinesTime CA] (ca: CA) (n: ℕ): WithTop ℕ :=
  Finset.max' ((time ca '' { w: Word | w.length = n }).toFinset) (by sorry)

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

noncomputable def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
  (t_max ca n).get (by simp_all[h, halts, Option.isSome_iff_ne_none])

def OCA_L { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.left_independent ca

def OCA_R { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.right_independent ca

def with_time { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))


syntax "t⦃" term "⦄" : term
macro_rules | `(t⦃ $expr ⦄) => `(with_time { fun $(Lean.mkIdent `n) => $expr })

def RT := tCellAutomatas |> t⦃ n - 1 ⦄







theorem OCA_L_equiv_FCA: ℒ (FCellAutomatas) = ℒ (FCellAutomatas |> OCA_L) := sorry

-- Open problems!
theorem X: ℒ (RT) ≠ ℒ (FCellAutomatas |> t⦃ 2 * n ⦄) := sorry
