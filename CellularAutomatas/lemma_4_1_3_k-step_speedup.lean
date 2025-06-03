import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca

lemma CellAutomata.δ_of_passive {C: CellAutomata} {q: C.Q} (h: C.passive q): C.δ q q q = q := by
  simp_all [h, CellAutomata.passive, CellAutomata.passive_set]

lemma CellAutomata.δδ_of_passive {C: CellAutomata} {q: C.Q} (h: C.passive q): δδ q = q := by
  simp_all [h, δδ, CellAutomata.δ_of_passive]

variable [Alphabet]


@[simp]
lemma comp0 (C: LCellAutomata) (c: Config C.Q): C.nextt c 0 = c := by sorry
@[simp]
lemma comp1 (C: LCellAutomata) (c: Config C.Q): C.nextt c 1 = C.next c := by sorry

/-
theorem FCellAutomata.linear_time_dead_border (C: FCellAutomata): ∃ C': FCellAutomata,
    C'.L = C.L
    ∧ C'.time = C.time
    ∧ C'.dead C'.border := by
  sorry
-/

theorem tCellAutomata.linear_time_dead_border (C: tCellAutomata) (h: ∃ c, ∀ n, C.t n ≤ c * n): ∃ C': tCellAutomata,
    C'.L = C.L
    ∧ C'.t = C.t
    ∧ C'.dead C'.border := by
  sorry

def φ {C: LCellAutomata} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)


def Sp (C: LCellAutomata): LCellAutomata := by
  have x := C.inv_fin_q
  have y := C.inv_decidable_q

  exact {
    Q := C.Q × (C.Q → C.Q)
    δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
    border := φ C.border C.border,
    embed := fun a => φ (C.embed a) C.border,
  }

lemma sp_border_passive {C: LCellAutomata} (h: C.passive C.border):
  (Sp C).passive (Sp C).border := by
  simp [CellAutomata.passive, CellAutomata.passive_set, Sp, φ, CellAutomata.δ_of_passive h]


private lemma fst_prop {C: LCellAutomata} (t: ℕ) (i: ℤ):
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


private lemma snd_prop (C: LCellAutomata) (w) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
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

    simp [c', fst_prop]
    rw [←CellAutomata.next]

    have ih := ih (i + 1) (by omega)
    simp [c'] at ih
    rw [ih]
    unfold φ
    simp
    rw [←CellAutomata.comp_succ_eq]
    rw [←CellAutomata.next]
    rw [←CellAutomata.comp_succ_eq]

lemma tCellAutomata.accepts_empty_iff_of_passive {C: tCellAutomata} (h: C.passive C.border):
    C.L [] ↔ C.border ∈ C.F_pos := by
  sorry

lemma tCellAutomata.accepts_empty_iff {C: tCellAutomata}:
    C.L [] ↔ δδt C.border (C.t 0) ∈ C.F_pos := by
  sorry



theorem one_step_speed_up (C: tCellAutomata.{u}) (h1: ∀ n, C.t n ≥ n) (h2: ∃ c, ∀ n, C.t n ≤ c * n):
  ∃ C': tCellAutomata.{u},
    C'.L = C.L
    ∧ C'.t = Nat.pred ∘ C.t := by

  have ⟨ C'', C''_L, C''_t, C''_dead ⟩ := tCellAutomata.linear_time_dead_border C h2

  set LC' := Sp C''.toLCellAutomata
  set t' := Nat.pred ∘ C''.t
  set F_pos' := { s: LC'.Q | s.snd (C''.border) ∈ C''.F_pos }
  set C' := tCellAutomata.mk LC' t' F_pos'

  use C'
  constructor
  case h.right => simp [t', C', C''_t]

  rw [←C''_L]

  funext w
  set n := w.length

  cases c: n
  case h.left.h.zero =>
    have : w = [] := by simp_all only [ge_iff_le, List.length_eq_zero_iff, t', C', n]
    rw [this]

    have border_passive := (CellAutomata.passive_of_dead C''_dead)

    have C'_border_passive: C'.passive C'.border := by
       have := sp_border_passive border_passive
       simp [C', LC', this]

    simp [tCellAutomata.accepts_empty_iff_of_passive border_passive,
      tCellAutomata.accepts_empty_iff_of_passive C'_border_passive]
    simp [F_pos', C', LC', Sp, φ, CellAutomata.δ_of_passive border_passive]


  case h.left.h.succ n' =>

  suffices : ((C'.comp w (t' n) 0).snd C''.border ∈ C''.F_pos) ↔ C''.comp w (C''.t n) 0 ∈ C''.F_pos
  · sorry
  have : C''.comp w ((C''.t n)-1) (0-1) = C''.border := sorry
  rw [←this]
  simp only [Function.comp_apply, Nat.pred_eq_sub_one, C', LC', t']
  have x := snd_prop C''.toLCellAutomata w ((C''.t n)-1) 0


  rw [x]

  have : C''.t n - 1 + 1 = C''.t n := by
    have : C''.t n ≥ n := by simp_all [h1 n]
    have : C''.t n > 0 := by omega
    omega

  simp [this]

  rw [C''_t]

  have : w.length = n := by simp [n]
  rw [this]

  have : C.t n ≥ 1 := sorry

  sorry

/-
theorem const_speed_up (k: ℕ): ℒ (tCellAutomatas |> with_time { f | ∃ k, ∀ n, C.t n ≤ n + k  }) = ℒ (RT) := sorry


theorem const_speed_up1: ℒ (tCellAutomatas |> t⦃ n - 1 + k + 1 ⦄) = ℒ (tCellAutomatas |> t⦃ n - 1 + k ⦄) := sorry


-/
