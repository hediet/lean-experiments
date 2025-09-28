import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca

variable [Alphabet]

private def φ {C: LCellAutomata} (b: C.Q) (c: C.Q) := (b, fun a => C.δ a b c)

private def Sp (C: LCellAutomata): LCellAutomata := by
  have x := C.inv_fin_q
  have y := C.inv_decidable_q

  exact {
    Q := C.Q × (C.Q → C.Q)
    δ := fun a b c => φ (C.δ a.fst b.fst c.fst) (c.snd b.fst),
    border := φ C.border C.border,
    embed := fun a => φ (C.embed a) C.border,
  }

private lemma sp_border_passive {C: LCellAutomata} (h: C.passive C.border):
  (Sp C).passive (Sp C).border := by
  simp [CellAutomata.passive, CellAutomata.passive_set, Sp, φ, CellAutomata.δ_of_passive h]

private lemma fst_prop {w} {C: LCellAutomata} (t: ℕ) (i: ℤ):
    ((Sp C).comp w t i).fst = C.comp w t i := by
  induction t generalizing i with
  | zero =>
    simp [LCellAutomata.embed_word, Sp, φ]
    grind
  | succ t ih =>
    rw [LCellAutomata.comp_succ_eq, LCellAutomata.comp_succ_eq]
    rw [CellAutomata.next]
    conv in (Sp C).δ => simp [Sp, φ]
    simp [ih, CellAutomata.next]

private lemma snd_prop (C: LCellAutomata) (w) (t: ℕ) (i: ℤ) (h: t + i + 1 ≥ w.length):
  ((Sp C).comp w t i).snd (C.comp w t (i - 1)) = C.comp w (t + 1) i := by

  induction t generalizing i with
  | zero =>
    rw [LCellAutomata.comp_succ_eq, LCellAutomata.comp_zero, LCellAutomata.comp_zero]
    set c := C.embed_word w
    simp [LCellAutomata.embed_word, Sp]
    have cp1_border : c (i+1) = C.border := by
      have: i + 1 ∉ w.range := by simp [Word.range]; omega
      simp [c, LCellAutomata.embed_word, this]

    split
    case zero.isTrue h_if =>
      have : C.embed (w.get' i h_if) = c i := by simp [c, LCellAutomata.embed_word, h_if]
      simp [φ, this, cp1_border, CellAutomata.next]
    case zero.isFalse h_if =>
      have : c i = C.border := by simp [c, LCellAutomata.embed_word, h_if]
      simp [φ, this, cp1_border, CellAutomata.next]

  | succ t ih =>
    rw [LCellAutomata.comp_succ_eq, CellAutomata.next]
    set c' := (Sp C).comp w t
    conv in (Sp C).δ => simp [Sp]
    set c := C.comp w t
    simp [c', fst_prop]
    rw [←CellAutomata.next]

    have ih := ih (i + 1) (by omega)
    simp [c'] at ih
    rw [ih]
    unfold φ
    simp
    rw [←LCellAutomata.comp_succ_eq]
    rw [←CellAutomata.next]
    rw [←LCellAutomata.comp_succ_eq]



theorem one_step_speed_up_dead (C: tCellAutomata.{u}) (h1: ∀ n, C.t n ≥ n) (h2: C.dead C.border):
  ∃ C': tCellAutomata.{u},
    C'.L = C.L
    ∧ C'.t = Nat.pred ∘ C.t := by

  set LC' := Sp C.toLCellAutomata
  set t' := Nat.pred ∘ C.t
  set F_pos' := { s: LC'.Q | s.snd (C.border) ∈ C.F_pos }
  set C' := tCellAutomata.mk LC' t' F_pos'

  use C'
  constructor
  case h.right => simp [t', C']

  funext w
  set n := w.length

  cases c: n
  case h.left.h.zero =>
    have : w = [] := by simp_all only [ge_iff_le, List.length_eq_zero_iff, n]
    rw [this]

    have border_passive := (CellAutomata.passive_of_dead h2)

    have C'_border_passive: C'.passive C'.border := by
       have := sp_border_passive border_passive
       simp [C', LC', this]

    simp [tCellAutomata.accepts_empty_iff_of_passive border_passive,
      tCellAutomata.accepts_empty_iff_of_passive C'_border_passive]
    simp [F_pos', C', LC', Sp, φ, CellAutomata.δ_of_passive border_passive]


  case h.left.h.succ n' =>

  suffices : ((C'.comp w (t' n) 0).snd C.border ∈ C.F_pos) ↔ C.comp w (C.t n) 0 ∈ C.F_pos
  · have r : (C'.comp w (t' n) 0).snd C.border ∈ C.F_pos ↔ (C'.comp w (t' n) 0) ∈ C'.F_pos := by simp [C', F_pos']
    rw [r] at this
    simp [n] at this
    simp [tCellAutomata.L]
    exact this

  have : C.comp w ((C.t n)-1) (0-1) = C.border := by
    apply LCellAutomata.dead_border_comp
    · simp_all
    · simp [Word.range]
  rw [←this]
  simp only [Function.comp_apply, Nat.pred_eq_sub_one, C', LC', t']
  have x := snd_prop C.toLCellAutomata w ((C.t n)-1) 0


  rw [x]

  have : C.t n - 1 + 1 = C.t n := by
    have : C.t n ≥ n := by simp_all
    have : C.t n > 0 := by omega
    omega

  simp [this]

  have : w.length = n := by simp [n]
  rw [this]

  suffices : ↑(C.t n - 1) + 0 + (1: ℤ) = C.t n;
  · rw [this]
    simp [h1]

  have : C.t n ≥ 1 := by
    rw [c]
    have := h1 (n' + 1)
    omega

  omega

theorem tCellAutomata.linear_time_dead_border (C: tCellAutomata) (h: ∃ c, ∀ n, C.t n ≤ c * n): ∃ C': tCellAutomata,
    C'.L = C.L
    ∧ C'.t = C.t
    ∧ C'.dead C'.border := by
  sorry


theorem one_step_speed_up (C: tCellAutomata.{u}) (h1: ∀ n, C.t n ≥ n) (h2: ∃ c, ∀ n, C.t n ≤ c * n):
  ∃ C': tCellAutomata.{u},
    C'.L = C.L
    ∧ C'.t = Nat.pred ∘ C.t := by

  have ⟨ C'', C''_L, C''_t, C''_dead ⟩ := tCellAutomata.linear_time_dead_border C h2
  rw [←C''_t] at h1
  rw [←C''_L, ←C''_t]
  apply one_step_speed_up_dead C'' h1 C''_dead


/-
theorem const_speed_up (k: ℕ): ℒ (tCellAutomatas |> with_time { f | ∃ k, ∀ n, C.t n ≤ n + k  }) = ℒ (RT) := sorry


theorem const_speed_up1: ℒ (tCellAutomatas |> t⦃ n - 1 + k + 1 ⦄) = ℒ (tCellAutomatas |> t⦃ n - 1 + k ⦄) := sorry


-/
