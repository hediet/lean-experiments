import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some
import CellularAutomatas.ca

variable [Alphabet]
variable {C: FCellAutomata.{u}}

private inductive cQ' (Q: Type u) where
  | border
  | state (s border: Q)
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

syntax "[" term "|" term "]" : term
macro_rules | `([$a | $b]) => `(cQ'.state $a $b)


private def cQ'.unwrap (q: cQ' Q) (b: Q) :=
  match q with
  | border => b
  | state s _b => s

open cQ'
infix:50 " ?? " => cQ'.unwrap


private def state_accepts' { C: FCellAutomata }
| [ s1 | _b1 ] => C.state_accepts s1
| border => C.comp_state_accepts C.border


private def cC' (C: FCellAutomata): FCellAutomata :=
  let _inv_fin_q := C.inv_fin_q;
  let _inv_decidable_q := C.inv_decidable_q;

  {
    Q := cQ' C.Q,
    δ
      | a@([_ | br]), b,            c
      | a,            b@([_ | br]), c
      | a,            b,            c@([_ | br])  => [ C.δ (a ?? br) (b ?? br) (c ?? br) | δδ br ]
      | border,       border,     border          => border
    embed a := state (C.embed a) C.border,
    border := border,
    state_accepts := state_accepts'
  }


theorem lemma_2_4_1_passive_initial_border (C: FCellAutomata.{u}):
  ∃ C': FCellAutomata.{u},
    C'.L = C.L
  ∧ C'.passive C'.border
  ∧ C'.initial C'.border
  -- ∧ DefinesTime.t C' = DefinesTime.t C
  --∧ (C.left_independent ↔ C'.left_independent)
  --∧ (C.right_independent ↔ C'.right_independent)
  := by
  let C' := cC' C
  use C'

  have a1: C'.passive C'.border := by
    simp [CellAutomata.passive, CellAutomata.passive_set, C', cC']

  have a2: C'.initial C'.border := by
    unfold CellAutomata.initial C' cC'
    intro a b c a_1
    simp_all only [C']
    split at a_1
    next x x_1 x_2 st br => simp_all only [reduceCtorEq, C']
    next x x_1 x_2 st br x_3 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 st br x_3 x_4 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 => simp_all only [C']

  have a3: C'.internal_state C'.border := by
    unfold LCellAutomata.internal_state C' cC'
    intro a
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, C']


  have C'_comp (w: Word) (wlen: w.length > 0) t i: (C'.comp w t i) = if i ∈ w.cone t then state (C.comp w t i) (δδt C.border t) else border := by
    induction t generalizing i
    case zero =>
      simp only [LCellAutomata.comp_zero, Word.cone_zero_eq_range, δδt_zero, C']
      unfold LCellAutomata.embed_word
      split
      case isTrue h => simp [cC']
      case isFalse h => simp [cC']

    case succ t ih =>
      have ih2 (i: ℤ): (C'.comp w t i).unwrap (δδt C.border t) = C.comp w t i := by
        rw [ih i]
        simp [unwrap]
        split
        case h_1 h =>
          split at h
          case isTrue => simp_all only [reduceCtorEq, C']
          case isFalse hSplit => simp [C.comp_outside_word_cone_eq_border_pow_t hSplit]
        case h_2 s b h =>
          split at h
          case isFalse hSplit => simp_all only [reduceCtorEq, C']
          case isTrue =>
            injection h with s_ b_
            simp_all

      simp [CellAutomata.comp_succ_eq]
      set c' := C'.comp w t
      conv =>
        pattern C'.next c' i
        unfold CellAutomata.next
      unfold C' cC'
      simp only [C']
      split
      case h_1 _a _b _c st br p | h_2 _a _b _c st br p alt | h_3 _a _b _c st br p alt1 alt2 =>
        conv =>
          pattern state st br ?? br
          simp [unwrap]

        rw [ih] at p
        split at p
        case isFalse h => simp_all only [reduceCtorEq, C', c']
        case isTrue h =>
          injection p with st_eq border_eq
          have : i ∈ w.cone (t + 1) := by
            try simp [Word.cone_prop' h]
            try simp [Word.cone_prop'' h]

          rw [border_eq] at ih2
          simp [this, δδt_succ, border_eq, ih2, ←st_eq]
          simp [CellAutomata.next]

      case h_4 h1 h2 h3 =>
        suffices : i ∉ w.cone (t + 1)
        · simp [this]
        rw [ih (i-1)] at h1
        rw [ih i] at h2
        rw [ih (i+1)] at h3
        simp_all [ite_eq_right_iff, reduceCtorEq, imp_false, c', C', Word.cone_succ_not wlen]

  have a4: C'.L = C.L := by
    rw [L_eq_iff]
    intro w
    by_cases c: w.length > 0
    case pos =>
      suffices : C'.config_accepts ∘ C'.comp w = C.config_accepts ∘ C.comp w
      simp [FCellAutomata.accepts_iff, FCellAutomata.comp_accepts]
      · simp [this]

      funext t
      simp [FCellAutomata.config_accepts]
      rw [C'_comp]
      simp [C', cC', state_accepts', Word.zero_mem_cone c]
      exact c -- question: why do I need exact?

    case neg =>
      simp at c
      simp [c]
      rw [FCellAutomata.accepts_empty_passive a1]
      simp [C', cC', state_accepts', FCellAutomata.accepts_empty_iff_comp_state_accepts_border]

  simp [a1, a2, a3, a4]
