import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some_defs
import CellularAutomatas.find_some
import CellularAutomatas.ca

variable [Alphabet]


def cC' (C: FCellAutomata): FCellAutomata :=
  let _h := C.inv_fin_q;
  let _x := C.inv_decidable_q;
  {
    Q := C.Q × Option Bool,
    δ := fun (a, _fa) (b, fb) (c, _fc) =>
      let r := C.δ a b c; (r, fb.or (C.state_accepts r)),
    inv_fin_q := instFintypeProd C.Q (Option Bool),
    embed := fun a => (C.embed a, C.state_accepts (C.embed a)),
    border := (C.border, C.state_accepts C.border),
    state_accepts := Prod.snd
  }


theorem lemma_2_3_1_FCellAutomata_accept_delta_closed (C: FCellAutomata.{u}):
  ∃ C': FCellAutomata.{u},
    C'.L = C.L
  --∧ DefinesTime.t C' = DefinesTime.t C
  ∧ C'.accept_delta_closed
:= by

  let _h := C.inv_fin_q;
  let _x := C.inv_decidable_q;
  let C' :=  cC' C


  have h1 (w: Word) t i: C.comp w t i = (C'.comp w t i).fst  := by
    induction t generalizing i with
    | zero =>
      simp [LCellAutomata.embed_word, C', cC']
      split
      next h_1 => simp_all
      next h_1 => simp_all

    | succ t ih =>
      simp_all [CellAutomata.comp_succ_eq, CellAutomata.next, C', cC']


  have h2 (w: Word) t: (C'.comp w t 0).snd = find_some_bounded (C.comp_accepts w) (t + 1) := by
    induction t with
    | zero =>
      simp [C', LCellAutomata.embed_word, find_some_bounded_succ, FCellAutomata.config_accepts, FCellAutomata.comp_accepts]

      split
      · simp [cC']
      · simp [cC']

    | succ t ih =>
      simp [CellAutomata.comp_succ_eq, CellAutomata.next]
      rw [find_some_bounded_succ]
      rw [←ih]
      simp [CellAutomata.comp_succ_eq, FCellAutomata.comp_accepts]
      have : C.comp w t = Prod.fst ∘ C'.comp w t := by
        have x := h1 w t
        funext i
        simp_all

      rw [this]
      set c := C'.comp w t
      simp [FCellAutomata.config_accepts, CellAutomata.next, C', cC']

  have h3: C'.L = C.L := by
    rw [L_eq_iff]
    intro w
    simp [FCellAutomata.accepts_iff]
    have : C'.comp_accepts w = find_some_bounded (C.comp_accepts w) ∘ Nat.succ := by
      funext t
      rw [comp_accepts_eq]
      conv =>
        pattern C'.state_accepts
        simp [C', cC']
      simp [h2]

    rw [this]
    simp [find_some_of_succ]



  have h4: C'.accept_delta_closed := by

    unfold FCellAutomata.accept_delta_closed
    constructor
    set val := true
    pick_goal 2
    set val := false
    case left | right =>
      suffices : ∀ a b c, C'.state_accepts b = some val → C'.state_accepts (C'.δ a b c) = some val
      · simp_all [CellAutomata.delta_closed_set, FCellAutomata.F_pos, FCellAutomata.F_neg, val]
      intro a b c h

      suffices : (C'.δ a b c).snd = val
      · simp_all [C', cC']

      have : b.snd = val := by
        obtain ⟨ b1, b2 ⟩ := b
        cases b2
        · simp [C', cC', C', cC'] at h
        · simp_all [C', cC', C', cC']

      simp_all [C', cC', val]

  use C'
