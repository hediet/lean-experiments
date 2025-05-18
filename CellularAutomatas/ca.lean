import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some_defs
import CellularAutomatas.find_some

lemma δδt_succ {C: CellAutomata} {q: C.Q} {t: ℕ} : δδt q (t + 1) = δδ (δδt q t) := by
  simp [δδt, apply_iterated_succ_apply']

@[simp]
lemma δδt_zero {C: CellAutomata} {q: C.Q} : δδt q 0 = q := by
  simp [δδt]



lemma CellAutomata.next_state_of_closed_set_state
  {C: CellAutomata} {S} {c: Config C.Q} {i} (h1: C.delta_closed_set S) (h2: c i ∈ S):
    C.next c i ∈ S := by
  unfold CellAutomata.next
  unfold CellAutomata.delta_closed_set at h1
  exact h1 (c (i - 1)) ⟨c i, h2⟩ (c (i + 1))



variable [Alphabet]


@[simp]
lemma empty_word_range: Word.range [] = {} := by
  unfold Word.range
  ext x
  simp_all


@[simp]
lemma LCellAutomata.comp_zero {C: LCellAutomata} {w}: C.comp w 0 = C.embed_word w := by rfl


def FCellAutomata.comp_accepts (C: FCellAutomata) (w) := C.config_accepts ∘ C.comp w


-- noncomputable def FCellAutomata.accepts' {C: FCellAutomata} (w) := find_some (C.comp_accepts w) == some true

lemma FCellAutomata.time_eq {C: FCellAutomata} {w}: C.time w = find_some_idx (C.comp_accepts w) := by
  simp [←min_nat_eq, FCellAutomata.time, comp_accepts, FCellAutomata.config_accepts]

lemma FCellAutomata.time_eq_none_iff {C: FCellAutomata} {w} : C.time w = none ↔ ∀ t, C.comp_accepts w t = none := by
  simp [FCellAutomata.time_eq, find_some_idx_eq_none_iff]


lemma FCellAutomata.time_eq_some_iff {C: FCellAutomata} {w t}:
    C.time w = some t ↔ ∃ val, C.comp_accepts w t = some val ∧ ∀ i < t, C.comp_accepts w i = none := by
  simp only [FCellAutomata.time_eq, find_some_idx_eq_some_iff]




lemma FCellAutomata.comp_accepts_eq_config_accepts_comp {C: FCellAutomata} {w} {t}: C.comp_accepts w t = C.config_accepts (C.comp w t) := by
  simp [comp_accepts]

lemma FCellAutomata.accepts_iff {C: FCellAutomata} {w}: C.accepts w ↔ find_some (C.comp_accepts w) = some true := by
  simp only [FCellAutomata.accepts, FCellAutomata.time_eq, find_some_idx, ←comp_accepts_eq_config_accepts_comp, find_some]
  cases c: find_some_idxd (C.comp_accepts w)
  case none =>
    simp_all
  case some val =>
    rw [find_some_idxd_eq_some_iff] at c
    simp only [Option.map_some', find_some, c]


def uniform_config {C: CellAutomata} (q: C.Q): Config C.Q := fun _ => q



lemma FCellAutomata.empty_word_config_eq_uniform_border {C: FCellAutomata}: C.embed_word [] = uniform_config C.border := by
  funext i
  simp [LCellAutomata.embed_word, uniform_config, uniform_config]



lemma FCellAutomata.uniform_state_eq {C: FCellAutomata} {q: C.Q}: C.nextt (uniform_config q) = uniform_config ∘ (δδt q) := by
  funext t i
  simp only [CellAutomata.nextt, δδt, Function.comp_apply, uniform_config]

  induction t generalizing i
  case h.h.zero =>
    simp [uniform_config, apply_iterated_zero]
  case h.h.succ n ih =>
    simp [apply_iterated_succ_apply', ih, δδ, CellAutomata.next, uniform_config]

lemma FCellAutomata_comp_empty_eq_uniform {C: FCellAutomata}: C.comp [] = uniform_config ∘ (δδt C.border) := by
  simp [LCellAutomata.comp, FCellAutomata.empty_word_config_eq_uniform_border, FCellAutomata.uniform_state_eq]


def Word.cone (w: Word) (t: ℕ): Set ℤ := { i: ℤ | -t ≤ i ∧ i < w.length + t }

instance (w: Word) (t: ℕ) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | -t ≤ i ∧ i < w.length + t })]:
  Decidable (i ∈ (Word.cone w t)) := d

lemma Word.cone_prop {w: Word} {t: ℕ} {i: ℤ} (d: ℤ) (h: i ∉ w.cone (t + 1)) (h2: d.natAbs ≤ 1): (i + d) ∉ w.cone t := by
  simp_all [Word.cone]
  omega

lemma Word.cone_prop' {w: Word} {t: ℕ} {i: ℤ} { d: ℤ } (h: (i + d) ∈ w.cone t) (h2: d.natAbs ≤ 1): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega

lemma Word.cone_prop'' {w: Word} {t: ℕ} {i: ℤ} (h: i ∈ w.cone t): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega


lemma Word.cone_succ {w: Word} {t: ℕ} {i: ℤ} (h1: i - 1 ∈ w.cone t) (h2: i + 1 ∈ w.cone t): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega

lemma Word.cone_succ_not {w: Word} {t: ℕ} {i: ℤ} (wlen: w.length > 0) (h1: i - 1 ∉ w.cone t) (h2: i ∉ w.cone t) (h3: i + 1 ∉ w.cone t): i ∉ w.cone (t + 1) := by
  simp_all [cone]
  omega

@[simp]
lemma Word.cone_zero_eq_range {w: Word}: w.cone 0 = w.range := by simp [Word.cone, Word.range]

def Word.get_cone_0 {w: Word} {i} (h: i ∈ w.cone 0) := w.get' i (Word.cone_zero_eq_range ▸ h)

lemma embed_word_eq_embed {C: LCellAutomata} {w: Word} {i} (h: i ∈ w.cone 0): C.embed_word w i = C.embed (w.get_cone_0 h) := by
  rw [Word.cone_zero_eq_range] at h
  simp_all [LCellAutomata.embed_word, Word.get_cone_0]

lemma Word.zero_mem_cone {w: Word} (h: w.length > 0) (t): 0 ∈ w.cone t := by
  simp [Word.cone]
  omega

def FCellAutomata.comp_state_accepts { C: FCellAutomata } (q: C.Q) :=
  find_some_bounded (C.state_accepts ∘ δδt q) C.inv_fin_q.card == some true

@[simp]
lemma FCellAutomata.uniform_config_accepts_eq {C: FCellAutomata}: (C.config_accepts ∘ uniform_config) = C.state_accepts := by
  funext
  simp [FCellAutomata.config_accepts, uniform_config]

def state_accepts_repeatingFunction (C: FCellAutomata): RepeatingFunction (C.state_accepts ∘ δδt C.border) := by
  apply repeating_function_of_composition
  unfold δδt
  apply repeating_function_of_iterate_fin_type (C.inv_fin_q)


lemma FCellAutomata.accepts_empty_iff_comp_state_accepts_border {C: FCellAutomata}: C.accepts [] ↔ C.comp_state_accepts C.border = true := by
  simp only [accepts_iff, comp_accepts, FCellAutomata_comp_empty_eq_uniform, comp_state_accepts, beq_iff_eq]
  simp only [←Function.comp_assoc, FCellAutomata.uniform_config_accepts_eq]
  rw [←find_some_bounded_eq_find_some_of_repeating_function (state_accepts_repeatingFunction C)]
  simp [state_accepts_repeatingFunction, RepeatingFunction, repeating_function_of_composition, repeating_function_of_iterate_fin_type ]



instance h {C: FCellAutomata}: Nonempty C.Q := ⟨ C.border ⟩

@[simp]
lemma CellAutomata.Q_card_gt_zero {C: FCellAutomata}: C.inv_fin_q.card > 0 := by
  have x := C.inv_fin_q.card_ne_zero
  omega

lemma FCellAutomata.δδ_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδ q = q := by
  simp_all [h, δδ, CellAutomata.passive, CellAutomata.passive_set]

@[simp]
lemma FCellAutomata.δδn_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδt q t = q := by
  simp_all [δδt, δδ, apply_iterated_fixed (FCellAutomata.δδ_of_passive h)]

lemma FCellAutomata.state_pow_accepts_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): C.comp_state_accepts q = (C.state_accepts q = some true) := by
  simp [FCellAutomata.comp_state_accepts, find_some_bounded_eq_some_iff, FCellAutomata.δδn_of_passive h]
  intro h2
  use 0
  simp

lemma FCellAutomata.accepts_empty_passive {C: FCellAutomata} (h: C.passive C.border):
    C.accepts [] ↔ C.state_accepts C.border = some true := by
  rw [FCellAutomata.accepts_empty_iff_comp_state_accepts_border]
  rw [FCellAutomata.state_pow_accepts_of_passive h]




lemma CellAutomata.nextt_succ_eq (C: LCellAutomata) (c: Config C.Q): C.nextt c (t + 1) = C.next (C.nextt c t) := by
  simp [CellAutomata.nextt, apply_iterated_succ_apply']


lemma CellAutomata.comp_succ_eq (C: LCellAutomata): C.comp w (t + 1) = C.next (C.comp w t) := by
  funext i
  simp [LCellAutomata.comp, CellAutomata.nextt_succ_eq]


lemma LCellAutomata.comp_outside_word_cone_eq_border_pow_t (C: LCellAutomata) {w: Word} {t: ℕ} {i: ℤ} (h: i ∉ w.cone t):
    C.comp w t i = δδt C.border t := by

  induction t generalizing i
  case zero =>
    simp_all [LCellAutomata.comp, CellAutomata.nextt, δδt, LCellAutomata.embed_word, Word.cone_zero_eq_range, not_true_eq_false]
  case succ t ih =>
    have h1 := ih $ Word.cone_prop 0 h (by simp)
    have h2 := ih $ Word.cone_prop (-1) h (by simp)
    have h3 := ih $ Word.cone_prop 1 h (by simp)
    have x: (i + -1) = i - 1 := by rfl

    rw [CellAutomata.comp_succ_eq]
    rw [δδt_succ]
    set c := C.comp w t
    simp_all [CellAutomata.next, δδ]


lemma neq_of_internal_state {C: LCellAutomata} (q: C.Q) {w i} (h1: i ∈ w.cone 0) (h3: C.internal_state q): C.embed_word w i ≠ q := by
  rw [embed_word_eq_embed h1]
  aesop

lemma next_eq_of_initial {C: LCellAutomata} { q: C.Q } {c: Config C.Q} {i: ℤ} (h1: C.initial q) (h2: C.next c i = q): c i = q := by
  subst h2
  apply h1
  · rfl

lemma comp_eq_of_initial {C: LCellAutomata} { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: C.initial q) (h2: C.comp w (t+1) i = q):
    C.comp w t i = q := by
  simp [CellAutomata.comp_succ_eq] at h2
  exact next_eq_of_initial h1 h2

lemma LCellAutomata.initial_internal_of_cone (C: LCellAutomata) { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: i ∈ w.cone 0) (h2: C.initial q) (h3: C.internal_state q):
    C.comp w t i ≠ q := by

  induction t
  case zero =>
    simp [h3, neq_of_internal_state q h1]
  case succ t ih =>
    by_contra eq
    simp_all only [ne_eq, not_true_eq_false, comp_eq_of_initial h2 eq]


lemma next_initial { C: LCellAutomata } { q: C.Q } { w: Word } { t: ℕ } (h1: C.initial q) (h2: C.next (C.comp w t) i = q): C.comp w t i = q :=
  by
  subst h2
  apply h1
  · rfl

lemma L_eq_iff (C C': FCellAutomata): C'.L = C.L ↔ (∀ w, C'.accepts w ↔ C.accepts w) := by
  unfold FCellAutomata.L
  rw [Set.ext_iff]
  rfl



noncomputable def FCellAutomata.time' (C: FCellAutomata) (w: Word): ℕ := (C.time w).getD 0


lemma FCellAutomata.accepts_iff_time (C: FCellAutomata) (w: Word):
    C.accepts w ↔ C.comp_accepts w (C.time' w) = some true := by
  unfold FCellAutomata.time'
  rw [time_eq]
  rw [C.accepts_iff]
  rw [find_some_eq_val_at_find_some_idx (C.comp_accepts w)]


inductive TimeCases (C: FCellAutomata) (w): Prop
| none (h1: C.time w = none) (h2: C.time' w = 0)
| some t (h1: C.time w = some t) (h2: C.time' w = t)

lemma tc C w: TimeCases C w := by
  cases c: C.time w
  case none => simp [TimeCases.none, c, FCellAutomata.time']
  case some => simp [TimeCases.some, c, FCellAutomata.time']

lemma comp_accepts_eq {C: FCellAutomata} {t: ℕ} {w: Word}: C.comp_accepts w t = C.state_accepts (C.comp w t 0) := by
  simp [FCellAutomata.comp_accepts, FCellAutomata.config_accepts]


@[simp]
lemma accept_delta_closed' (C: FCellAutomata) (h: C.accept_delta_closed) (k: ℕ):
    C.comp_accepts w (C.time' w + k) = C.comp_accepts w (C.time' w) := by
  induction k
  case zero => simp
  case succ k ih =>
    cases tc C w
    case none h1 h2 => simp_all [FCellAutomata.time_eq_none_iff.mp h1]
    case some t h1 h2 =>
      simp_all only [h2]

      have ⟨ accepts, ⟨ h_accepts, _ ⟩ ⟩ := FCellAutomata.time_eq_some_iff.mp h1

      rw [←ih]
      simp only [comp_accepts_eq] at *

      have : (t + (k + 1)) = (t + k) + 1 := by omega
      simp only [this, CellAutomata.comp_succ_eq]
      set c := C.comp w (t + k)
      unfold FCellAutomata.accept_delta_closed at h

      cases c_accepts: accepts
      case false =>
        have : c 0 ∈ C.F_neg := by simp_all [FCellAutomata.F_neg]
        have : (C.next c) 0 ∈ C.F_neg := CellAutomata.next_state_of_closed_set_state (h.2) this
        have : C.state_accepts ((C.next c) 0) = some accepts := by simp_all [FCellAutomata.F_neg]
        simp_all

      case true =>
        have : c 0 ∈ C.F_pos := by simp_all [FCellAutomata.F_pos]
        have : (C.next c) 0 ∈ C.F_pos := CellAutomata.next_state_of_closed_set_state (h.1) this
        have : C.state_accepts ((C.next c) 0) = some accepts := by simp_all [FCellAutomata.F_pos]
        simp_all



lemma accept_delta_closed { C: FCellAutomata } (h: C.accept_delta_closed) (k: ℕ):
  C.accepts w ↔ C.comp_accepts w (C.time' w + k) = some true
:= by simp [accept_delta_closed' C h, C.accepts_iff_time]
