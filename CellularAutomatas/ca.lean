import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some

theorem min_nat_eq {f: ℕ -> Option Bool}: min_nat { i | f i ≠ none } = find_some_idx f := by
  unfold min_nat find_some_idx
  cases c: find_some_idxd f
  case none =>
    rw [find_some_idxd_eq_none_iff] at c
    simp [c]
  case some val =>
    rw [find_some_idxd_eq_some_iff] at c
    have : ∃ n, ¬f n = none := by
      use val.idx
      simp [c]
    simp_all [Nat.find_eq_iff]

theorem δδt_succ {C: CellAutomata} {q: C.Q} {t: ℕ} : δδt q (t + 1) = δδ (δδt q t) := by
  simp [δδt, apply_iterated_succ_apply']

@[simp]
theorem δδt_zero {C: CellAutomata} {q: C.Q} : δδt q 0 = q := by
  simp [δδt]

variable [Alphabet]

@[simp]
theorem LCellAutomata.comp_zero {C: LCellAutomata} {w}: C.comp w 0 = C.embed_word w := by rfl


def FCellAutomata.comp_accepts {C: FCellAutomata} (w) := C.config_accepts ∘ C.comp w


theorem FCellAutomata.time_eq {C: FCellAutomata} {w}: C.time w = find_some_idx (C.comp_accepts w) := by
  simp [←min_nat_eq, FCellAutomata.time, comp_accepts, FCellAutomata.config_accepts]

theorem FCellAutomata.comp_accepts_eq_config_accepts_comp {C: FCellAutomata} {w} {t}: C.comp_accepts w t = C.config_accepts (C.comp w t) := by
  simp [comp_accepts]

theorem FCellAutomata.accepts_iff {C: FCellAutomata} {w}: C.accepts w ↔ find_some (C.comp_accepts w) = some true := by
  simp only [FCellAutomata.accepts, FCellAutomata.time_eq, find_some_idx, ←comp_accepts_eq_config_accepts_comp, find_some]
  cases c: find_some_idxd (comp_accepts w)
  case none =>
    simp_all
  case some val =>
    rw [find_some_idxd_eq_some_iff] at c
    simp only [Option.map_some', find_some, c]


def uniform_config {C: CellAutomata} (q: C.Q): Config C.Q := fun _ => q

@[simp]
theorem empty_word_range: Word.range [] = {} := by
  unfold Word.range
  ext x
  simp_all

theorem FCellAutomata.empty_word_config_eq_uniform_border {C: FCellAutomata}: C.embed_word [] = uniform_config C.border := by
  funext i
  simp [LCellAutomata.embed_word, uniform_config, uniform_config]



theorem FCellAutomata.uniform_state_eq {C: FCellAutomata} {q: C.Q}: C.nextt (uniform_config q) = uniform_config ∘ (δδt q) := by
  funext t i
  simp only [CellAutomata.nextt, δδt, Function.comp_apply, uniform_config]

  induction t generalizing i
  case h.h.zero =>
    simp [uniform_config, apply_iterated_zero]
  case h.h.succ n ih =>
    simp [apply_iterated_succ_apply', ih, δδ, CellAutomata.next, uniform_config]

theorem FCellAutomata_comp_empty_eq_uniform {C: FCellAutomata}: C.comp [] = uniform_config ∘ (δδt C.border) := by
  simp [LCellAutomata.comp, FCellAutomata.empty_word_config_eq_uniform_border, FCellAutomata.uniform_state_eq]


def Word.cone (w: Word) (t: ℕ): Set ℤ := { i: ℤ | -t ≤ i ∧ i < w.length + t }

instance (w: Word) (t: ℕ) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | -t ≤ i ∧ i < w.length + t })]:
  Decidable (i ∈ (Word.cone w t)) := d

theorem Word.cone_prop {w: Word} {t: ℕ} {i: ℤ} (d: ℤ) (h: i ∉ w.cone (t + 1)) (h2: d.natAbs ≤ 1): (i + d) ∉ w.cone t := by
  simp_all [Word.cone]
  omega

theorem Word.cone_prop' {w: Word} {t: ℕ} {i: ℤ} { d: ℤ } (h: (i + d) ∈ w.cone t) (h2: d.natAbs ≤ 1): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega

theorem Word.cone_prop'' {w: Word} {t: ℕ} {i: ℤ} (h: i ∈ w.cone t): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega


theorem Word.cone_succ {w: Word} {t: ℕ} {i: ℤ} (h1: i - 1 ∈ w.cone t) (h2: i + 1 ∈ w.cone t): i ∈ w.cone (t + 1) := by
  simp_all [Word.cone]
  omega

theorem Word.cone_succ_not {w: Word} {t: ℕ} {i: ℤ} (wlen: w.length > 0) (h1: i - 1 ∉ w.cone t) (h2: i ∉ w.cone t) (h3: i + 1 ∉ w.cone t): i ∉ w.cone (t + 1) := by
  simp_all [cone]
  omega

@[simp]
theorem Word.cone_zero_eq_range {w: Word}: w.cone 0 = w.range := by simp [Word.cone, Word.range]

def Word.get_cone_0 {w: Word} {i} (h: i ∈ w.cone 0) := w.get' i (Word.cone_zero_eq_range ▸ h)

theorem embed_word_eq_embed {C: LCellAutomata} {w: Word} {i} (h: i ∈ w.cone 0): C.embed_word w i = C.embed (w.get_cone_0 h) := by
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


theorem FCellAutomata.accepts_empty_iff_comp_state_accepts_border {C: FCellAutomata}: C.accepts [] ↔ C.comp_state_accepts C.border = true := by
  simp only [accepts_iff, comp_accepts, FCellAutomata_comp_empty_eq_uniform, comp_state_accepts, beq_iff_eq]
  simp only [←Function.comp_assoc, FCellAutomata.uniform_config_accepts_eq]
  rw [←find_some_bounded_eq_find_some_of_repeating_function (state_accepts_repeatingFunction C)]
  simp [state_accepts_repeatingFunction, RepeatingFunction, repeating_function_of_composition, repeating_function_of_iterate_fin_type ]



instance h {C: FCellAutomata}: Nonempty C.Q := ⟨ C.border ⟩

@[simp]
theorem CellAutomata.Q_card_gt_zero {C: FCellAutomata}: C.inv_fin_q.card > 0 := by
  have x := C.inv_fin_q.card_ne_zero
  omega

theorem FCellAutomata.δδ_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδ q = q := by
  simp_all [h, δδ, CellAutomata.passive, CellAutomata.passive_set]

@[simp]
theorem FCellAutomata.δδn_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδt q t = q := by
  simp_all [δδt, δδ, apply_iterated_fixed (FCellAutomata.δδ_of_passive h)]

theorem FCellAutomata.state_pow_accepts_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): C.comp_state_accepts q = (C.state_accepts q = some true) := by
  simp [FCellAutomata.comp_state_accepts, find_some_bounded_eq_some_iff, FCellAutomata.δδn_of_passive h]
  intro h2
  use 0
  simp

theorem FCellAutomata.accepts_empty_passive {C: FCellAutomata} (h: C.passive C.border):
    C.accepts [] ↔ C.state_accepts C.border = some true := by
  rw [FCellAutomata.accepts_empty_iff_comp_state_accepts_border]
  rw [FCellAutomata.state_pow_accepts_of_passive h]




theorem CellAutomata.nextt_succ_eq (C: LCellAutomata) (c: Config C.Q): C.nextt c (t + 1) = C.next (C.nextt c t) := by
  simp [CellAutomata.nextt, apply_iterated_succ_apply']


theorem CellAutomata.comp_succ_eq (C: LCellAutomata): C.comp w (t + 1) = C.next (C.comp w t) := by
  funext i
  simp [LCellAutomata.comp, CellAutomata.nextt_succ_eq]


theorem LCellAutomata.comp_outside_word_cone_eq_border_pow_t (C: LCellAutomata) {w: Word} {t: ℕ} {i: ℤ} (h: i ∉ w.cone t):
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


theorem neq_of_internal_state {C: LCellAutomata} (q: C.Q) {w i} (h1: i ∈ w.cone 0) (h3: C.internal_state q): C.embed_word w i ≠ q := by
  rw [embed_word_eq_embed h1]
  aesop

theorem next_eq_of_initial {C: LCellAutomata} { q: C.Q } {c: Config C.Q} {i: ℤ} (h1: C.initial q) (h2: C.next c i = q): c i = q := by
  subst h2
  apply h1
  · rfl

theorem comp_eq_of_initial {C: LCellAutomata} { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: C.initial q) (h2: C.comp w (t+1) i = q):
    C.comp w t i = q := by
  simp [CellAutomata.comp_succ_eq] at h2
  exact next_eq_of_initial h1 h2

theorem LCellAutomata.initial_internal_of_cone (C: LCellAutomata) { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: i ∈ w.cone 0) (h2: C.initial q) (h3: C.internal_state q):
    C.comp w t i ≠ q := by

  induction t
  case zero =>
    simp [h3, neq_of_internal_state q h1]
  case succ t ih =>
    by_contra eq
    simp_all only [ne_eq, not_true_eq_false, comp_eq_of_initial h2 eq]


theorem next_initial { C: LCellAutomata } { q: C.Q } { w: Word } { t: ℕ } (h1: C.initial q) (h2: C.next (C.comp w t) i = q): C.comp w t i = q :=
  by
  subst h2
  apply h1
  · rfl

lemma L_eq_iff (C C': FCellAutomata): C'.L = C.L ↔ (∀ w, C'.accepts w ↔ C.accepts w) := by
  unfold FCellAutomata.L
  rw [Set.ext_iff]
  rfl


inductive lemma_1_Q (Q: Type u) where
  | border
  | state (s border: Q)
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

syntax "[" term "|" term "]" : term
macro_rules | `([$a | $b]) => `(lemma_1_Q.state $a $b)

def lemma_1_Q.unwrap (q: lemma_1_Q Q) (b: Q) :=
  match q with
  | border => b
  | state s _b => s

open lemma_1_Q
infix:50 " ?? " => unwrap

def lemma_1_state_accepts (C: FCellAutomata)
| [ s1 | _b1 ] => C.state_accepts s1
| border => C.comp_state_accepts C.border

def lemma_1_c (C: FCellAutomata): FCellAutomata :=
  let _inv_fin_q := C.inv_fin_q;
  let _inv_decidable_q := C.inv_decidable_q;

  {
    Q := lemma_1_Q C.Q,
    δ
      | a@([_ | br]), b,            c
      | a,            b@([_ | br]), c
      | a,            b,            c@([_ | br])  => [ C.δ (a ?? br) (b ?? br) (c ?? br) | δδ br ]
      | border,       border,     border          => border
    embed a := state (C.embed a) C.border,
    border := border,
    state_accepts := lemma_1_state_accepts C
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
  let C' := lemma_1_c C
  use C'

  have a1: C'.passive C'.border := by
    simp [CellAutomata.passive, CellAutomata.passive_set, C', lemma_1_c]

  have a2: C'.initial C'.border := by
    unfold CellAutomata.initial C' lemma_1_c
    intro a b c a_1
    simp_all only [C']
    split at a_1
    next x x_1 x_2 st br => simp_all only [reduceCtorEq, C']
    next x x_1 x_2 st br x_3 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 st br x_3 x_4 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 => simp_all only [C']

  have a3: C'.internal_state C'.border := by
    unfold LCellAutomata.internal_state C' lemma_1_c
    intro a
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, C']


  have C'_comp (w: Word) (wlen: w.length > 0) t i: (C'.comp w t i) = if i ∈ w.cone t then state (C.comp w t i) (δδt C.border t) else border := by
    induction t generalizing i
    case zero =>
      simp only [LCellAutomata.comp_zero, Word.cone_zero_eq_range, δδt_zero, C']
      unfold LCellAutomata.embed_word
      split
      case isTrue h => simp [lemma_1_c]
      case isFalse h => simp [lemma_1_c]

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
      unfold C' lemma_1_c
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
      simp [C', lemma_1_c, lemma_1_state_accepts, Word.zero_mem_cone c]
      exact c -- Remove exact, why ???

    case neg =>
      simp at c
      simp [c]
      rw [FCellAutomata.accepts_empty_passive a1]
      simp [C', lemma_1_c, lemma_1_state_accepts, FCellAutomata.accepts_empty_iff_comp_state_accepts_border]

  simp [a1, a2, a3, a4]



  /-
  have h' { w } (wlen: w.length ≠ 0): C.state_accept_seq 0 w = C'.state_accept_seq 0 w := by
    unfold FCellAutomata.state_accept_seq
    funext t

    have h'': C'.comp w t 0 ≠ border := by
      apply LCellAutomata.initial_internal_of_cone
      simp [Word.cone]
      omega
      simp_all only [a2, C', ne_eq, List.length_eq_zero_iff, C']
      exact a2
      simp_all only [ne_eq, List.length_eq_zero_iff, C']
      exact a3

    rw [←h]
    conv =>
      pattern C'.state_accepts
      unfold C'
      unfold lemma_1_c
      simp

    unfold state_accepts
    cases c: C'.comp w t 0
    case h.border => simp_all [C']
    case h.state s sb =>  simp [C', lemma_1_c, unwrap]


  have hh: ∀ w, (w ∈ C'.L ↔ w ∈ C.L) ↔ (C'.accepts w ↔ C.accepts w) := by
    intro w
    simp_all only [C', FCellAutomata.L]
    rfl

  have h: C'.L = C.L := by
    ext w
    cases wlen: w.length

    case zero =>
      rw [hh]
      rw [List.length_eq_zero_iff] at wlen
      rw [wlen]
      rw [FCellAutomata.accepts_empty_passive a1]
      rw [FCellAutomata.accepts_empty_iff_comp_state_accepts_border]
      simp [C', lemma_1_c, state_accepts]

    case succ =>
      have wlen: w.length ≠ 0 := by simp_all [C']
      rw [eq_L]
      simp [h' wlen]

  simp [a1, a2, h]
-/



/-

inductive LemmaCases where
  | computing
  | accept
  | reject
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

def lemma_C' (C: FCellAutomata): FCellAutomata :=
  let _h := C.inv_fin;
  let _x := C.inv_decidable;
  {
    Q := C.Q × LemmaCases,
    δ := fun (a, fa) (b, fb) (c, fc) =>
      let r := C.δ a b c; (
        r,
        if fb ≠ LemmaCases.computing then fb else
        if r ∈ C.F_pos then LemmaCases.accept else
        if r ∈ C.F_neg then LemmaCases.reject else
        LemmaCases.computing
      ),
    inv_fin := instFintypeProd C.Q LemmaCases,
    embed := fun a => (C.embed a, LemmaCases.computing),
    border := (C.border, LemmaCases.computing),
    F_pos := { x: C.Q × LemmaCases | x.snd = LemmaCases.accept },
    F_neg := { x: C.Q × LemmaCases | x.snd = LemmaCases.reject },
  }

theorem lemma_2_3_1_F_delta_closed (C: FCellAutomata):
  ∃ C': FCellAutomata,
    C'.L = C.L
  ∧ DefinesTime.t C' = DefinesTime.t C
  ∧ ∀ f: C'.F_pos, C'.dead f
  ∧ ∀ f: C'.F_neg, C'.dead f
:= by

  let C': FCellAutomata := lemma_C' C


  have h (w: Word) n i: C.comp w n i = (C'.comp w n i).fst  := by
    induction n using LCellAutomata.comp.induct generalizing i with
    | case1 =>
      simp [LCellAutomata.embed_word, LCellAutomata.comp, C', lemma_C']
      split
      next h_1 => simp_all only [C']
      next h_1 => simp_all only [C']

    | case2 k ih =>
      unfold LCellAutomata.comp CellAutomata.next
      rw [ih]
      rw [ih]
      rw [ih]
      simp_all only [ne_eq, ite_not, C']
      rfl


  sorry
-/





theorem const_speed_up1: ℒ (tCellAutomatas |> t⦃ n - 1 + k + 1 ⦄) = ℒ (tCellAutomatas |> t⦃ n - 1 + k ⦄) := sorry


-- Q -> fun Q -> Q
def φ {C: tCellAutomata} (c: C.Q) (b: C.Q) := (b, fun a => δ a b c)

def Sp {C: tCellAutomata} := {
  Q := C.Q × Option (C.Q → C.Q)
  δ
  | (aq, af) (bq, bf) (cq, none) := (δ aq bq cq, none)
  | (aq, af) (bq, bf) (cq, some cf) := φ (cf bq) (δ aq bq cq)
}
