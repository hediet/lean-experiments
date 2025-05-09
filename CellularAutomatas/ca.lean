import Mathlib
import CellularAutomatas.defs
import CellularAutomatas.common
import CellularAutomatas.find_some

variable [Alphabet]

@[simp]
theorem LCellAutomata.comp_zero {C: LCellAutomata} {w}: C.comp w 0 = C.embed_word w := by rfl





def Word.cone (w: Word) (t: ℕ): Set ℤ := { i: ℤ | -t ≤ i ∧ i < w.length + t }

instance (w: Word) (t: ℕ) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | -t ≤ i ∧ i < w.length + t })]:
  Decidable (i ∈ (Word.cone w t)) := d

theorem Word.cone_prop {w: Word} {t: ℕ} {i: ℤ} (d: ℤ) (h: i ∉ w.cone (t + 1)) (h2: d.natAbs ≤ 1): (i + d) ∉ w.cone t := by
  simp_all [Word.cone]
  omega

def Word.get_cone_0 {w: Word} {i} (h: i ∈ w.cone 0) := w.get ⟨i.toNat, by simp_all [h, Word.cone]⟩

theorem embed_word_eq_embed {C: LCellAutomata} {w: Word} {i} (h: i ∈ w.cone 0): C.embed_word w i = C.embed (w.get_cone_0 h) := by
  simp [Word.cone] at h
  simp [Word.get_cone_0, LCellAutomata.embed_word, Word.cone, h]




def FCellAutomata.comp_state_accepts { C: FCellAutomata } (q: C.Q) :=
  find_some_bounded (C.state_accepts ∘ δδn q) C.inv_fin_q.card == some true


theorem FCellAutomata.accepts_empty_iff_comp_state_accepts_border {C: FCellAutomata}: C.accepts [] ↔ C.comp_state_accepts C.border = true := by
  unfold FCellAutomata.accepts
  sorry


/-
def CellAutomata.pow_t (C: CellAutomata) (q: C.Q)
| 0 => q
| n + 1 => C.δ (CellAutomata.pow_t C q n) (CellAutomata.pow_t C q n) (CellAutomata.pow_t C q n)

instance state_pow_t (C: CellAutomata): NatPow C.Q where
  pow := CellAutomata.pow_t C

def CellAutomata.pow_t_eq (C: CellAutomata) (q: C.Q) (n: ℕ): q^n = CellAutomata.pow_t C q n := by rfl

@[simp]
def CellAutomata.pow_t_eq_0 {C: CellAutomata} (q: C.Q): q^0 = q := by rfl

def CellAutomata.pow_t_eq_1 (C: CellAutomata) (q: C.Q): q^1 = C.δ q q q := by rfl

def CellAutomata.pow_t_eq_succ {C: CellAutomata} (q: C.Q): q^(n+1) = (q^n)^1 := by rfl



protected def FCellAutomata.state_pow_accepts' { C: FCellAutomata } (q: C.Q) (n: ℕ) :=
  match C.state_accepts q with
    | some v => v
    | none => match n with
      | 0 => false
      | k + 1 => C.state_pow_accepts' (q^1) k


@[simp]
theorem FCellAutomata.passive_q_pow_eq_q {C: FCellAutomata} {q: C.Q} (h: C.passive q): q^1 = q := by
  simp_all [h, CellAutomata.passive_set, CellAutomata.passive, CellAutomata.pow_t_eq_1]


lemma FCellAutomata.state_pow_accepts'_of_passive {C: FCellAutomata} {q: C.Q} (h1: C.passive q) n:
  C.state_pow_accepts' q n = (C.state_accepts q = some true) := by
  induction n
  case zero =>
    simp_all [FCellAutomata.state_pow_accepts']
    aesop
  case succ n h =>
    simp [FCellAutomata.state_pow_accepts', FCellAutomata.passive_q_pow_eq_q h1]
    simp_all only [eq_iff_iff]
    apply Iff.intro
    · intro a
      split at a
      next x v heq =>
        subst a
        simp_all only [iff_true]
      next x heq => simp_all only [reduceCtorEq, iff_false, not_true_eq_false]
    · intro a
      simp_all only [iff_true]
-/


instance h {C: FCellAutomata}: Nonempty C.Q := ⟨ C.border ⟩

@[simp]
theorem CellAutomata.Q_card_gt_zero {C: FCellAutomata}: C.inv_fin_q.card > 0 := by
  have x := C.inv_fin_q.card_ne_zero
  omega

@[simp]
theorem FCellAutomata.δδ_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδ q = q := by
  simp_all [h, δδ, CellAutomata.passive, CellAutomata.passive_set]

@[simp]
theorem FCellAutomata.δδn_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q): δδn q t = q := by
  simp_all [δδn, δδ, apply_iterated, apply_iterated_fixed]
  sorry

@[simp]
theorem FCellAutomata.state_pow_accepts_of_passive {C: FCellAutomata} {q: C.Q} (h: C.passive q):
    C.FCellAutomata.comp_state_accepts q = (C.state_accepts q = some true) := by
  simp [FCellAutomata.comp_state_accepts, find_some_bounded_eq_some_iff, FCellAutomata.δδn_of_passive h]
  intro h2
  use 0
  simp

theorem FCellAutomata.accepts_empty_passive {C: FCellAutomata} (h: C.passive C.border):
    C.accepts [] ↔ C.state_accepts C.border = some true := by
  rw [FCellAutomata.accepts_empty_iff_comp_state_accepts_border]
  rw [FCellAutomata.state_pow_accepts_of_passive h]







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

def state_accepts (C: FCellAutomata)
| [ s1 | _b1 ] => C.state_accepts s1
| border => C.FCellAutomata.comp_state_accepts C.border

def lemma_1_c (C: FCellAutomata): FCellAutomata :=
  let _inv_fin_q := C.inv_fin_q;
  let _inv_decidable_q := C.inv_decidable_q;

  {
    Q := lemma_1_Q C.Q,
    δ
      | a@([_ | br]), b,            c
      | a,            b@([_ | br]), c
      | a,            b,            c@([_ | br])  => [ C.δ (a ?? br) (b ?? br) (c ?? br) | br^1 ]
      | border,       border,     border          => border
    embed a := state (C.embed a) C.border,
    border := border,
    state_accepts := state_accepts C
  }





theorem LCellAutomata.border_pow_t (C: LCellAutomata) {w: Word} {t: ℕ} {i: ℤ} (h: i ∉ w.cone t):
    C.comp w t i = C.border^t := by

  induction t generalizing i
  case zero =>
    simp [LCellAutomata.comp, CellAutomata.pow_t, LCellAutomata.embed_word]
    intro c
    simp_all [Word.cone, CharP.cast_eq_zero, neg_zero, add_zero, Set.mem_setOf_eq, and_self, not_true_eq_false]
  case succ t ih =>
    have h1 := ih $ Word.cone_prop 0 h (by simp)
    have h2 := ih $ Word.cone_prop (-1) h (by simp)
    have h3 := ih $ Word.cone_prop 1 h (by simp)
    have x: (i + -1) = i - 1 := by rfl
    simp_all [LCellAutomata.comp, CellAutomata.pow_t, LCellAutomata.embed_word, CellAutomata.next, CellAutomata.pow_t_eq]



theorem neq_of_internal_state {C: LCellAutomata} (q: C.Q) {w i} (h1: i ∈ w.cone 0) (h3: C.internal_state q): C.embed_word w i ≠ q := by
  rw [embed_word_eq_embed h1]
  aesop

theorem next_eq_of_initial {C: LCellAutomata} { q: C.Q } {c: Config C.Q} {i: ℤ} (h1: C.initial q) (h2: C.next c i = q): c i = q := by
  subst h2
  apply h1
  · rfl

theorem comp_eq_of_initial {C: LCellAutomata} { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: C.initial q) (h2: C.comp w (t+1) i = q): C.comp w t i = q := by
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

def FCellAutomata.state_accept_seq { C: FCellAutomata } (i: ℤ) (w: Word) (t: ℕ) :=
  C.state_accepts (C.comp w t i)

theorem eq_time { C1 C2: FCellAutomata }
  (h: C1.state_accept_seq 0 w = C2.state_accept_seq 0 w):
    C1.time w = C2.time w := by
    unfold FCellAutomata.time
    unfold FCellAutomata.state_accept_seq at h
    conv =>
      pattern C1.state_accepts _
      rw [eq_of_app h t]

theorem eq_L { C1 C2: FCellAutomata } (h: C1.state_accept_seq 0 w = C2.state_accept_seq 0 w): w ∈ C1.L ↔ w ∈ C2.L := by
    unfold FCellAutomata.L

    suffices : C1.accepts w ↔ C2.accepts w
    exact this

    unfold FCellAutomata.accepts
    unfold FCellAutomata.state_accept_seq at h
    conv =>
      pattern C1.state_accepts _
      rw [eq_of_app h t]
    simp [eq_time h]

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

  have b_eq_b_pow {w: Word} {t} {i} {b _s: C.Q} (h: (C'.comp w t i) = state _s b): b = (C.border^t) := by
    induction t generalizing i b _s with
    | zero =>
      simp_all [C', LCellAutomata.comp, lemma_1_c, LCellAutomata.embed_word]
      split at h
      simp_all only [state.injEq, C']
      simp_all only [not_and, not_lt, reduceCtorEq, C']
    | succ t ih =>

      simp [LCellAutomata.comp, CellAutomata.next] at h
      set ci := C'.comp w t
      simp [C', lemma_1_c] at h
      split at h
      case h_1 _a _b _c st br p | h_2 _a _b _c st br p alt | h_3 _a _b _c st br p alt1 alt2 =>
        simp at h
        let x := ih p
        rw [CellAutomata.pow_t_eq_succ]
        simp_all only [C', ci, x]
      case h_4 =>
        simp_all only [reduceCtorEq, C', ci]

  have h (w: Word) t i: (C'.comp w t i).unwrap (C.border ^ t) = C.comp w t i := by
    induction t using LCellAutomata.comp.induct generalizing i with
    | case1 =>
      simp [LCellAutomata.embed_word, C', lemma_1_c]
      rw [apply_dite unwrap]
      rw [dite_apply]
      simp [unwrap]

    | case2 t ih =>
      unfold LCellAutomata.comp
      rw [CellAutomata.pow_t_eq_succ]
      set bt := C.border^t

      rw [CellAutomata.next]
      set cn := C'.comp w t

      unfold C' lemma_1_c
      simp
      split

      case h_1 _a _b _c st br p | h_2 _a _b _c st br p alt | h_3 _a _b _c st br p alt1 alt2 =>
        have x: bt = br := by
          unfold bt
          have t := b_eq_b_pow p
          simp_all [t]

        rw [unwrap]
        rw [←p]
        rw [←x]
        rw [ih (i-1)]
        rw [ih i]
        rw [ih (i+1)]
        simp [CellAutomata.next]

      case h_4 c1 c2 c3 =>
        simp [unwrap, CellAutomata.next]
        rw [←ih i]
        rw [←ih (i-1)]
        rw [←ih (i+1)]
        rw [c1, c2, c3]
        simp [unwrap]
        rfl

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
