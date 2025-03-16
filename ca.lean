import Mathlib

theorem ite_eq_of_true {α} { p: Prop } [Decidable p] (h: p) (a b: α): (if p then a else b) = a := by
  simp_all only [↓reduceIte]

noncomputable def min_nat (set: Set ℕ) :=
  let _dec := Classical.dec;
  if h: ∃ n, n ∈ set
  then some (Nat.find h)
  else none

theorem set_iff {α: Type*} (p1 p2: α → Prop): {w | p1 w} = {w | p2 w} ↔ (∀ w, p1 w ↔ p2 w) := by
  simp [Set.ext_iff]


----------------------------------------------------------------


class Alphabet where
  (α: Type 0)

def Word [Alphabet] := List Alphabet.α

structure CellularAutomata where
  Q: Type u
  δ: Q → Q → Q → Q
  [inv_decidable_q: DecidableEq Q]
  [inv_fin_q: Fintype Q]

def Config (Q: Type*) := ℤ → Q

def CellularAutomata.next (ca: CellularAutomata) (c: Config ca.Q): Config ca.Q :=
  fun i => ca.δ (c (i - 1)) (c i) (c (i + 1))

def CellularAutomata.comp (ca: CellularAutomata) (n: ℕ) (c: Config ca.Q): Config ca.Q :=
  match n with
  | 0 => c
  | n + 1 => ca.next (ca.comp n c)

variable (ca: CellularAutomata)

def CellularAutomata.passive_set (Q: Set ca.Q) := ∀ (a b c: Q), ca.δ a b c = b
def CellularAutomata.passive (q: ca.Q) := ca.passive_set { q }
def CellularAutomata.delta_closed_set (Q: Set ca.Q) := ∀ a (b: Q) c, ca.δ a b c ∈ Q
def CellularAutomata.dead (q: ca.Q) := ca.delta_closed_set {q}
def CellularAutomata.left_independent := ∀ (q1 q2 q3 q4), ca.δ q1 q2 q3 = ca.δ q4 q2 q3
def CellularAutomata.right_independent := ∀ (q1 q2 q3 q4), ca.δ q1 q2 q3 = ca.δ q1 q2 q4
def CellularAutomata.initial (q: ca.Q) := ∀ a b c, ca.δ a b c = q → b = q


variable [α: Alphabet]

structure LanguageCellularAutomata extends CellularAutomata where
  embed: α.α → Q
  border: Q

def LanguageCellularAutomata.embed_word (ca: LanguageCellularAutomata) (word: Word): Config ca.Q :=
  fun i =>
    if h: i ≥ 0 ∧ i < word.length
    then ca.embed (word.get ⟨i.toNat, by omega⟩)
    else ca.border

def LanguageCellularAutomata.comp (C: LanguageCellularAutomata) (w: Word)
| 0 => C.embed_word w
| t + 1 => C.next (C.comp w t)

def LanguageCellularAutomata.internal_state {C: LanguageCellularAutomata} (q: C.Q) := ∀ a: α.α, C.embed a ≠ q

@[simp]
theorem LanguageCellularAutomata.comp_zero {C: LanguageCellularAutomata} {w}: C.comp w 0 = C.embed_word w := by rfl


class DefinesLanguage (CA: Type u) where
  L: CA -> Language α.α

def ℒ [DefinesLanguage CA] (s: (Set CA)): Set (Language α.α) :=
  fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca


class DefinesTime (CA: Type u) where
  t: CA -> Word → Option ℕ

/-
def t_max [DefinesTime CA] (ca: CA) (n: ℕ): Option ℕ := sorry

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ := sorry
-/


structure FCellularAutomata extends LanguageCellularAutomata where
  state_accepts: Q -> Option Bool
  -- none: continue
  -- some true: accept
  -- some false: reject


noncomputable def FCellularAutomata.time (C: FCellularAutomata) (w: Word): Option ℕ :=
  min_nat { t | C.state_accepts (C.comp w t 0) ≠ none }

def FCellularAutomata.accepts (C: FCellularAutomata) (w: Word) :=
  match C.time w with
  | some t => C.state_accepts (C.comp w t 0) = some true
  | none => False

def FCellularAutomata.L (C: FCellularAutomata): Language α.α := { w: Word | C.accepts w }

def FCellularAutomatas [α: Alphabet]: Set FCellularAutomata := fun _a => true



instance : DefinesLanguage FCellularAutomata where
  L ca := ca.L

instance : Coe FCellularAutomata CellularAutomata where
  coe ca := ca.toCellularAutomata

/-
instance : DefinesTime FCellularAutomata where
  t ca := sorry
-/

structure tCellularAutomata extends LanguageCellularAutomata where
  t: ℕ → ℕ
  F_pos: Set Q

def tCellularAutomata.L (C: tCellularAutomata): Language α.α := fun w =>
  (C.comp w (C.t w.length)) 0 ∈ C.F_pos

def tCellularAutomatas [α: Alphabet]: Set tCellularAutomata := fun _a => true

instance : DefinesLanguage tCellularAutomata where
  L ca := ca.L

instance : Coe tCellularAutomata CellularAutomata where
  coe ca := ca.toCellularAutomata

/-
instance : DefinesTime tCellularAutomata where
  t ca := sorry


def OCA_L { β: Type u } [Coe β CellularAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellularAutomata.left_independent ca

def OCA_R { β: Type u } [Coe β CellularAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellularAutomata.right_independent ca

def rt { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))

syntax term "&" term : term
macro_rules | `($a & $b) => `($b $a)



def RT := tCellularAutomatas & rt { fun n => n - 1 }

theorem X: ℒ (RT) = ℒ (FCellularAutomatas & OCA_L) := sorry
-/



def CellularAutomata.pow_t (C: CellularAutomata) (q: C.Q)
| 0 => q
| n + 1 => C.δ (CellularAutomata.pow_t C q n) (CellularAutomata.pow_t C q n) (CellularAutomata.pow_t C q n)

instance state_pow_t (C: CellularAutomata): NatPow C.Q where
  pow := CellularAutomata.pow_t C

def CellularAutomata.pow_t_eq (C: CellularAutomata) (q: C.Q) (n: ℕ): q^n = CellularAutomata.pow_t C q n := by rfl

@[simp]
def CellularAutomata.pow_t_eq_0 {C: CellularAutomata} (q: C.Q): q^0 = q := by rfl

def CellularAutomata.pow_t_eq_succ {C: CellularAutomata} (q: C.Q): q^(n+1) = (q^n)^1 := by rfl



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

protected def FCellularAutomata.state_pow_accepts' { C: FCellularAutomata } (q: C.Q)
| 0 => C.state_accepts q
| n + 1 => match C.state_accepts q with
  | some v => some v
  | none => C.state_pow_accepts' (q^1) n

def FCellularAutomata.state_pow_accepts { C: FCellularAutomata } (q: C.Q): Option Bool :=
  C.state_pow_accepts' q (C.inv_fin_q.card)

def lemma_1_c (C: FCellularAutomata): FCellularAutomata :=
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
    state_accepts
      | [ s1 | _b1 ] => C.state_accepts s1
      | border => C.state_pow_accepts C.border
  }


def Word.cone (w: Word) (t: ℕ): Set ℤ := { i: ℤ | -t ≤ i ∧ i < w.length + t }

instance (w: Word) (t: ℕ) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | -t ≤ i ∧ i < w.length + t })]:
  Decidable (i ∈ (Word.cone w t)) := d

theorem Word.cone_prop {w: Word} {t: ℕ} {i: ℤ} (d: ℤ) (h: i ∉ w.cone (t + 1)) (h2: d.natAbs ≤ 1): (i + d) ∉ w.cone t := by
  simp_all [Word.cone]
  omega





theorem LanguageCellularAutomata.border_pow_t (C: LanguageCellularAutomata) {w: Word} {t: ℕ} {i: ℤ} (h: i ∉ w.cone t):
    C.comp w t i = C.border^t := by

  induction t generalizing i
  case zero =>
    simp [LanguageCellularAutomata.comp, CellularAutomata.pow_t, LanguageCellularAutomata.embed_word]
    intro c
    simp_all [Word.cone, CharP.cast_eq_zero, neg_zero, add_zero, Set.mem_setOf_eq, and_self, not_true_eq_false]
  case succ t ih =>
    have h1 := ih $ Word.cone_prop 0 h (by simp)
    have h2 := ih $ Word.cone_prop (-1) h (by simp)
    have h3 := ih $ Word.cone_prop 1 h (by simp)
    have x: (i + -1) = i - 1 := by rfl
    simp_all [LanguageCellularAutomata.comp, CellularAutomata.pow_t, LanguageCellularAutomata.embed_word, CellularAutomata.next, CellularAutomata.pow_t_eq]

theorem LanguageCellularAutomata.initial_internal_of_cone (C: LanguageCellularAutomata) { q: C.Q } {w: Word} {t: ℕ} {i: ℤ} (h1: i ∈ w.cone 0) (h2: C.initial q) (h3: C.internal_state q):
    C.comp w t i ≠ q := by
  sorry


theorem next_initial { C: LanguageCellularAutomata } { q: C.Q } { w: Word } { t: ℕ } (h1: C.initial q) (h2: C.next (C.comp w t) i = q): C.comp w t i = q :=
  by
  subst h2
  apply h1
  · rfl

def FCellularAutomata.state_accept_seq { C: FCellularAutomata } (i: ℤ) (w: Word) (t: ℕ) :=
  C.state_accepts (C.comp w t i)

-- How to get rid of this?
theorem eq_of_app { α β: Type* } { f g: α → β } (h: f = g) (a: α): f a = g a := by
  rw [h]

theorem eq_time { C1 C2: FCellularAutomata }
  (h: C1.state_accept_seq 0 w = C2.state_accept_seq 0 w):
    C1.time w = C2.time w := by
    unfold FCellularAutomata.time
    unfold FCellularAutomata.state_accept_seq at h
    conv =>
      pattern C1.state_accepts _
      rw [eq_of_app h t]

theorem eq_L { C1 C2: FCellularAutomata } (h: C1.state_accept_seq 0 w = C2.state_accept_seq 0 w): w ∈ C1.L ↔ w ∈ C2.L := by
    unfold FCellularAutomata.L

    suffices : C1.accepts w ↔ C2.accepts w
    exact this

    unfold FCellularAutomata.accepts
    unfold FCellularAutomata.state_accept_seq at h
    conv =>
      pattern C1.state_accepts _
      rw [eq_of_app h t]
    simp [eq_time h]

theorem lemma_2_4_1_passive_initial_border (C: FCellularAutomata.{u}):
  ∃ C': FCellularAutomata.{u},
    C'.L = C.L
  ∧ C'.passive C'.border
  ∧ C'.initial C'.border
  -- ∧ DefinesTime.t C' = DefinesTime.t C
  --∧ (C.left_independent ↔ C'.left_independent)
  --∧ (C.right_independent ↔ C'.right_independent)
  := by
  let C' := lemma_1_c C
  use C'

  have c1: C'.passive C'.border := by
    simp [CellularAutomata.passive, CellularAutomata.passive_set, C', lemma_1_c]

  have c2: C'.initial C'.border := by
    unfold CellularAutomata.initial C' lemma_1_c
    intro a b c a_1
    simp_all only [C']
    split at a_1
    next x x_1 x_2 st br => simp_all only [reduceCtorEq, C']
    next x x_1 x_2 st br x_3 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 st br x_3 x_4 => simp_all only [imp_false, reduceCtorEq, C']
    next x x_1 x_2 => simp_all only [C']

  have c3: C'.internal_state C'.border := by
    unfold LanguageCellularAutomata.internal_state C' lemma_1_c
    intro a
    simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, C']

  have b_eq_b_pow {w: Word} {t} {i} {b _s: C.Q} (h: (C'.comp w t i) = state _s b): b = (C.border^t) := by
    induction t generalizing i b _s with
    | zero =>
      simp_all [C', LanguageCellularAutomata.comp, lemma_1_c, LanguageCellularAutomata.embed_word]
      split at h
      simp_all only [state.injEq, C']
      simp_all only [not_and, not_lt, reduceCtorEq, C']
    | succ t ih =>

      simp [LanguageCellularAutomata.comp, CellularAutomata.next] at h
      set ci := C'.comp w t
      simp [C', lemma_1_c] at h
      split at h
      case h_1 _a _b _c st br p | h_2 _a _b _c st br p alt | h_3 _a _b _c st br p alt1 alt2 =>
        simp at h
        let x := ih p
        rw [CellularAutomata.pow_t_eq_succ]
        simp_all only [C', ci, x]
      case h_4 =>
        simp_all only [reduceCtorEq, C', ci]


  have h (w: Word) t i: (C'.comp w t i).unwrap (C.border ^ t) = C.comp w t i := by
    induction t using LanguageCellularAutomata.comp.induct generalizing i with
    | case1 =>
      simp [LanguageCellularAutomata.embed_word, C', lemma_1_c]
      rw [apply_dite unwrap]
      rw [dite_apply]
      simp [unwrap]

    | case2 t ih =>
      unfold LanguageCellularAutomata.comp
      rw [CellularAutomata.pow_t_eq_succ]
      set bt := C.border^t

      rw [CellularAutomata.next]
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
        simp [CellularAutomata.next]

      case h_4 c1 c2 c3 =>
        simp [unwrap, CellularAutomata.next]
        rw [←ih i]
        rw [←ih (i-1)]
        rw [←ih (i+1)]
        rw [c1, c2, c3]
        simp [unwrap]
        rfl

  have h w: w ∈ C'.L ↔ w ∈ C.L := by
    cases wlen: w.length

    case zero =>
      unfold FCellularAutomata.L
      suffices : C'.accepts w ↔ C.accepts w
      exact this
      rw [List.length_eq_zero_iff] at wlen

      unfold FCellularAutomata.accepts

      have : C'.time w = some 0 := by
        unfold FCellularAutomata.time

        have : C'.state_accepts (C'.comp w 0 0) = C.state_pow_accepts C.border := by
          simp [C', lemma_1_c]
          sorry



        sorry

      sorry

    sorry

  sorry





/-

inductive LemmaCases where
  | computing
  | accept
  | reject
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

def lemma_C' (C: FCellularAutomata): FCellularAutomata :=
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

theorem lemma_2_3_1_F_delta_closed (C: FCellularAutomata):
  ∃ C': FCellularAutomata,
    C'.L = C.L
  ∧ DefinesTime.t C' = DefinesTime.t C
  ∧ ∀ f: C'.F_pos, C'.dead f
  ∧ ∀ f: C'.F_neg, C'.dead f
:= by

  let C': FCellularAutomata := lemma_C' C


  have h (w: Word) n i: C.comp w n i = (C'.comp w n i).fst  := by
    induction n using LanguageCellularAutomata.comp.induct generalizing i with
    | case1 =>
      simp [LanguageCellularAutomata.embed_word, LanguageCellularAutomata.comp, C', lemma_C']
      split
      next h_1 => simp_all only [C']
      next h_1 => simp_all only [C']

    | case2 k ih =>
      unfold LanguageCellularAutomata.comp CellularAutomata.next
      rw [ih]
      rw [ih]
      rw [ih]
      simp_all only [ne_eq, ite_not, C']
      rfl


  sorry
-/
