import Mathlib

class Alphabet where
  (α: Type 0)


def Word [Alphabet] := List Alphabet.α
def Config (Q: Type*) := ℤ → Q


structure CellularAutomata where
  Q: Type u
  δ: Q → Q → Q → Q
  [d: DecidableEq Q]
  [inv_fin: Fintype Q]

def CellularAutomata.next (ca: CellularAutomata) (c: Config ca.Q): Config ca.Q :=
  fun i => ca.δ (c (i - 1)) (c i) (c (i + 1))

def CellularAutomata.next_n (ca: CellularAutomata) (n: ℕ) (c: Config ca.Q): Config ca.Q :=
  match n with
  | 0 => c
  | n + 1 => ca.next (ca.next_n n c)

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

def LanguageCellularAutomata.step_n (ca: LanguageCellularAutomata) (word: Word)
| 0 => ca.embed_word word
| k + 1 => ca.next (ca.step_n word k)

def LanguageCellularAutomata.step_n' (ca: LanguageCellularAutomata) (n: ℕ) (word: Word): Config ca.Q :=
  ca.next_n n (ca.embed_word word)


class DefinesLanguage (CA: Type u) where
  L: CA -> Language α.α

def ℒ [DefinesLanguage CA] (s: (Set CA)): Set (Language α.α) :=
  fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca


class DefinesTime (CA: Type u) where
  t: CA -> Word → Option ℕ

def t_max [DefinesTime CA] (ca: CA) (n: ℕ): Option ℕ := sorry

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ := sorry

structure FCellularAutomata extends LanguageCellularAutomata where
  F_pos: Finset Q
  F_neg: Finset Q

def FCellularAutomata.L (ca: FCellularAutomata): Language α.α := fun w =>
  ∃ n: ℕ, (ca.next_n n (ca.embed_word w)) 0 ∈ ca.F_pos

def FCellularAutomatas [α: Alphabet]: Set FCellularAutomata := fun _a => true

instance : DefinesLanguage FCellularAutomata where
  L ca := ca.L

instance : Coe FCellularAutomata CellularAutomata where
  coe ca := ca.toCellularAutomata

instance : DefinesTime FCellularAutomata where
  t ca := sorry


structure tCellularAutomata extends LanguageCellularAutomata where
  t: ℕ → ℕ
  F_pos: Set Q

def tCellularAutomata.L (ca: tCellularAutomata): Language α.α := fun w =>
  (ca.next_n (ca.t w.length) (ca.embed_word w)) 0 ∈ ca.F_pos

def tCellularAutomatas [α: Alphabet]: Set tCellularAutomata := fun _a => true

instance : DefinesLanguage tCellularAutomata where
  L ca := ca.L

instance : Coe tCellularAutomata CellularAutomata where
  coe ca := ca.toCellularAutomata

instance : DefinesTime tCellularAutomata where
  t ca := sorry


def OCA_L { β: Type u } [Coe β CellularAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellularAutomata.left_independent ca

def OCA_R { β: Type u } [Coe β CellularAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellularAutomata.right_independent ca

def t { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))

syntax term "&" term : term
macro_rules | `($a & $b) => `($b $a)



def RT := tCellularAutomatas & t { fun n => n - 1 }

theorem X: ℒ (RT) = ℒ (FCellularAutomatas & OCA_L) := sorry

--def finset_set_fintype { α } [h: Fintype α] (s: Set α): Finset α



inductive lemma_1_Q (Q: Type u) where
  | border
  | state (s border: Q)
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

def lemma_1_Q.unwrap (b: Q)
| border => b
| state s _b => s

def lemma_1_Q.unwrap2 (b: Q)
| border => b
| state _s b => b

open lemma_1_Q

def lemma_1_c (C: FCellularAutomata): FCellularAutomata := 
  let _inv_fin := C.inv_fin;
  let _d := C.d;

  {
    Q := lemma_1_Q C.Q,
    δ := fun
        | state st br,  b,            c            => state (C.δ st             (b.unwrap br)   (c.unwrap br)) (C.δ br br br)
        | a,            state st br,  c            => state (C.δ (a.unwrap br)  st              (c.unwrap br)) (C.δ br br br)
        | a,            b,            state st br  => state (C.δ (a.unwrap br)  (b.unwrap br)   st           ) (C.δ br br br)
        | border,       border,       border       => border

    embed := fun a => state (C.embed a) C.border,
    border := border,
    F_pos := { x | true = match x with
      | state s1 _b1 => s1 ∈ C.F_pos
      | _ => C.border ∈ C.F_pos
    },
    F_neg := { x | true = match x with
      | state s1 _b1 => s1 ∈ C.F_neg
      | _ => C.border ∈ C.F_neg
    },
  }

def CellularAutomata.pow_t (C: CellularAutomata) (q: C.Q)
| 0 => q
| n + 1 => let x := CellularAutomata.pow_t C q n; C.δ x x x


theorem next_initial { C: LanguageCellularAutomata } { q: C.Q } { w: Word } { t: ℕ } (h1: C.initial q) (h2: C.next (C.step_n w t) i = q): C.step_n w t i = q :=
  by 
  subst h2
  apply h1
  · rfl

theorem lemma_2_4_1_passive_initial_border (C: FCellularAutomata.{u}):
  ∃ C': FCellularAutomata.{u},
    C'.L = C.L
  ∧ C'.passive C'.border
  ∧ C'.initial C'.border
  ∧ DefinesTime.t C' = DefinesTime.t C
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
  

  have h (w: Word) t i: (C'.step_n w t i) = if i ≥ -t ∧ i < w.length + t then state (C.step_n w t i) (C.pow_t C.border t) else border := by
    induction t using LanguageCellularAutomata.step_n.induct generalizing i with
    | case1 =>
      simp [LanguageCellularAutomata.step_n, lemma_1_Q.unwrap, LanguageCellularAutomata.step_n, CellularAutomata.pow_t, LanguageCellularAutomata.embed_word, C', lemma_1_c]
      simp_all only [and_self, ↓reduceDIte, C']
      split
      next h => simp_all only [C']
      next h => simp_all only [not_and, not_lt, C']
    | case2 t ih =>
      simp [LanguageCellularAutomata.step_n, CellularAutomata.next]
      rw [ih, ih, ih]

      by_cases h: (i ≥ -(t - 1) ∧ i < w.length + t - 1)
      
      have x1: i - 1 ≥ -↑t ∧ i - 1 < ↑(List.length w) + ↑t := by omega
      have x2: i ≥ -↑t ∧ i < ↑(List.length w) + ↑t := by omega
      have x3: i + 1 ≥ -↑t ∧ i + 1 < ↑(List.length w) + ↑t := by omega
      have x4: i ≥ -↑(t + 1) ∧ i < ↑(List.length w) + ↑(t + 1) := by omega

      simp_all only [ge_iff_le, neg_sub, tsub_le_iff_right, neg_le_sub_iff_le_add, true_and, Int.reduceNeg, and_self, ↓reduceIte, C']
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right_1⟩ := x2
      obtain ⟨left_2, right_2⟩ := x3
      obtain ⟨left_3, right_3⟩ := x4
      simp_all only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
        add_neg_le_iff_le_add, and_self, ↓reduceIte, C']
      rfl


      
  
  /-
   C.step_n w t i = (C'.step_n w t i).unwrap (C.pow_t C.border t) ∧ (C.pow_t C.border t) = (C'.step_n w t i).unwrap2 (C.step_n w t i) := by
    induction t using LanguageCellularAutomata.step_n.induct generalizing i with
    | case1 =>
      simp [LanguageCellularAutomata.step_n, lemma_1_Q.unwrap, LanguageCellularAutomata.step_n, CellularAutomata.pow_t, LanguageCellularAutomata.embed_word]
      simp_all only [C', lemma_1_c]
      split
      next h =>
        simp_all only [true_and, C']
        rfl
      next h =>
        simp_all only [true_and, C']
        rfl

    | case2 t ih =>
      let bt := (C.pow_t C.border t)
      have h : bt = (C.pow_t C.border t) := by simp [bt]
      rw [←h] at ih
      
      unfold CellularAutomata.pow_t
      rw [←h]
      simp [LanguageCellularAutomata.step_n]
      constructor
-/





      --simp [CellularAutomata.pow_t, C', LanguageCellularAutomata.step_n, LanguageCellularAutomata.embed_word, lemma_1_c, lemma_1_Q.unwrap]
      --aesop?

  sorry



inductive LemmaCases where
  | computing
  | accept
  | reject
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

def lemma_C' (C: FCellularAutomata): FCellularAutomata := 
  let _h := C.inv_fin;
  let _x := C.d;
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

  have h (w: Word) n i: C.step_n w n i = (C'.step_n w n i).fst  := by
    induction n using LanguageCellularAutomata.step_n.induct generalizing i with
    | case1 =>
      simp [LanguageCellularAutomata.embed_word, LanguageCellularAutomata.step_n, C', lemma_C']
      split
      next h_1 => simp_all only [C']
      next h_1 => simp_all only [C']

    | case2 k ih =>
      unfold LanguageCellularAutomata.step_n CellularAutomata.next
      rw [ih]
      rw [ih]
      rw [ih]
      simp_all only [ne_eq, ite_not, C']
      rfl
      

  sorry

