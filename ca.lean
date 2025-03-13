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

def CellularAutomata.passive_set (Q: Set ca.Q) := ∀ a (b: Q) c, ca.δ a b c = b
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
    if h: i < 0 ∨ i ≥ word.length
    then ca.border
    else ca.embed (word.get ⟨i.toNat, by omega⟩)

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


inductive LemmaCases where
  | computing
  | accept
  | reject
deriving Inhabited, BEq, Repr, Fintype, DecidableEq

def LemmaQ Q := Q × LemmaCases

theorem lemma_2_3_1_F_delta_closed (C: FCellularAutomata):
  ∃ C': FCellularAutomata,
    C'.L = C.L
  ∧ DefinesTime.t C' = DefinesTime.t C
  ∧ C'.delta_closed_set C'.F_pos
  ∧ C'.delta_closed_set C'.F_neg
:= by
  have h := C.inv_fin
  have x := C.d
  have [z: DecidableEq (LemmaQ C.Q)]
  have [x: Fintype (LemmaQ C.Q)]
  
  let C': FCellularAutomata := {
    Q := LemmaQ C.Q,
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
    F_pos := { x: LemmaQ C.Q | x.snd = LemmaCases.accept },
    F_neg := { x: LemmaQ C.Q | x.snd = LemmaCases.reject },
  }

  have h (w: Word) n i: C.step_n w n i = (C'.step_n w n i).fst  := by
    induction n using LanguageCellularAutomata.step_n.induct generalizing i with
    | case1 => 
      simp [LanguageCellularAutomata.embed_word, LanguageCellularAutomata.step_n, C']
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


theorem lemma_2_4_1_passive_initial_border (C: FCellularAutomata):
  ∃ C': FCellularAutomata,
    C'.L = C.L
  ∧ C'.passive C'.border
  ∧ C'.initial C'.border
  ∧ DefinesTime.t C' = DefinesTime.t C
  ∧ (C.left_independent ↔ C'.left_independent)
  ∧ (C.right_independent ↔ C'.right_independent)
  := sorry
