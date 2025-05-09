import Mathlib
import CellularAutomatas.find_some

open Set

class Alphabet where
  (α: Type 0)

variable [Alphabet]

def α [Alphabet] := Alphabet.α

def Word := List α

structure CellAutomata where
  Q: Type u
  δ: Q → Q → Q → Q
  [inv_decidable_q: DecidableEq Q]
  [inv_fin_q: Fintype Q]

def Config (Q: Type*) := ℤ → Q

def CellAutomata.next (ca: CellAutomata) (c: Config ca.Q): Config ca.Q :=
  fun i => ca.δ (c (i - 1)) (c i) (c (i + 1))

def CellAutomata.comp (ca: CellAutomata) (n: ℕ) (c: Config ca.Q): Config ca.Q :=
  match n with
  | 0 => c
  | n + 1 => ca.next (ca.comp n c)

variable (ca: CellAutomata)

def CellAutomata.passive_set (Q: Set ca.Q) := ∀ (a b c: Q), ca.δ a b c = b
def CellAutomata.passive (q: ca.Q) := ca.passive_set { q }

def CellAutomata.delta_closed_set (Q: Set ca.Q) := ∀ a (b: Q) c, ca.δ a b c ∈ Q
def CellAutomata.dead (q: ca.Q) := ca.delta_closed_set {q}

def CellAutomata.left_independent := ∀ (q1 q2 q3 q1'), ca.δ q1 q2 q3 = ca.δ q1' q2 q3
def CellAutomata.right_independent := ∀ (q1 q2 q3 q3'), ca.δ q1 q2 q3 = ca.δ q1 q2 q3'

def CellAutomata.initial (q: ca.Q) := ∀ a b c, ca.δ a b c = q → b = q



def δδ { C: CellAutomata } (q: C.Q) := C.δ q q q

def δδn { C: CellAutomata } (q: C.Q) := apply_iterated δδ q



class DefinesLanguage (CA: Type u) where
  L: CA -> Language α

def ℒ [DefinesLanguage CA] (s: (Set CA)): Set (Language α) :=
  fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca

class DefinesTime (CA: Type u) where
  t: CA -> Word → Option ℕ


-- # =============== LCellAutomata ===============

structure LCellAutomata extends CellAutomata where
  embed: α → Q
  border: Q

def LCellAutomata.embed_word (ca: LCellAutomata) (word: Word): Config ca.Q :=
  fun i =>
    if h: i ≥ 0 ∧ i < word.length
    then ca.embed (word.get ⟨i.toNat, by omega⟩)
    else ca.border

def LCellAutomata.comp (C: LCellAutomata) (w: Word)
| 0 => C.embed_word w
| t + 1 => C.next (C.comp w t)

/-- A state is an internal state if embedding an input does not produce it. -/
def LCellAutomata.internal_state {C: LCellAutomata} (q: C.Q) := ∀ a: α, C.embed a ≠ q



-- # =============== FCellAutomata ===============

structure FCellAutomata extends LCellAutomata where
  /--
    * `none`: continue
    * `some true`: accept
    * `some false`: reject
  -/
  state_accepts: Q -> Option Bool

noncomputable def min_nat (set: Set ℕ) :=
  let _dec := Classical.dec;
  if h: ∃ n, n ∈ set
  then some (Nat.find h)
  else none

noncomputable def FCellAutomata.time (C: FCellAutomata) (w: Word): Option ℕ :=
  min_nat { t | C.state_accepts (C.comp w t 0) ≠ none }

def FCellAutomata.accepts (C: FCellAutomata) (w: Word) :=
  match C.time w with
  | some t => C.state_accepts (C.comp w t 0) = some true
  | none => False

def FCellAutomata.L (C: FCellAutomata): Language α := { w: Word | C.accepts w }

def FCellAutomatas [α: Alphabet]: Set FCellAutomata := fun _a => true


instance : DefinesLanguage FCellAutomata where
  L ca := ca.L

instance : Coe FCellAutomata CellAutomata where
  coe ca := ca.toCellAutomata



-- # =============== tCellAutomata ===============

structure tCellAutomata extends LCellAutomata where
  t: ℕ → ℕ
  F_pos: Set Q

def tCellAutomata.L (C: tCellAutomata): Language α := fun w =>
  (C.comp w (C.t w.length)) 0 ∈ C.F_pos

def tCellAutomatas [α: Alphabet]: Set tCellAutomata := fun _a => true

instance : DefinesLanguage tCellAutomata where
  L ca := ca.L

instance : Coe tCellAutomata CellAutomata where
  coe ca := ca.toCellAutomata


/-
def t_max [DefinesTime CA] (ca: CA) (n: ℕ): Option ℕ := sorry

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ := sorry
-/

/-
instance : DefinesTime FCellAutomata where
  t ca := sorry
-/


/-
instance : DefinesTime tCellAutomata where
  t ca := sorry


def OCA_L { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.left_independent ca

def OCA_R { β: Type u } [Coe β CellAutomata] (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ CellAutomata.right_independent ca

def rt { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))

syntax term "&" term : term
macro_rules | `($a & $b) => `($b $a)



def RT := tCellAutomatas & rt { fun n => n - 1 }

theorem X: ℒ (RT) = ℒ (FCellAutomatas & OCA_L) := sorry
-/
