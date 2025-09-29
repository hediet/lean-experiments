import Mathlib

section Utilities

noncomputable def min_nat (set: Set ℕ) :=
  let _dec := Classical.dec;
  if h: ∃ n, n ∈ set
  then some (Nat.find h)
  else none

def apply_iterated (f: α → α) (a: α) (k: ℕ) := Nat.iterate f k a

end Utilities

section Word

class Alphabet where
  (α: Type 0)
  [fin: Fintype α]

variable [Alphabet]

def α [Alphabet] := Alphabet.α

def Word := List α

def Word.range (w: Word): Set ℤ := { i: ℤ | i ≥ 0 ∧ i < w.length }

instance (w: Word) (i: ℤ) [d: Decidable (i ∈ { i: ℤ | i ≥ 0 ∧ i < w.length })]:
  Decidable (i ∈ w.range) := d

def Word.get' (w: Word) (i: ℤ) (h: i ∈ w.range) := w.get ⟨
    i.toNat,
    by simp only [range, ge_iff_le, Set.mem_setOf_eq] at h; omega
⟩

end Word

variable [Alphabet]

section CellAutomata

structure CellAutomata where
  Q: Type u
  δ: Q → Q → Q → Q
  [inv_decidable_q: DecidableEq Q]
  [inv_fin_q: Fintype Q]

def Config (Q: Type*) := ℤ → Q

variable (C: CellAutomata)

def CellAutomata.next (c: Config C.Q): Config C.Q :=
  fun i => C.δ (c (i - 1)) (c i) (c (i + 1))

def CellAutomata.nextt: Config C.Q → ℕ → Config C.Q := apply_iterated C.next


/-- A set is passive if every element stays the same when it is just surrounded by other elements from the set.  -/
def CellAutomata.passive_set (Q: Set C.Q) := ∀ (a b c: Q), C.δ a b c = b

/-- A state is passive if it stays the same when it is just surrounded by itself. -/
def CellAutomata.passive (q: C.Q) := C.passive_set { q }

/-- A set state is closed if no matter what, cells having such a state remain in that set. -/
def CellAutomata.delta_closed_set (Q: Set C.Q) := ∀ a (b: Q) c, C.δ a b c ∈ Q
/-- A state is dead if no matter what, it doesn't change. -/
def CellAutomata.dead (q: C.Q) := C.delta_closed_set {q}

def CellAutomata.left_independent := ∀ (q1 q2 q3 q1'), C.δ q1 q2 q3 = C.δ q1' q2 q3
def CellAutomata.right_independent := ∀ (q1 q2 q3 q3'), C.δ q1 q2 q3 = C.δ q1 q2 q3'

/-- A state is initial if it cannot be created -/
def CellAutomata.initial (q: C.Q) := ∀ a b c, C.δ a b c = q → b = q



def δδ { C: CellAutomata } (q: C.Q) := C.δ q q q

def δδt { C: CellAutomata } (q: C.Q) := apply_iterated δδ q

end CellAutomata

section LanguageDefinitions

class DefinesLanguage (CA: Type u) where
  L: CA -> Language α

def ℒ {CA: Type u} [DefinesLanguage CA] (s: (Set CA)): Set (Language α) :=
  fun L => ∃ ca: CA, ca ∈ s ∧ L = DefinesLanguage.L ca

class DefinesTime (CA: Type u) where
  time: CA -> Word → WithTop ℕ

noncomputable def time' [DefinesTime CA] (C: CA) (w: Word): ℕ := (DefinesTime.time C w).getD 0

end LanguageDefinitions

section LCellAutomata

/--
 A cellular automaton that can map words to a configuration.
 This is the basis for cellular automata that can recognize languages.
-/
structure LCellAutomata extends CellAutomata where
  embed: α → Q
  border: Q

def LCellAutomata.embed_word (ca: LCellAutomata) (w: Word): Config ca.Q :=
  fun i =>
    if h: i ∈ w.range
    then ca.embed (w.get' i h)
    else ca.border

/-- To compute the nth configuration of a word, we compute the nth follow configuration of the word's embedding. -/
def LCellAutomata.comp (C: LCellAutomata) (w: Word) := C.nextt (C.embed_word w)

/-- A state is an internal state if embedding an input does not produce it. -/
def LCellAutomata.internal_state {C: LCellAutomata} (q: C.Q) := ∀ a: α, C.embed a ≠ q

end LCellAutomata

section FCellAutomata

/-- A cellular automaton that can recognize languages by defining "accepting" and "rejecting" states. -/
structure FCellAutomata extends LCellAutomata where
  /--
    * `none`: continue
    * `some true`: accept
    * `some false`: reject
  -/
  state_accepts: Q -> Option Bool

def FCellAutomata.config_accepts (C: FCellAutomata) (c: Config C.Q) := C.state_accepts (c 0)

noncomputable def FCellAutomata.time (C: FCellAutomata) (w: Word): Option ℕ :=
  min_nat { t | C.config_accepts (C.comp w t) ≠ none }

def FCellAutomata.accepts (C: FCellAutomata) (w: Word) :=
  match C.time w with
  | some t => C.config_accepts (C.comp w t) = some true
  | none => False

def FCellAutomata.L (C: FCellAutomata): Language α := { w: Word | C.accepts w }

def FCellAutomata.F_pos { C': FCellAutomata } := { q: C'.Q | C'.state_accepts q = some true }
def FCellAutomata.F_neg { C': FCellAutomata } := { q: C'.Q | C'.state_accepts q = some false }

def FCellAutomata.accept_delta_closed (C: FCellAutomata) := C.delta_closed_set C.F_pos ∧ C.delta_closed_set C.F_neg


def FCellAutomatas [α: Alphabet]: Set FCellAutomata := fun _a => true

instance : DefinesLanguage FCellAutomata where
  L ca := ca.L

noncomputable instance : DefinesTime FCellAutomata where
  time ca w := ca.time w

instance : Coe FCellAutomata CellAutomata where
  coe ca := ca.toCellAutomata

end FCellAutomata

section tCellAutomata

structure tCellAutomata extends LCellAutomata where
  t: ℕ → ℕ
  F_pos: Set Q

def tCellAutomata.L (C: tCellAutomata): Language α := fun w =>
  (C.comp w (C.t w.length)) 0 ∈ C.F_pos

def tCellAutomatas [α: Alphabet]: Set tCellAutomata := Set.univ

instance : DefinesLanguage tCellAutomata where
  L ca := ca.L

instance : DefinesTime tCellAutomata where
  time ca w := some (ca.t w.length)

instance : Coe tCellAutomata CellAutomata where
  coe ca := ca.toCellAutomata

end tCellAutomata

noncomputable def t_max [DefinesTime CA] (ca: CA) (n: ℕ): WithTop ℕ :=
  sSup (DefinesTime.time ca '' { w : Word | w.length = n })

def halts [DefinesTime CA] (ca: CA): Prop :=
  ∀ n: ℕ, t_max ca n ≠ none

noncomputable def t_max' [DefinesTime CA] (ca: CA) (h: halts ca) (n: ℕ): ℕ :=
  (t_max ca n).get (by simp_all[halts, Option.isSome_iff_ne_none])


def with_time { β: Type u } [DefinesTime β] (fns: Set (ℕ → ℕ)) (set: Set β): Set β :=
  fun ca => ca ∈ set ∧ halts ca ∧ ((h: halts ca) → ((t_max' ca h) ∈ fns))


syntax "t⦃" term "⦄" : term
macro_rules | `(t⦃ $expr ⦄) => `(with_time { fun $(Lean.mkIdent `n) => $expr })

def RT := { C ∈ tCellAutomatas | ∀ n, C.t n = n - 1 }
