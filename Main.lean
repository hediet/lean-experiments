import Mathlib
import Lean

open Lean Elab Command Term Meta

def main : IO Unit :=
  IO.println "Hello, Lean World!"


structure OffsetRange where
  start : Nat
  endEx : Nat
  inv : start ≤ endEx

instance : Repr OffsetRange where
  reprPrec r prec := Repr.addAppParen (repr s!"[{r.start} toEx {r.endEx}]") prec

def OffsetRange.contains (r : OffsetRange) (i : Int) : Bool :=
  r.start ≤ i && i < r.endEx

def OffsetRange.isEmpty (r : OffsetRange) : Bool :=
  r.start >= r.endEx

def OffsetRange.length (r : OffsetRange) : ℕ :=
  r.endEx - r.start

def OffsetRange.delta (r : OffsetRange) (i : ℤ) : OffsetRange :=
  { start := r.start + i.toNat, endEx := r.endEx + i.toNat, inv := by simp [r.inv] }

@[simp]
def OffsetRange.is_before_or_touching (r1 r2 : OffsetRange) : Bool :=
  r1.endEx ≤ r2.start

syntax  "[" term "toEx" term "]" : term
macro_rules | `([$x toEx $i]) => `(OffsetRange.mk $x $i (by simp))





structure Replacement (α : Type u) where
  range : OffsetRange
  replacement : List α

instance {α : Type u} { h: Repr α } : Repr (Replacement α) where
  reprPrec e prec := Repr.addAppParen (repr e.range ++ " |-> " ++ repr e.replacement) prec

def Replacement.apply {α : Type u} (edit : Replacement α) (original : List α) : List α :=
  let before := original.extract 0 edit.range.start
  let after := original.extract edit.range.endEx original.length
  before.append (edit.replacement.append after)

syntax  term "|->" term : term
macro_rules | `($range |-> $repl) => `(Replacement.mk $range $repl)

def Replacement.delta {α : Type u} (r : Replacement α) : ℤ := r.replacement.length - r.range.length

def Replacement.delta_range {α : Type u} (r : Replacement α) (delta: ℤ): Replacement α :=
  { range := r.range.delta delta, replacement := r.replacement }

def Replacement.new_length {α : Type u} (r : Replacement α) : ℕ := r.replacement.length




def replacement_is_before {α : Type u} (r1 r2: Replacement α): Prop :=
  r1.range.is_before_or_touching r2.range





@[simp]
def neighboring {α : Type u} (list: List α) (prop : α → α → Prop): Prop :=
  match list with
  | [] => true
  | [_a] => true
  | (a::b::rs) => prop a b ∧ neighboring (b::rs) prop




-- neighboring replacements replacement_is_before

structure Edit (α : Type u) where
  replacements : List (Replacement α)

instance {α : Type u} : HAppend (Replacement α) (Replacement α) (Edit α) where
  hAppend r1 r2 := Edit.mk [r1, r2]

instance {α : Type u} : HAppend (Edit α) (Replacement α) (Edit α) where
  hAppend e r := { replacements := e.replacements ++ [r] }

instance {α : Type u} : HAppend (Replacement α) (Edit α) (Edit α) where
  hAppend r e := { replacements := r :: e.replacements }

instance {α : Type u} : HAppend (Edit α) (Edit α) (Edit α) where
  hAppend e1 e2 := { replacements := e1.replacements ++ e2.replacements }


def Edit.apply {α : Type u} (edit : Edit α) (original : List α) : List α :=
  edit.replacements.foldr Replacement.apply original

def Edit.delta_ranges {α : Type u} (edit : Edit α) (delta : ℤ) : Edit α :=
  { replacements := edit.replacements.map (fun r => { range := r.range.delta delta, replacement := r.replacement }) }




inductive EditSection (α : Type u) where
  | copy:  ℕ → EditSection α
  | insert: List α → EditSection α

def EditSection.apply {α : Type u} (s : EditSection α) (original : List α) : (List α, List α) :=
  match s with
  | EditSection.copy n => (original.extract 0 n, original.extract n original.length)
  | EditSection.insert l => (original, l ++ original)

structure EditSections (α : Type u) where
  sections: List (EditSection α)




def Edit.compose {α : Type u} (e2 e1 : Edit α) : Edit α :=
  match (e2.replacements, e1.replacements) with
  | ([], _) => e2
  | (_, []) => e1
  | ((r2::r2s), (r1::r1s)) =>
    if r1.range.start + r1.new_length <= r2.range.start then
      r1 ++ ((e2.delta_ranges (-r1.delta)).compose (Edit.mk r1s))
    else if r2.range.endEx <= r1.range.start then
      r2 ++ ((Edit.mk r2s).compose e2)
    else
      sorry

syntax:60 term " o " term:61 : term

macro_rules
  | `($e2 o $e1) => `(Edit.compose $e2 $e1)

syntax (name := myTuple) "{" term,* "}" : term
macro_rules (kind := myTuple)
  | `({ $xs,* }) => `(Edit.mk ([ $xs,* ]))



def arr := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def r := { [1 toEx 2] |-> [100, 101, 102], [ 6 toEx 9 ] |-> [] }
#eval! r.apply arr






def replacement_delta {α : Type u} (r : Replacement α) : ℤ :=
  Int.ofNat r.replacement.length - r.range.length

def total_delta {α : Type u} (edit : Edit α) : ℤ := List.sum $ edit.replacements.map $ replacement_delta

def list_map_neighboring
  {α β : Type u} (p: α → α → Prop) (p₂: β -> β -> Prop) (f: α → β) (h₁: ∀a₁ a₂, p a₁ a₂ -> p₂ (f a₁) (f a₂))
  (list: List α) (h₂: neighboring list p): neighboring (list.map f) p₂ :=
  by induction list
   with
    | nil => simp
    | cons a1 a1s => cases a1s; simp; simp_all only [List.map_cons, neighboring, and_self]

def delta_maintains_offset_range_sorting (r1 r2: OffsetRange) (i: ℤ) (h: r1.is_before_or_touching r2): (r1.delta i).is_before_or_touching (r2.delta i) :=
  by simp_all [h, OffsetRange.is_before_or_touching, OffsetRange.delta]

def delta_replacement {α : Type u} (i : ℤ) (r : Replacement α): Replacement α :=
  { range := r.range.delta i, replacement := r.replacement }

def delta_maintains_replacement_sorting (r1 r2: Replacement α) (i: ℤ) (h: r1.range.is_before_or_touching r2.range):
  replacement_is_before (delta_replacement i r1) (delta_replacement i r2) :=
    delta_maintains_offset_range_sorting r1.range r2.range i h

def delta_edit_ranges {α : Type u} (edit : Edit α) (i : ℤ): Edit α :=
  { replacements := edit.replacements.map (delta_replacement i),
    inv_sorted := by
      apply list_map_neighboring
      apply delta_maintains_replacement_sorting


      intro
      intro
      intro
      unfold replacement_is_before
      aesop

      have x :=edit.inv_sorted
      unfold replacement_is_before at x
      aesop

  }

-- x: A -> B,         y: B
