
import Mathlib

open Set List

noncomputable def find_some { α } (f: ℕ → Option α): Option α :=
  let _dec := Classical.dec;
  if h: ∃ n, (f n).isSome = true
  then (f (Nat.find h)).get (Nat.find_spec h)
  else none


def pop_nat_fn {α} (f: ℕ → α) := fun n => f (n + 1)

def find_some_bounded { α } (f: ℕ → Option α): ℕ -> Option α
| 0 => none
| n + 1 =>
  match f 0 with
  | some val => some val
  | none => find_some_bounded (pop_nat_fn f) n


lemma find_some_eq_none_iff { α } { f: ℕ → Option α }: find_some f = none ↔ ∀ k, f k = none := by
  unfold find_some
  split_ifs
  case pos h =>
    simp only [reduceDIte, h, reduceCtorEq, false_iff, not_forall]
    rcases h with ⟨n, hn⟩
    use n
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [Option.isSome_none, Bool.false_eq_true]
  case neg h =>
    simp_all [h]

lemma find_some_eq_some_iff { α } { f: ℕ → Option α } (val): find_some f = some val ↔ ∃ k, f k = some val ∧ ∀ j, j < k → f j = none := by
  let _dec := Classical.dec;
  unfold find_some
  simp only [Option.some_get, Option.dite_none_right_eq_some]

  constructor
  · intro h
    let ⟨h', h⟩ := h
    let ⟨n, h''⟩ := h'

    use Nat.find h'
    simp_all [Nat.find_min h']

  · intro h
    let ⟨k, hk⟩ := h

    have h'': ∃ n, (f n).isSome = true := by
      use k
      simp [hk.1]

    use h''

    have hk2 : (f k).isSome = true ∧ ∀ j < k, (f j).isSome ≠ true := by simp_all

    rw [←Nat.find_eq_iff h''] at hk2
    simp_all

lemma unroll_all (m) (p: ℕ → Prop): (∀ j < (m + 1), p j) ↔ p 0 ∧ ∀ k < m, p (k + 1) := by
  apply Iff.intro
  · intro a
    simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, add_lt_add_iff_right,
      implies_true, and_self]
  · intro a j a_1
    obtain ⟨left, right⟩ := a
    have right := right (j - 1)
    cases j
    case zero => exact left
    case succ n => simp_all


lemma find_some_bounded_eq_none_iff { α } { f: ℕ → Option α } (k): find_some_bounded f k = none ↔ ∀ j < k, f j = none := by
  induction k generalizing f
  case zero => simp [find_some_bounded]
  case succ n ih =>
    unfold find_some_bounded
    have ih := @ih (pop_nat_fn f)
    cases c: f 0
    · simp [ih, pop_nat_fn, unroll_all n (fun k => f k = none), c]
    · simp
      use 0
      simp [c]


lemma find_some_bounded_some_iff { α } { f: ℕ → Option α } (k) (val): find_some_bounded f k = some val ↔ ∃ j < k, f j = some val ∧ ∀ m < j, f m = none := by
  sorry



lemma find_some_eq_none_iff_find_some_bounded_eq_none { α } { f: ℕ → Option α }: (∀ k, find_some_bounded f k = none) ↔ find_some f = none := by
  rw [find_some_eq_none_iff]
  conv =>
    pattern find_some_bounded _ _ = _
    rw [find_some_bounded_eq_none_iff]
  apply Iff.intro
  · intro a k
    simp [a (k+1) k]
  · intro a k j a_1
    simp_all only


lemma find_some_of_find_some_bounded { α } { f: ℕ → Option α } {val} (h: find_some_bounded f k = some val): find_some f = some val := by

  rw [find_some_eq_some_iff]

  rw [find_some_bound]

lemma find_some_bounded_eq_none_iff_find_some_eq_none { α } { f: ℕ → Option α } (val): ∃ k, find_some_bounded f k = some val ↔ find_some f = some val := by
  sorry


structure RepeatingFunction (f: ℕ → M) where
  k: ℕ
  inv: f '' univ = f '' { n | n ≤ k }



def iterative_function {M} (f: ℕ → M) := ∀ i j, f i = f j → f (i+1) = f (j+1)

lemma iterative_function_is_cyclic {M} (f: ℕ → M) (h1: iterative_function f) (o i: ℕ) (h2: f i = f (i + o)): f (i + k) = f (i + k % o) := by
  --unfold iterative_function at h1
  let r := k % o
  have h := Nat.div_add_mod k o
  conv =>
    pattern (i + k)
    rw [←h]



def k' (k a b: ℕ) := if k <= a then k else a + ((k-a) % b)

lemma apply_iterated_mod {M} (h: Fintype M): ∃ a b, a + b ≤ h.card + 1 ∧ ∀ k: (apply_iterated f m) k = (apply_iterated f m) (k' k a b) :=
/-

∃ k1 ≠ k2 ∈ {0...h.card+1}: g k1 = g k2
a := k1
b := k2 - k1


f a = f b => f (a + 1) = f (b + 1)
f a = f (a + k) => f (a + j) = f (a + j % k)

g (k1 + (i * b)) = g k1

g (k1 + j) = g (k2 + j)

a + b

-/
sorry


def repeating_function_of_iterate_fin_type { M } (h: Fintype M) { f: M → M } (m: M): RepeatingFunction (apply_iterated f m) := {
  k := h.card
  inv := by
    ext x
    constructor
    · intro h
      simp at h
      rcases h with ⟨y, hy⟩
      simp

      sorry
    · intro h
      aesop
}

def repeating_function_of_composition { α β } { g: α → β } { f: ℕ → α } (h: RepeatingFunction f): RepeatingFunction (g ∘ f) := {
  k := h.k
  inv := by rw [image_comp, image_comp, h.inv]
}




lemma find_some_bounded_eq_find_some_of_repeating_function { α } { f: ℕ → Option α } (h: RepeatingFunction f): find_some_bounded f h.k = find_some f := by
  cases c: find_some_bounded f h.k
  case some val =>
    simp [find_some_bounded_eq_find_some' c]
  case none =>
