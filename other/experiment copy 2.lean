import Std.Data.HashMap
import Aesop
open Std


def maxDollars_spec (n : Nat) : Nat :=
  if n ≤ 8 then
  -- Base case: for `n ≤ 8`, it's better to sell the coin directly.
    n
  else
  -- Recursive case: choose the maximum between selling the coin directly and exchanging it.
    max n (maxDollars_spec (n / 2) + maxDollars_spec (n / 3) + maxDollars_spec (n / 4))




def helperMemo : Nat → HashMap Nat Nat → Nat × HashMap Nat Nat
  | n, memo =>
    match memo[n]? with
    | some v => (v, memo)  -- already cached
    | none =>
      if n ≤ 8 then          -- base case: sell coin directly
        let memo' := memo.insert n n
        (n, memo')
      else
        -- recursive: compute best exchange value, memoizing along the way
        let (v1, memo1) := helperMemo (n / 2) memo
        let (v2, memo2) := helperMemo (n / 3) memo1
        let (v3, memo3) := helperMemo (n / 4) memo2
        let best := max n (v1 + v2 + v3)
        let memo' := memo3.insert n best
        (best, memo')

def maxDollarsMemo (n : Nat) : Nat :=
  (helperMemo n (HashMap.empty)).fst


def memo_map_correct (m: HashMap Nat Nat): Prop := ∀ {n v}, m[n]? = some v -> maxDollars_spec n = v

theorem empty_memo_correct: memo_map_correct (HashMap.empty) := by simp [memo_map_correct]

theorem correct_insert_maintains_correctness m (h1: memo_map_correct m) (v k) (h2: v = maxDollars_spec k):
    memo_map_correct (m.insert k v) := by
  unfold memo_map_correct at *
  intro n v c
  rw [HashMap.getElem?_insert] at c
  split at c
  all_goals simp_all



theorem helperMemo_correct (n: Nat) (m) (m_h: memo_map_correct m): (helperMemo n m).fst = maxDollars_spec n ∧ memo_map_correct (helperMemo n m).snd := by
  induction n using Nat.strongRecOn generalizing m
  case ind n ih =>

  generalize r_def : helperMemo n m = r
  let (rv, rm) := r
  unfold helperMemo at r_def
  split at r_def

  case h_1 x v heq => simp_all [m_h heq]
  case h_2 v' c =>

    split at r_def
    case isTrue hc =>
      rw [Prod.mk.injEq] at r_def
      rw [←r_def.1, ←r_def.2] at *
      have : maxDollars_spec n = n := by
        unfold maxDollars_spec
        simp only [ite_true, hc]
      have z := @correct_insert_maintains_correctness m m_h n n this.symm
      simp [z, this]

    case isFalse hc =>
      split at r_def; next tpl1 v1 memo1 eq1 =>
      split at r_def; next tpl2 v2 memo2 eq2 =>
      split at r_def; next tpl3 v3 memo3 eq3 =>

      have ih1 := ih (n / 2) (by omega) m m_h
      rw [eq1] at ih1
      have ih2 := ih (n / 3) (by omega) memo1 ih1.2
      rw [eq2] at ih2
      have ih3 := ih (n / 4) (by omega) memo2 ih2.2
      rw [eq3] at ih3

      have : max n (v1 + v2 + v3) = maxDollars_spec n := by
        unfold maxDollars_spec
        have x := ih1.1
        dsimp at *
        simp [hc, ih1.1, ih2.1, ih3.1]
      simp at r_def
      simp [this, ←r_def.1]
      rw [←r_def.2]
      exact @correct_insert_maintains_correctness _ ih3.2 _ _ this


theorem memo_correct : ∀ (n : Nat), maxDollarsMemo n = maxDollars_spec n := by
  intro n
  unfold maxDollarsMemo
  cases c: (helperMemo n HashMap.empty)
  case mk fst snd =>
  have this := helperMemo_correct n (HashMap.empty) empty_memo_correct c
  simp_all
