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



def PMap (m: HashMap Nat Nat) (P: Nat → Nat → Prop): Prop := ∀ {n v}, m[n]? = some v -> P n v

def correct (n: Nat) (v: Nat): Prop := maxDollars_spec n = v

theorem empty_correct: PMap (HashMap.empty) correct := by
  unfold PMap
  intro n v h_eq
  rw [HashMap.getElem?_empty] at h_eq
  contradiction

theorem insert_correct {m: HashMap Nat Nat} {n v: Nat} (h1: PMap m correct) (h2: correct n v) : PMap (m.insert n v) correct := by
  unfold PMap at *
  intro n' v' h_eq
  rw [HashMap.getElem?_insert] at h_eq
  split at h_eq
  all_goals simp_all

structure Result (n: Nat) where
  r: Nat × HashMap Nat Nat
  h_value: correct n (r.fst)
  h_memo : PMap (r.snd) correct

def helperMemo' (n: Nat) (memo: HashMap Nat Nat) (h: PMap memo correct) : Result n :=
  match h_eq: memo[n]? with
  | some v => { r := (v, memo), h_value := h h_eq, h_memo := h }
  | none =>
    if h_if: n ≤ 8 then -- base case: sell coin directly
      let memo' := memo.insert n n
      have : maxDollars_spec n = n := by simp [h_if, maxDollars_spec]
      { r := (n, memo'), h_value := this, h_memo := insert_correct h this }
    else
      -- recursive: compute best exchange value, memoizing along the way
      let ⟨ r, h_v1, h_m1 ⟩  := helperMemo' (n / 2) memo h
      let ⟨ r2, h_v2, h_m2 ⟩  := helperMemo' (n / 3) r.snd h_m1
      let ⟨ r3, h_v3, h_m3 ⟩  := helperMemo' (n / 4) r2.snd h_m2
      let best := max n (r.fst + r2.fst + r3.fst)
      let memo' := r3.snd.insert n best
      have : maxDollars_spec n = best := by
        unfold maxDollars_spec
        rw [h_v1, h_v2, h_v3]
        simp [h_if, best]
      { r := (best, memo'), h_value := this, h_memo := insert_correct h_m3 this }


theorem helperMemo'_eq_helperMemo {memo} (h: PMap memo correct):
    (helperMemo' n memo h).r = (helperMemo n memo)
    := by
  induction n using Nat.strongRecOn generalizing memo h
  case ind k ih =>
  unfold helperMemo helperMemo'
  split
  case h_1 v heq => simp [heq, h]
  case h_2 heq =>
    split
    case isTrue hif => simp [heq]
    case isFalse hif =>

      sorry -- this should be trivial, but I don't know how to do it
