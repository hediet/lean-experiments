
import Mathlib

open Set List Nat

structure Indexed (α: Type) where
  val: α
  idx: ℕ

noncomputable def find_some_idx { α } (f: ℕ → Option α): Option (Indexed α) :=
  let _dec := Classical.dec;
  if h: ∃ n, (f n).isSome = true
  then let idx := Nat.find h; some ⟨ (f idx).get (Nat.find_spec h), idx ⟩
  else none

noncomputable def find_some { α } (f: ℕ → Option α) := Option.map Indexed.val (find_some_idx f)

private def find_some_bounded_acc { α } (f: ℕ → Option α) (idx: ℕ): ℕ -> Option (Indexed α)
| 0 => none
| n + 1 =>
  match f idx with
  | some val => some ⟨ val, idx ⟩
  | none => find_some_bounded_acc f (idx + 1) n

def find_some_bounded_idx { α } (f: ℕ → Option α) (k: ℕ) := find_some_bounded_acc f 0 k

def find_some_bounded { α } (f: ℕ → Option α) := Option.map Indexed.val ∘ find_some_bounded_idx f

lemma find_some_idx_eq_none_iff { α } { f: ℕ → Option α }: find_some_idx f = none ↔ ∀ i, f i = none := by
  unfold find_some_idx
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

lemma find_some_idx_eq_some_iff { α } { f: ℕ → Option α } (val): find_some_idx f = some val ↔ f val.idx = some val.val ∧ ∀ i < val.idx, f i = none := by
  let _dec := Classical.dec;
  unfold find_some_idx
  simp only [Option.some_get, Option.dite_none_right_eq_some]

  constructor
  · intro h
    let ⟨h', h⟩ := h
    let ⟨n, h''⟩ := h'
    simp only [Option.some.injEq] at h
    simp only [←h]
    simp_all []

  · intro h
    let ⟨k, hk⟩ := h

    have h'': ∃ n, (f n).isSome = true := by
      use val.idx
      simp [k]

    use h''
    simp

    have hk2 : (f val.idx).isSome = true ∧ ∀ j < val.idx, (f j).isSome ≠ true := by simp_all

    rw [←Nat.find_eq_iff h''] at hk2
    simp_all

lemma unroll_all2 (b) (p: ℕ → Prop): (∀ j, b ≤ j → p j) ↔ p b ∧ ∀ j, b + 1 ≤ j → p j := by
  apply Iff.intro
  · intro a
    simp_all only [le_refl, true_and]
    intro j a_1
    have y: b ≤ j := by omega
    simp [a j y]

  · intro a j a_1
    obtain ⟨left, right⟩ := a
    have right := right j
    by_cases c: b + 1 ≤ j
    · exact right c
    · have h: j = b := by omega
      simp_all


private lemma find_some_bounded_acc_eq_none_iff { α } { f: ℕ → Option α } (s len): find_some_bounded_acc f s len = none ↔ ∀ j ∈ Set.Ico s (s + len), f j = none := by
  induction len generalizing s
  case zero =>
    unfold find_some_bounded_acc
    simp [imp_false, true_iff]

  case succ n ih =>
    unfold find_some_bounded_acc
    have ih := ih (s+1)
    cases c: f s
    · simp [ih]
      conv =>
        arg 2
        rw [unroll_all2]

      simp_all [c]
      have h: s + (n + 1) = s + 1 + n := by omega
      simp [h]

    · simp
      use s
      simp [c]


lemma find_some_bounded_eq_none_iff { α } { f: ℕ → Option α } (k): find_some_bounded_idx f k = none ↔ ∀ j < k, f j = none := by simp [find_some_bounded_idx, find_some_bounded_acc_eq_none_iff]


private lemma find_some_bounded_acc_eq_some_iff { α } { f: ℕ → Option α } (s len val): find_some_bounded_acc f s len = some val ↔ f val.idx = some val.val ∧ val.idx ∈ Set.Ico s (s + len) ∧ ∀ j ∈ Set.Ico s val.idx, f j = none := by
  induction len generalizing s
  case zero =>
    unfold find_some_bounded_acc
    simp

  case succ n ih =>
    unfold find_some_bounded_acc
    have ih := ih (s+1)
    cases c: f s
    case none =>
      simp [ih]
      intro h

      conv =>
          arg 2
          rw [unroll_all2]

      simp [c]

      intro hh


      have x: val.idx ≠ s := by
        simp_all only [mem_Ico, and_imp, true_and, ne_eq]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [reduceCtorEq]
      omega

    case some =>
      simp
      constructor
      · intro h
        simp [←h, c]
        intro j
        intro h1
        intro h2
        exfalso
        exact Nat.lt_irrefl s (Nat.lt_of_le_of_lt h1 h2)

      · intro h
        cases x: val with | mk val_val val_idx =>
        simp_all [x]

        by_cases c2: s = val_idx
        · simp_all
        · have x: s < val_idx := by
            have y := h.2.1.1
            omega
          have y := h.2.2 s
          simp at y
          have y := y x
          rename_i x_1 y_1
          subst x_1
          simp_all only [le_refl, reduceCtorEq]




lemma find_some_bounded_idx_eq_some_iff { α } { f: ℕ → Option α } { k val }: find_some_bounded_idx f k = some val ↔ f val.idx = some val.val ∧ val.idx < k ∧ ∀ j < val.idx, f j = none := by
  simp [find_some_bounded_idx, find_some_bounded_acc_eq_some_iff]

lemma find_some_bounded_eq_some_iff { α } { f: ℕ → Option α } { k val }: find_some_bounded f k = some val ↔ ∃ t, f t = some val ∧ t < k ∧ ∀ j < t, f j = none := by
  simp [find_some_bounded, find_some_bounded_idx_eq_some_iff]
  constructor
  · intro h
    have ⟨ a, h ⟩ := h
    use a.idx
    simp_all
  · intro h
    have ⟨ a, h ⟩ := h
    use ⟨ val, a ⟩


lemma find_some_eq_none_iff_find_some_bounded_eq_none { α } { f: ℕ → Option α }: (∀ k, find_some_bounded_idx f k = none) ↔ find_some_idx f = none := by
  rw [find_some_idx_eq_none_iff]
  conv =>
    pattern find_some_bounded_idx _ _ = _
    rw [find_some_bounded_eq_none_iff]
  apply Iff.intro
  · intro a k
    simp [a (k+1) k]
  · intro a k j a_1
    simp_all only


lemma find_some_of_find_some_bounded { α } { f: ℕ → Option α } {val} (h: find_some_bounded_idx f k = some val): find_some_idx f = some val := by
  rw [find_some_idx_eq_some_iff]
  rw [find_some_bounded_idx_eq_some_iff] at h
  simp_all

lemma find_some_bounded_eq_none_iff_find_some_eq_none { α } { f: ℕ → Option α } (val): ∃ k, find_some_bounded_idx f k = some val ↔ find_some_idx f = some val := by
  rw [find_some_idx_eq_some_iff]
  simp [find_some_bounded_idx_eq_some_iff]
  use val.idx + 1
  simp





structure RepeatingFunction (f: ℕ → M) where
  k: ℕ
  inv: f '' univ = f '' { n | n < k }



def iterative_function {M} (f: ℕ → M) := ∀ i j, f i = f j → f (i+1) = f (j+1)




def k' (k a b: ℕ) := if k ≤ a then k else a + ((k-a) % b)

lemma k'_bounded (k a b) (h: b > 0): k' k a b ≤ a + (b - 1) := by
  unfold k'
  by_cases c: k ≤ a
  · simp [c]
    omega
  · simp [c]
    have x := (Nat.mod_lt (k-a) h)
    omega


def apply_iterated (f: α → α) (a: α) (k: ℕ) := Nat.iterate f k a

@[simp]
theorem apply_iterated_fixed {α: Type u} {m: α} {f: α -> α} {t: ℕ} (h: f m = m): apply_iterated f m t = m := by
  unfold apply_iterated
  apply Function.iterate_fixed h

@[simp]
theorem apply_iterated_zero {α: Type u} {m: α} {f: α -> α}: apply_iterated f m 0 = m := by
  simp [apply_iterated]

theorem apply_iterated_succ_apply' {α: Type u} {m: α} {f: α -> α}: apply_iterated f m (n+1) = f (apply_iterated f m n) := by
  simp [apply_iterated, Function.iterate_succ_apply']

lemma f_not_inj (h: Fintype M) (f: ℕ → M): ∃ b, ∃ a < b, b ≤ h.card ∧ f a = f b := by
  set n := Fintype.card M + 1 with nh

  let f' : Fin n → M := fun i => f i.val
  have : ¬Function.Injective f' := by
    have x := Fintype.card_le_of_injective f'
    simp_all [n]
  -- So f' is not injective ⇒ ∃ i ≠ j, f' i = f' j
  simp only [Function.Injective] at this
  push_neg at this
  obtain ⟨i, j, hne, heq⟩ := this
  wlog hij : i < j generalizing i j
  · exact this j i (Eq.symm hne) (Ne.symm heq) (lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq))
  use j.val
  use i.val
  constructor
  · exact hij
  constructor
  · omega
  · exact hne

lemma apply_iterated_mod {M} (h: Fintype M) (f: M -> M) (m:M): ∃ a b, a + (b - 1) < h.card ∧ b > 0 ∧ ∀ k, (apply_iterated f m) k = (apply_iterated f m) (k' k a b) := by
  have ⟨ b, a, h ⟩  := f_not_inj h (apply_iterated f m)
  set g := apply_iterated f m
  use a
  set bb := b - a

  have m1 (i k: ℕ): g (a + i) = g (a + i + bb) := by
    induction i
    case zero => simp [h, bb, Nat.add_sub_cancel' (Nat.le_of_lt h.1)]

    case succ n ih =>
      simp [g, apply_iterated] at ih

      have x1: a + (n + 1) = 1 + (a + n) := by omega
      have x2: a + (n + 1) + bb = 1 + (a + n + bb) := by omega

      rw [x2, x1]
      unfold g
      simp [apply_iterated]
      rw [Function.iterate_add]
      conv =>
        pattern f^[1 + (a + n + bb)] m
        rw [Function.iterate_add]
      simp [ih]

  have m1 (i k: ℕ) (h: i ≥ a): g i = g (i + bb * k) := by
    induction k generalizing i
    case zero => simp [h]

    case succ n ih =>
      have ⟨ s, sh ⟩ := Nat.exists_eq_add_of_le h
      rw [sh]
      rw [Nat.mul_add]
      rw [ih (a + s) (by omega)]
      have y: a + s + bb * n = a + (s + bb * n) := by omega
      rw [y]
      rw [m1]
      apply congrArg
      omega
      exact s

  use bb
  constructor
  · omega

  unfold k'
  constructor
  · omega
  intro k

  by_cases c: k ≤ a
  · simp [c]
  simp only [c, ↓reduceIte]

  simp [Nat.mod_def]
  simp at c
  set x := (k - a) / bb

  have xx: a + (k - a - bb * x) ≥ a := by omega

  --have xx1: (k - a - bb * x ≥ 0) := sorry
  have xx2: k - a ≥ bb * x := by
    unfold x
    have := Nat.mul_le_of_le_div bb ((k-a)/bb) (k-a) (le_refl _)
    conv =>
      pattern bb * _
      rw [Nat.mul_comm]
    simp_all

  conv =>
    arg 2
    rw [m1 _ x xx]
  apply congrArg
  omega




def repeating_function_of_iterate_fin_type { M } (h: Fintype M) { f: M → M } (m: M): RepeatingFunction (apply_iterated f m) := {
  k := h.card
  inv := by
    ext x
    constructor
    · intro h
      simp at h
      rcases h with ⟨y, hy⟩
      simp
      have ⟨ a, b, hf ⟩ := apply_iterated_mod h f m
      use k' y a b
      constructor
      · have bounded := k'_bounded y a b (by simp [hf])
        omega

      simp [←hy, hf.2.2 y]

    · intro h
      aesop
}

def repeating_function_of_composition { α β } { g: α → β } { f: ℕ → α } (h: RepeatingFunction f): RepeatingFunction (g ∘ f) := {
  k := h.k
  inv := by rw [image_comp, image_comp, h.inv]
}


lemma repeating_function_forall {α} { f: ℕ → α } (h: RepeatingFunction f) (p: α → Prop): (∀ i < h.k, p (f i)) ↔ (∀ i, p (f i)) := by
  have x := h.inv
  constructor
  · intro h1
    intro k
    have : f k ∈ f '' univ := mem_image_of_mem f (mem_univ k)
    rw [x] at this
    obtain ⟨k', hk', eqfk⟩ := this
    rw [←eqfk]
    exact h1 k' hk'

  · intro h1
    intro k
    intro h2
    exact (h1 k)


lemma find_some_bounded_idx_eq_find_some_idx_of_repeating_function { α } { f: ℕ → Option α } (h: RepeatingFunction f): find_some_bounded_idx f h.k = find_some_idx f := by
  cases c: find_some_bounded_idx f h.k
  case some val =>
    simp [find_some_bounded_idx_eq_some_iff] at c
    apply Eq.symm
    simp [find_some_idx_eq_some_iff]
    simp [c]
    exact c.2.2

  case none =>
    simp [find_some_bounded_eq_none_iff] at c
    apply Eq.symm
    rw [find_some_idx_eq_none_iff]
    simp_all [repeating_function_forall h (fun val => val = none)]

lemma find_some_bounded_eq_find_some_of_repeating_function { α } { f: ℕ → Option α } (h: RepeatingFunction f): find_some_bounded f h.k = find_some f := by
  simp [find_some_bounded, find_some, find_some_bounded_idx_eq_find_some_idx_of_repeating_function]
