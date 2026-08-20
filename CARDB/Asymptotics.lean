/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Discrete dominance and explicit bounds

The discrete topology contributes `2^(2^N - N)` bases. Every other
topology on an `N`-element set with `N ≥ 2` has at most `3 * 2^(N-2)`
open sets, and there are at most `2^(N * (N - 1))` topologies, so

```
2^(2^N - N) ≤ #(N) ≤ 2^(2^N - N) + 2^(N * (N - 1) + 3 * 2^(N-2)).
```

The relative error is at most `2^(N^2 - 2^(N-2))`, hence
`#(N) ∼ 2^(2^N - N)`. For `N ≥ 10` the error term is at most the
discrete term, so `#(N) ≤ 2 * 2^(2^N - N)`.
-/

open Set TopologicalSpace

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma isOpen_bot (U : Set α) : @IsOpen α ⊥ U := trivial

lemma opensOf_bot : opensOf (⊥ : TopologicalSpace α) = univ := by
  ext U
  exact ⟨fun _ => mem_univ U, fun _ => isOpen_bot U⟩

lemma ncard_opensOf_bot :
    ncard (opensOf (⊥ : TopologicalSpace α)) = 2 ^ Fintype.card α := by
  rw [opensOf_bot, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_set]

lemma minimalOpen_bot (x : α) :
    minimalOpen (⊥ : TopologicalSpace α) x = {x} :=
  @IsOpen.nhdsKer_eq α ⊥ {x} (isOpen_bot {x})

lemma minimalBasis_bot :
    minimalBasis (⊥ : TopologicalSpace α) = range (singleton : α → Set α) := by
  ext U
  simp [minimalBasis, minimalOpen_bot, singleton]

omit [Fintype α] [DecidableEq α] in
lemma singleton_set_injective : Function.Injective (singleton : α → Set α) :=
  fun x y h => by
    have : x ∈ ({y} : Set α) := (Set.ext_iff.mp h x).1 (mem_singleton x)
    simpa using this

lemma ncard_minimalBasis_bot :
    ncard (minimalBasis (⊥ : TopologicalSpace α)) = Fintype.card α := by
  rw [minimalBasis_bot, ncard_range_of_injective singleton_set_injective,
    Nat.card_eq_fintype_card]

theorem card_fiber_discrete :
    Fintype.card (Fiber (⊥ : TopologicalSpace α)) =
      2 ^ (2 ^ Fintype.card α - Fintype.card α) := by
  rw [card_fiber, ncard_opensOf_bot, ncard_minimalBasis_bot]

theorem card_valid_bases_ge_discrete :
    2 ^ (2 ^ Fintype.card α - Fintype.card α) ≤ Fintype.card (ValidBasis α) := by
  rw [card_valid_bases_sum_fiber, ← card_fiber_discrete]
  exact Finset.single_le_sum (f := fun τ : TopologicalSpace α => Fintype.card (Fiber τ))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⊥ : TopologicalSpace α))

lemma exists_specializes_of_ne_bot {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    ∃ x y : α, x ≠ y ∧ y ∈ minimalOpen t x := by
  have hnd : ¬@DiscreteTopology α t :=
    fun h => ht (DiscreteTopology.eq_bot (α := α) (t := t))
  have : ∃ x, ¬t.IsOpen {x} := by
    contrapose! hnd
    exact ⟨eq_bot_of_singletons_open hnd⟩
  obtain ⟨x, hx⟩ := this
  have hne : minimalOpen t x ≠ {x} := by
    intro h
    exact hx ((nhdsKer_eq_iff_isOpen (s := ({x} : Set α))).mp h)
  obtain ⟨y, hy, hxy⟩ :=
    exists_of_ssubset ((subset_nhdsKer (s := ({x} : Set α))).ssubset_of_ne hne.symm)
  exact ⟨x, y, Ne.symm (by simpa using hxy), hy⟩

variable {x y : α}

lemma card_pair (hne : x ≠ y) :
    Fintype.card {z : α // z = x ∨ z = y} = 2 := by
  refine (Fintype.card_congr
    { toFun := fun z : {z : α // z = x ∨ z = y} => decide (z.1 = x)
      invFun := fun b => if b then ⟨x, Or.inl rfl⟩ else ⟨y, Or.inr rfl⟩
      left_inv := fun z => by
        apply Subtype.ext
        rcases z.2 with h | h
        · simp [h]
        · have : decide (y = x) = false := decide_eq_false (Ne.symm hne)
          simp [h, this]
      right_inv := fun b => by
        cases b
        · simp [Ne.symm hne]
        · simp }).trans
    (by decide : Fintype.card Bool = 2)

lemma card_rest (hne : x ≠ y) :
    Fintype.card {z : α // z ≠ x ∧ z ≠ y} = Fintype.card α - 2 := by
  have := Fintype.card_subtype_compl (fun z : α => z = x ∨ z = y)
  have heq : {z : α // ¬(z = x ∨ z = y)} ≃ {z : α // z ≠ x ∧ z ≠ y} :=
    { toFun := fun z => ⟨z.1, by simpa [not_or] using z.2⟩
      invFun := fun z => ⟨z.1, by simpa [not_or] using z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr heq, this, card_pair hne]

/-- Encode a constrained open by its trace on `α \ {x,y}` and the
    three-way status of `{x,y}`. -/
noncomputable def packConstrained (a b : α) (hne : a ≠ b)
    (U : {U : Set α // a ∈ U → b ∈ U}) :
    Set {z : α // z ≠ a ∧ z ≠ b} × Fin 3 := by
  classical
  exact ({z | z.1 ∈ U.1},
    if a ∈ U.1 then ⟨2, by decide⟩ else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩)

lemma packConstrained_injective (a b : α) (hne : a ≠ b) :
    Function.Injective (packConstrained a b hne) := by
  classical
  intro U V h
  apply Subtype.ext
  have hrest := congrArg Prod.fst h
  have hstat := congrArg Prod.snd h
  ext z
  by_cases hza : z = a
  · rw [hza]
    have : (if a ∈ U.1 then (⟨2, by decide⟩ : Fin 3) else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) =
        (if a ∈ V.1 then ⟨2, by decide⟩ else if b ∈ V.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) := by
      simpa [packConstrained] using hstat
    split_ifs at this <;> simp_all
  · by_cases hzb : z = b
    · rw [hzb]
      have : (if a ∈ U.1 then (⟨2, by decide⟩ : Fin 3) else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) =
          (if a ∈ V.1 then ⟨2, by decide⟩ else if b ∈ V.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩) := by
        simpa [packConstrained] using hstat
      split_ifs at this <;> try simp_all
      · exact iff_of_true (U.2 (by simp_all)) (V.2 (by simp_all))
    · have := Set.ext_iff.mp hrest ⟨z, ⟨hza, hzb⟩⟩
      simpa [packConstrained] using this

lemma card_constrained (hne : x ≠ y) :
    ncard {U : Set α | x ∈ U → y ∈ U} ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  classical
  haveI : DecidablePred (fun U : Set α => x ∈ U → y ∈ U) := fun _ => inferInstance
  haveI : Fintype {U : Set α // x ∈ U → y ∈ U} := Subtype.fintype _
  have hle := Fintype.card_le_of_injective (packConstrained x y hne)
    (packConstrained_injective x y hne)
  have hcard : ncard {U : Set α | x ∈ U → y ∈ U} =
      Fintype.card {U : Set α // x ∈ U → y ∈ U} := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard]
  refine hle.trans ?_
  rw [Fintype.card_prod, Fintype.card_set, Fintype.card_fin, card_rest hne, mul_comm]

lemma ncard_opens_of_specialization {t : TopologicalSpace α}
    (hne : x ≠ y) (hy : y ∈ minimalOpen t x) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  have hsub : opensOf t ⊆ {U : Set α | x ∈ U → y ∈ U} := by
    intro U hU hxU
    exact minimalOpen_subset_of_isOpen t hU hxU hy
  exact (ncard_le_ncard hsub).trans (card_constrained hne)

lemma ncard_opensOf_le_of_ne_bot {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by
  obtain ⟨x, y, hne, hy⟩ := exists_specializes_of_ne_bot ht
  exact ncard_opens_of_specialization hne hy

def specSet (t : TopologicalSpace α) : Set (α × α) :=
  {p | @Specializes α t p.1 p.2}

omit [DecidableEq α] in
lemma specSet_injective :
    Function.Injective (specSet : TopologicalSpace α → Set (α × α)) := by
  intro t₁ t₂ h
  have hmin : ∀ z, minimalOpen t₁ z = minimalOpen t₂ z := by
    intro z
    ext w
    have : @Specializes α t₁ w z ↔ @Specializes α t₂ w z := by
      simpa [specSet] using (Set.ext_iff.mp h (w, z))
    simpa [minimalOpen, mem_nhdsKer_singleton] using this
  have : minimalBasis t₁ = minimalBasis t₂ := by
    ext U
    simp [minimalBasis, hmin]
  exact (generateFrom_minimalBasis t₁).symm.trans
    ((congrArg generateFrom this).trans (generateFrom_minimalBasis t₂))

/-- Off-diagonal specialization pairs. The diagonal is always present. -/
def specOffDiag (t : TopologicalSpace α) : Set {p : α × α // p.1 ≠ p.2} :=
  {p | @Specializes α t p.1.1 p.1.2}

lemma specOffDiag_injective :
    Function.Injective (specOffDiag : TopologicalSpace α → Set {p : α × α // p.1 ≠ p.2}) := by
  intro t₁ t₂ h
  refine specSet_injective ?_
  ext p
  obtain ⟨x, y⟩ := p
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_true (@specializes_rfl α t₁ x) (@specializes_rfl α t₂ x)
  · simpa [specSet, specOffDiag] using (Set.ext_iff.mp h ⟨(x, y), hxy⟩)

lemma card_off_diag :
    Fintype.card {p : α × α // p.1 ≠ p.2} =
      Fintype.card α * (Fintype.card α - 1) := by
  have hdiag : Fintype.card {p : α × α // p.1 = p.2} = Fintype.card α :=
    Fintype.card_congr
      { toFun := fun p : {p : α × α // p.1 = p.2} => p.1.1
        invFun := fun x => ⟨(x, x), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.2)
        right_inv := fun _ => rfl }
  have hne : {p : α × α // p.1 ≠ p.2} ≃ {p : α × α // ¬(p.1 = p.2)} :=
    Equiv.subtypeEquivRight fun _ => Iff.rfl
  rw [Fintype.card_congr hne, Fintype.card_subtype_compl (fun p : α × α => p.1 = p.2),
    Fintype.card_prod, hdiag]
  exact (Nat.mul_sub_one (Fintype.card α) (Fintype.card α)).symm

lemma card_topologies_le :
    Fintype.card (TopologicalSpace α) ≤
      2 ^ (Fintype.card α * (Fintype.card α - 1)) := by
  have h := Fintype.card_le_of_injective
    (specOffDiag : TopologicalSpace α → Set {p : α × α // p.1 ≠ p.2})
    specOffDiag_injective
  rwa [Fintype.card_set, card_off_diag] at h

lemma card_fiber_le_of_ne_bot {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    Fintype.card (Fiber t) ≤ 2 ^ (3 * 2 ^ (Fintype.card α - 2)) := by
  rw [card_fiber]
  exact Nat.pow_le_pow_right (by decide : 0 < 2)
    ((Nat.sub_le _ _).trans (ncard_opensOf_le_of_ne_bot ht))

theorem card_valid_bases_bounds (hN : 2 ≤ Fintype.card α) :
    2 ^ (2 ^ Fintype.card α - Fintype.card α) ≤ Fintype.card (ValidBasis α) ∧
    Fintype.card (ValidBasis α) ≤
      2 ^ (2 ^ Fintype.card α - Fintype.card α) +
        2 ^ (Fintype.card α * (Fintype.card α - 1) + 3 * 2 ^ (Fintype.card α - 2)) := by
  refine ⟨card_valid_bases_ge_discrete, ?_⟩
  rw [card_valid_bases_sum_fiber]
  have hsplit :
      ∑ τ : TopologicalSpace α, Fintype.card (Fiber τ) =
        Fintype.card (Fiber (⊥ : TopologicalSpace α)) +
          ∑ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
            Fintype.card (Fiber τ) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun τ : TopologicalSpace α => τ = ⊥)]
    simp [Finset.filter_eq']
  rw [hsplit, card_fiber_discrete]
  have hsum :
      ∑ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
          Fintype.card (Fiber τ) ≤
        (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card *
          2 ^ (3 * 2 ^ (Fintype.card α - 2)) := by
    have hle' : ∀ τ ∈ Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥),
        Fintype.card (Fiber τ) ≤ 2 ^ (3 * 2 ^ (Fintype.card α - 2)) :=
      fun τ hτ => card_fiber_le_of_ne_bot (Finset.mem_filter.mp hτ).2
    have := Finset.sum_le_sum hle'
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard :
      (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card ≤
        2 ^ (Fintype.card α * (Fintype.card α - 1)) :=
    (Finset.card_filter_le _ _).trans (by simpa using card_topologies_le)
  have : (Finset.univ.filter (fun τ : TopologicalSpace α => τ ≠ ⊥)).card *
      2 ^ (3 * 2 ^ (Fintype.card α - 2)) ≤
        2 ^ (Fintype.card α * (Fintype.card α - 1) + 3 * 2 ^ (Fintype.card α - 2)) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hcard
  exact Nat.add_le_add_left (hsum.trans this) _

lemma add_succ_sq (k : ℕ) : (k + 1) ^ 2 + (k + 1) = k ^ 2 + k + 2 * k + 2 := by
  ring

lemma two_mul_pow (a : ℕ) : 2 ^ a * 2 = 2 * 2 ^ a := by
  rw [mul_comm]

lemma le_two_pow_sub_three (k : ℕ) (hk : 10 ≤ k) : k + 1 ≤ 2 ^ (k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 3 ≤ k := le_trans (by decide : 3 ≤ 10) hk
    have h2 : 2 ^ (k + 1 - 3) = 2 * 2 ^ (k - 3) := by
      rw [show k + 1 - 3 = k - 3 + 1 by omega, pow_succ, two_mul_pow]
    rw [h2]
    have : k + 2 ≤ 2 * (k + 1) := by nlinarith
    exact this.trans (Nat.mul_le_mul_left 2 ih)

lemma two_pow_poly_le (n : ℕ) (hn : 10 ≤ n) : n ^ 2 + n ≤ 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : 2 ≤ k := le_trans (by decide : 2 ≤ 10) hk
    have hpow : 2 ^ (k + 1 - 2) = 2 * 2 ^ (k - 2) := by
      rw [show k + 1 - 2 = k - 2 + 1 by omega, pow_succ, two_mul_pow]
    rw [add_succ_sq, hpow]
    have hsmall : 2 * k + 2 ≤ 2 ^ (k - 2) := by
      have hk1 : k + 1 ≤ 2 ^ (k - 3) := le_two_pow_sub_three k hk
      have : 3 ≤ k := le_trans (by decide : 3 ≤ 10) hk
      have h2 : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
        rw [show k - 2 = k - 3 + 1 by omega, pow_succ, two_mul_pow]
      have hmul : 2 * (k + 1) ≤ 2 * 2 ^ (k - 3) := Nat.mul_le_mul_left 2 hk1
      have : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [this] at hmul
      rwa [h2]
    have hsum := Nat.add_le_add ih hsmall
    have : 2 ^ (k - 2) + 2 ^ (k - 2) = 2 * 2 ^ (k - 2) := by
      rw [two_mul]
    exact hsum.trans_eq this

theorem card_valid_bases_dominated (hN : 10 ≤ Fintype.card α) :
    Fintype.card (ValidBasis α) ≤
      2 * 2 ^ (2 ^ Fintype.card α - Fintype.card α) := by
  have h2 : 2 ≤ Fintype.card α := le_trans (by decide : 2 ≤ 10) hN
  obtain ⟨_, hhi⟩ := card_valid_bases_bounds h2
  refine hhi.trans ?_
  set N := Fintype.card α
  have hgap : N * (N - 1) + 3 * 2 ^ (N - 2) ≤ 2 ^ N - N := by
    have hpoly := two_pow_poly_le N hN
    have hsq : N * (N - 1) + N = N ^ 2 := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_self N), sq]
    have : N * (N - 1) + 3 * 2 ^ (N - 2) + N ≤ 2 ^ (N - 2) + 3 * 2 ^ (N - 2) := by
      linarith [hsq]
    have hsum : 2 ^ (N - 2) + 3 * 2 ^ (N - 2) = 4 * 2 ^ (N - 2) := by
      ring
    have h4 : 4 * 2 ^ (N - 2) = 2 ^ N := by
      have : 2 ≤ N := h2
      have hfour : (4 : ℕ) = 2 ^ 2 := by decide
      rw [hfour, ← pow_add, show 2 + (N - 2) = N by omega]
    exact Nat.le_sub_of_add_le (this.trans_eq (hsum.trans h4))
  have herr : 2 ^ (N * (N - 1) + 3 * 2 ^ (N - 2)) ≤ 2 ^ (2 ^ N - N) :=
    Nat.pow_le_pow_right (by decide) hgap
  have : 2 ^ (2 ^ N - N) + 2 ^ (N * (N - 1) + 3 * 2 ^ (N - 2)) ≤
      2 ^ (2 ^ N - N) + 2 ^ (2 ^ N - N) :=
    Nat.add_le_add_left herr _
  have h2D : 2 ^ (2 ^ N - N) + 2 ^ (2 ^ N - N) = 2 * 2 ^ (2 ^ N - N) := by
    rw [two_mul]
  exact this.trans_eq h2D

open Filter Topology

lemma remainder_exp_add_n_le (n : ℕ) (hn : 10 ≤ n) :
    n * (n - 1) + 3 * 2 ^ (n - 2) + n ≤ 2 ^ n - n := by
  have hpoly := two_pow_poly_le n hn
  have hsq : n * (n - 1) + n = n ^ 2 := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_self n), sq]
  have h4 : 2 ^ (n - 2) + 3 * 2 ^ (n - 2) = 2 ^ n := by
    have : 2 ^ (n - 2) + 3 * 2 ^ (n - 2) = 4 * 2 ^ (n - 2) := by ring
    have hfour : (4 : ℕ) = 2 ^ 2 := by decide
    rw [this, hfour, ← pow_add, show 2 + (n - 2) = n by omega]
  have : n ^ 2 + 3 * 2 ^ (n - 2) + n ≤ 2 ^ n := by
    have := Nat.add_le_add hpoly (Nat.le_refl (3 * 2 ^ (n - 2)))
    convert this using 1
    · ring
    · exact h4.symm
  have hleft : n * (n - 1) + 3 * 2 ^ (n - 2) + n + n = n ^ 2 + 3 * 2 ^ (n - 2) + n := by
    rw [← hsq]; ac_rfl
  have : n * (n - 1) + 3 * 2 ^ (n - 2) + n + n ≤ 2 ^ n := by
    rwa [hleft]
  exact Nat.le_sub_of_add_le this

lemma card_valid_bases_ratio_le_one_add_half_pow (n : ℕ) (hn : 10 ≤ n) :
    (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n) ≤
      1 + (1 / 2 : ℝ) ^ n := by
  have h2 : 2 ≤ n := le_trans (by decide : 2 ≤ 10) hn
  have hN : 2 ≤ Fintype.card (Fin n) := by simpa using h2
  obtain ⟨_, hbound⟩ := card_valid_bases_bounds (α := Fin n) hN
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n - n) := pow_pos (by norm_num) _
  have hC :
      (Fintype.card (ValidBasis (Fin n)) : ℝ) ≤
        (2 : ℝ) ^ (2 ^ n - n) + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hbound
    simpa [Nat.cast_add, Nat.cast_pow, Fintype.card_fin] using this
  have hdiv := div_le_div_of_nonneg_right hC hDpos.le
  have hsplit :
      ((2 : ℝ) ^ (2 ^ n - n) + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2))) /
          (2 : ℝ) ^ (2 ^ n - n) =
        1 + (2 : ℝ) ^ (n * (n - 1) + 3 * 2 ^ (n - 2)) / (2 : ℝ) ^ (2 ^ n - n) := by
    field_simp [hDpos.ne']
  refine hdiv.trans ((le_of_eq hsplit).trans (add_le_add le_rfl ?_))
  set a := n * (n - 1) + 3 * 2 ^ (n - 2)
  set b := 2 ^ n - n
  have hab : a + n ≤ b := remainder_exp_add_n_le n hn
  have hmon :
      (2 : ℝ) ^ a / (2 : ℝ) ^ b ≤ (2 : ℝ) ^ a / (2 : ℝ) ^ (a + n) :=
    div_le_div_of_nonneg_left (pow_nonneg (by norm_num) _)
      (pow_pos (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hab)
  have hsimp : (2 : ℝ) ^ a / (2 : ℝ) ^ (a + n) = (1 / 2 : ℝ) ^ n := by
    rw [pow_add (2 : ℝ) a n, div_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      one_div, inv_pow]
  exact hmon.trans_eq hsimp

omit [Fintype α] [DecidableEq α] in
/-- `#(N) ∼ 2^(2^N - N)`: the ratio tends to `1`. -/
theorem card_valid_bases_asymptotic :
    Tendsto (fun n : ℕ =>
      (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n))
      atTop (nhds (1 : ℝ)) := by
  have hge : ∀ n,
      1 ≤ (Fintype.card (ValidBasis (Fin n)) : ℝ) / (2 : ℝ) ^ (2 ^ n - n) := by
    intro n
    refine (one_le_div (pow_pos (by norm_num : (0 : ℝ) < 2) (2 ^ n - n))).mpr ?_
    have h := card_valid_bases_ge_discrete (α := Fin n)
    have := (Nat.cast_le (α := ℝ)).mpr (by simpa using h)
    simpa [Nat.cast_pow] using this
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hupper : Tendsto (fun n : ℕ => (1 : ℝ) + (1 / 2 : ℝ) ^ n) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) hupper
    (Eventually.of_forall hge)
    (eventually_atTop.2 ⟨10, fun n hn => card_valid_bases_ratio_le_one_add_half_pow n hn⟩)
