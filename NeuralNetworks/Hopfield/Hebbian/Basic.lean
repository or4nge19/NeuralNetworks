/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Matteo Cipollina
-/

import NeuralNetworks.Hopfield.Basic
import NeuralNetworks.Hopfield.Energy
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Infix

namespace HopfieldState

open SpinState

variable {n : ℕ}

section HebbianConstruction

open UpdateSeq

/-!
# 4. A Classical Hebbian-Rule Construction

We now add a **concrete** Hopfield network construction for a set of patterns:
W = ∑_{p in P} p pᵀ (minus the diagonal) θᵢ = 0 (for simplicity)
and show that each stored pattern is indeed a fixed point.
-/

/--
The naive Hebbian outer-product rule, summing `p_i p_j` for each stored pattern `p`.
We then explicitly zero out the diagonal afterwards (classical Hopfield assumption).
-/
def hebbWeights {n : ℕ} (P : Finset (HopfieldState n)) : Matrix (Fin n) (Fin n) ℝ :=
  let raw : Matrix (Fin n) (Fin n) ℝ :=
    ∑ p ∈ P, fun i j => (p i).toReal * (p j).toReal
  fun i j =>
    if i = j then 0 else raw i j  -- zero out the diagonal

lemma hebbWeights_sym {n : ℕ} (P : Finset (HopfieldState n)) :
    (hebbWeights P).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  unfold hebbWeights
  dsimp only [RCLike.star_def]
  by_cases h : i = j
  · -- When i = j, both sides are 0
    simp [h]
  · -- When i ≠ j, show raw weights are symmetric
    simp only [if_neg h, if_neg (Ne.symm h)]
    -- Show that the raw weights are symmetric before applying the diagonal zeros
    -- When i ≠ j, we need to show the sum at (i,j) equals the sum at (j,i)
    simp only [conj_trivial]
    rw [@Matrix.sum_apply]
    simp only [Matrix.sum_apply]
    -- For the goal, we just need to use commutativity of multiplication
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_comm]

-- Define a sign function to match the spin state corresponding to a real number
noncomputable def SpinState.sign (x : ℝ) : SpinState :=
  if x ≥ 0 then SpinState.up else SpinState.down

lemma hebbWeights_diagZero {n : ℕ} (P : Finset (HopfieldState n)) :
    (hebbWeights P).diag = 0 := by
  ext i
  unfold Matrix.diag
  unfold hebbWeights
  simp only [if_pos (Eq.refl i)]
  simp -- This evaluates to -1 directly from SpinState.toReal definition

/--
A simple "Hebbian" HopfieldNetwork with thresholds=0 and weights given by `hebbWeights`.
-/
def hebbianHopfield (P : Finset (HopfieldState n)) : HopfieldNetwork n where
  weights := {
    val := hebbWeights P,
    property := ⟨hebbWeights_sym P, hebbWeights_diagZero P⟩
  }
  thresholds := fun _ => 0

/-- When in a branch with a contradictory spin state assumption, use this to derive False --/
lemma spin_state_contradiction {s : SpinState} (h_up : s = SpinState.up) (h_down : s = SpinState.down) : False := by
  have : SpinState.up = SpinState.down := by
    rw [←h_up, h_down]
  exact SpinState.noConfusion this

/-- The square of any spin value is 1 --/
lemma spin_square_one {s : SpinState} : (s.toReal)^2 = 1 := by
  cases s <;> simp [SpinState.toReal]

/-- Count the number of indices not equal to i --/
lemma sum_filter_ne_card {n : ℕ} (i : Fin n) :
  (Finset.filter (fun j => j ≠ i) Finset.univ).card = n - 1 := by
  -- The cardinality of the universal set is n
  have h_univ : (Finset.univ : Finset (Fin n)).card = n := by
    exact Finset.card_fin n

  -- The complement of {i} has cardinality n-1
  have h_single : (Finset.filter (fun j => j = i) Finset.univ).card = 1 := by
    simp [Finset.filter_eq', Finset.card_singleton]

  -- The two sets form a partition of the universe
  have h_partition :
    Finset.filter (fun j => j ≠ i) Finset.univ ∪ Finset.filter (fun j => j = i) Finset.univ = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    apply Iff.intro
    · intro _; exact trivial
    · intro _; exact ne_or_eq j i

  -- The two sets are disjoint
  have h_disj : Disjoint (Finset.filter (fun j => j ≠ i) Finset.univ) (Finset.filter (fun j => j = i) Finset.univ) := by
    apply Finset.disjoint_iff_ne.mpr
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    subst hy hxy
    simp_all only [Finset.card_univ, Fintype.card_fin, ne_eq, not_true_eq_false]

  -- Apply the cardinality of a union of disjoint sets
  have h_card_union :
    (Finset.filter (fun j => j ≠ i) Finset.univ ∪ Finset.filter (fun j => j = i) Finset.univ).card =
    (Finset.filter (fun j => j ≠ i) Finset.univ).card + (Finset.filter (fun j => j = i) Finset.univ).card := by
    apply Finset.card_union_of_disjoint h_disj

  -- Combine all the facts
  rw [←h_partition] at h_univ
  rw [h_card_union] at h_univ
  rw [h_single] at h_univ
  exact Nat.eq_sub_of_add_eq h_univ
