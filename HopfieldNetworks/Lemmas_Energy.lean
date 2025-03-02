import HopfieldNetworks.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-!
# Hopfield Networks Formalization (Energy Function Properties)

This file builds upon `HopfieldNetworks.Basic` to formalize properties
of the Hopfield network energy function, particularly its decrease
under asynchronous updates.  We aim to show that the energy function
acts as a Lyapunov function for the network dynamics.
-/

open Matrix
open BigOperators

namespace HopfieldState

open SpinState
open Finset BigOperators

variable {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n)

/--
Helper function to compute the change in energy when updating neuron `i`.
-/
noncomputable
def energyDiff (i : Fin n) : ℝ :=
  energy net (updateState net x i) - energy net x

/-- Sum over universal set equals sum over all finite indices.
    Essential for Hopfield network energy calculations where we sum over all neurons. -/
@[simp]
lemma Finset.sum_univ {α : Type*} {β : Type*} [AddCommMonoid β] [Fintype α]
  (f : α → β) :
  ∑ x ∈ univ, f x = ∑ x, f x := by
  apply Finset.sum_congr
  · exact Finset.eq_univ_iff_forall.2 (fun x => Finset.mem_univ x)
  · intro x _
    rfl

lemma energyDiff_eq (i : Fin n) :
    energyDiff net x i = - ((localField net x i) * (updateState net x i i).toReal) + ((localField net x i) * (x i).toReal) := by
  let x' := updateState net x i
  calc
    energyDiff net x i = energy net x' - energy net x := by rfl
    _ = ((-0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x')) - (∑ j, net.thresholds j * (toRealVector x' j))) -
      ((-0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x)) - (∑ j, net.thresholds j * (toRealVector x j))) := by simp [energy, energy', energy_eq_energy']
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - (∑ j, net.thresholds j * (toRealVector x' j)) + (∑ j, net.thresholds j * (toRealVector x j)) := by ring
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - (net.thresholds i * (toRealVector x' i) + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x' j)) + (net.thresholds i * (toRealVector x i) + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x j)) := by
      have h1 : ∑ j, net.thresholds j * (toRealVector x' j) =
               net.thresholds i * (toRealVector x' i) + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x' j) := by
        rw [@Fin.sum_univ_def]
        simp [toRealVector_apply]
        ring_nf
        exact rfl
      have h2 : ∑ j, net.thresholds j * (toRealVector x j) =
               net.thresholds i * (toRealVector x i) + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x j) := by
        rw [@Fin.sum_univ_def]
        simp [toRealVector_apply]
        exact rfl
      rw [h1, h2]
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - net.thresholds i * (toRealVector x' i) + net.thresholds i * (toRealVector x i) - ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x' j) + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (toRealVector x j) := by ring
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - net.thresholds i * (x' i).toReal + net.thresholds i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x' j).toReal + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x j).toReal := by simp
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - net.thresholds i * (x' i).toReal + net.thresholds i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x' j).toReal + ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x j).toReal := by
      have h1 : ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x' j).toReal = ∑ j ∈ Finset.univ.erase i, net.thresholds j * (x j).toReal := by
        apply Finset.sum_congr
        · rfl -- Sets are equal
        · intro j hj
          have h2 : x' j = x j := by
            have j_neq_i : j ≠ i := by exact ne_of_mem_erase hj
            apply Function.update_of_ne j_neq_i
          simp only [mul_eq_mul_left_iff]
          rw [h2]
          exact mul_eq_mul_left_iff.mp rfl
      rw [h1]
    _ = -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') + 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) - net.thresholds i * (x' i).toReal + net.thresholds i * (x i).toReal := by simp only [neg_mul, mem_univ, sum_erase_eq_sub]; ring_nf; sorry
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - net.thresholds i * (x' i).toReal + net.thresholds i * (x i).toReal := by
      simp
      have h_bil : -0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x') (toRealVector x') = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) := by
        rw [Matrix.toBilin'_apply]
        exact?

      have h_bil2 : 0.5 * Matrix.toBilin' (weightsMatrix net) (toRealVector x) (toRealVector x) = 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) := by
        rw [Matrix.toBilin'_apply]
        exact?
      rw [h_bil, h_bil2]
      ring_nf
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - (localField net x i + ((weightsMatrix net) *ᵥ (toRealVector x)) i) * (x' i).toReal + (localField net x i + ((weightsMatrix net) *ᵥ (toRealVector x)) i) * (x i).toReal := by
      simp [localField, Matrix.mulVec]
      have h_field : net.thresholds i = localField net x i + ((weightsMatrix net) *ᵥ (toRealVector x)) i - ((weightsMatrix net) *ᵥ (toRealVector x)) i := by
        simp [localField]
        rw [add_sub_cancel]
      rw [h_field]
      ring_nf
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - (localField net x i * (x' i).toReal + ((weightsMatrix net *ᵥ toRealVector x) i) * (x' i).toReal) + (localField net x i * (x i).toReal + ((weightsMatrix net *ᵥ toRealVector x) i) * (x i).toReal) := by ring
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ((weightsMatrix net *ᵥ toRealVector x) i) * (x' i).toReal + ((weightsMatrix net *ᵥ toRealVector x) i) * (x i).toReal := by ring
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j, (weightsMatrix net j i) * toRealVector x j * (x' i).toReal + ∑ j, (weightsMatrix net j i) * toRealVector x j * (x i).toReal := by
      simp only [Matrix.mulVec, PiLp.innerProductSpace]
      ring_nf
      simp only [one_div, toRealVector_apply]
      exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (toRealVector x j) * (x' i).toReal - (weightsMatrix net i i) * (toRealVector x i) * (x' i).toReal + ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (toRealVector x j) * (x i).toReal + (weightsMatrix net i i) * (toRealVector x i) * (x i).toReal := by
      simp only [neg_mul, toRealVector_apply, mem_univ, sum_erase_eq_sub]
      ring
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (toRealVector x j) * (x' i).toReal - 0 + ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (toRealVector x j) * (x i).toReal + 0 := by
      simp [weights_diag_zero]
      ring_nf
      exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * toRealVector x j * (x' i).toReal + ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * toRealVector x j * (x i).toReal := by ring
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (x j).toReal * (x' i).toReal + ∑ j ∈ Finset.univ.erase i, (weightsMatrix net j i) * (x j).toReal * (x i).toReal := by simp
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j ∈ Finset.univ.erase i, (weightsMatrix net i j) * (x j).toReal * (x' i).toReal + ∑ j ∈ Finset.univ.erase i, (weightsMatrix net i j) * (x j).toReal * (x i).toReal := by
      have h1 : ∀ (i j : Fin n), weightsMatrix net j i = weightsMatrix net i j := by
        intro i j
        have h2 := weights_symmetric net
        simp at h2
        exact rfl
      simp [h1]
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j , (weightsMatrix net i j) * (x j).toReal * (x' i).toReal + (weightsMatrix net i i) * (x i).toReal * (x' i).toReal + ∑ j , (weightsMatrix net i j) * (x j).toReal * (x i).toReal - (weightsMatrix net i i) * (x i).toReal * (x i).toReal := by
      simp only [neg_mul, mem_univ, sum_erase_eq_sub]
      ring
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ∑ j , (weightsMatrix net i j) * (x j).toReal * (x' i).toReal + 0 + ∑ j , (weightsMatrix net i j) * (x j).toReal * (x i).toReal - 0 := by
      simp [weights_diag_zero]
      ring_nf
      exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - (∑ j , (weightsMatrix net i j) * (x j).toReal) * (x' i).toReal + (∑ j , (weightsMatrix net i j) * (x j).toReal) * (x i).toReal := by ring_nf; simp only [one_div]; exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ((weightsMatrix net).mulVec (fun i => (x i).toReal) i) * (x' i).toReal + ((weightsMatrix net).mulVec (fun i => (x i).toReal) i) * (x i).toReal := by simp [Matrix.mulVec, PiLp.innerProductSpace]; exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - ((weightsMatrix net).mulVec (toRealVector x) i) * (x' i).toReal + ((weightsMatrix net).mulVec (toRealVector x) i) * (x i).toReal := by simp; exact rfl
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - (localField net x i + net.thresholds i) * (x' i).toReal + (localField net x i + net.thresholds i) * (x i).toReal := by simp [localField]
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal - localField net x i * (x' i).toReal + localField net x i * (x i).toReal + localField net x i * (x i).toReal - net.thresholds i * (x' i).toReal + net.thresholds i * (x i).toReal := by ring_nf;
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - localField net x i * (x' i).toReal + localField net x i * (x i).toReal - localField net x i * (x' i).toReal - net.thresholds i * (x' i).toReal + localField net x i * (x i).toReal + net.thresholds i * (x i).toReal := by ring_nf;
    _ = -0.5 * ((toRealVector x') ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x'))) + 0.5 * ((toRealVector x) ⬝ᵥ ((weightsMatrix net) *ᵥ (toRealVector x))) - ((∑ j, net.thresholds j * (toRealVector (Function.update x i (if 0 < localField net x i then SpinState.up else if localField net x i < 0 then SpinState.down else x i)) j)) - (∑ j, net.thresholds j * (toRealVector x j))) := by ring_nf; exact rfl
    _ = - localField net x i * (x' i).toReal + localField net x i * (x i).toReal := by simp only [neg_mul, toRealVector_apply]; ring_nf; exact rfl

lemma energyDiff_sign (i : Fin n) :
  (localField net x i > 0 → energyDiff net x i ≤ 0) ∧
  (localField net x i < 0 → energyDiff net x i ≤ 0) := by
  constructor
  · intro hlf
    have hx' := updateState net x i
    have hx'' := Function.update x i (if 0 < localField net x i then SpinState.up else if localField net x i < 0 then SpinState.down else x i)
    simp [energyDiff_eq]
    simp [updateState]
    split_ifs
    · simp [SpinState.up]
      have hspin : (SpinState.up).toReal = 1 := by simp
      have hlt : - (localField net x i * 1) + (localField net x i * (x i).toReal) ≤ 0 := by
        have hpos : (localField net x i) > 0 := by exact hlf
        simp [hpos]
        have hcomp : (x i).toReal ≤ 1 := by
          cases x i
          · simp
          · simp
        have hmul : (localField net x i) * (x i).toReal ≤ (localField net x i) * 1 := by gcongr
        linarith
      exact hlt
    · simp [SpinState.down]
      sorry
    · simp
      have hspin : (x i).toReal = (x i).toReal := by simp
      have hlt : - (localField net x i * (x i).toReal) + (localField net x i * (x i).toReal) ≤ 0 := by
        simp
      exact hlt
  · intro hlf
    have hx' := updateState net x i
    have hx'' := Function.update x i (if 0 < localField net x i then SpinState.up else if localField net x i < 0 then SpinState.down else x i)
    simp [energyDiff_eq]
    simp [updateState]
    split_ifs
    · simp [SpinState.up]
      sorry
    · simp [SpinState.down]
      have hspin : (SpinState.down).toReal = -1 := by simp
      have hlt : - (localField net x i * -1) + (localField net x i * (x i).toReal) ≤ 0 := by
        have hneg : (localField net x i) < 0 := by exact hlf
        simp [hneg]
        have hcomp : (x i).toReal ≥ -1 := by
          cases x i
          · simp
          · simp
        have hmul : (localField net x i) * (x i).toReal ≤ (localField net x i) * -1 := by gcongr
        linarith
      exact hlt
    · simp
      have hspin : (x i).toReal = (x i).toReal := by simp
      have hlt : - (localField net x i * (x i).toReal) + (localField net x i * (x i).toReal) ≤ 0 := by
        simp
      exact hlt

/--
The energy function is non-increasing under asynchronous updates. This is the core
Lyapunov function property.
-/
lemma energy_decrease (i : Fin n) :
  energy net (updateState net x i) ≤ energy net x := by
  have hx' := updateState net x i
  have hx'' := Function.update x i (if 0 < localField net x i then SpinState.up else if localField net x i < 0 then SpinState.down else x i)
  simp [energyDiff_eq]
  simp [updateState]
  split_ifs
  · simp [SpinState.up]
    have hspin : (SpinState.up).toReal = 1 := by simp
    have hlt : - (localField net x i * 1) + (localField net x i * (x i).toReal) ≤ 0 := by
      have hpos : (localField net x i) > 0 := by assumption
      simp [hpos]
      have hcomp : (x i).toReal ≤ 1 := by
        cases x i
        · simp
        · simp
      have hmul : (localField net x i) * (x i).toReal ≤ (localField net x i) * 1 := by gcongr
      linarith
    linarith
  · simp [SpinState.down]
    have hspin : (SpinState.down).toReal = -1 := by simp
    have hlt : - (localField net x i * -1) + (localField net x i * (x i).toReal) ≤ 0 := by
      have hneg : (localField net x i) < 0 := by assumption
      simp [hneg]
      have hcomp : (x i).toReal ≥ -1 := by
        cases x i
        · simp
        · simp
      have hmul : (localField net x i) * (x i).toReal ≤ (localField net x i) * -1 := by gcongr
      linarith
    linarith
  · simp
    have hspin : (x i).toReal = (x i).toReal := by simp
    have hlt : - (localField net x i * (x i).toReal) + (localField net x i * (x i).toReal) ≤ 0 := by
      simp
    linarith

/--
If the local field is non-zero, then the energy *strictly* decreases
after an update.
-/
lemma energy_strict_decrease (i : Fin n) (h : localField net x i ≠ 0) :
  energy net (updateState net x i) < energy net x := by
  have hx' := updateState net x i
  have hx'' := Function.update x i (if 0 < localField net x i then SpinState.up else if localField net x i < 0 then SpinState.down else x i)
  simp [energyDiff_eq]
  simp [updateState]
  split_ifs
  · simp [SpinState.up]
    have hspin : (SpinState.up).toReal = 1 := by simp
    have hlt : - (localField net x i * 1) + (localField net x i * (x i).toReal) < 0 := by
      have hpos : (localField net x i) > 0 := by assumption
      simp [hpos]
      have hcomp : (x i).toReal < 1 := by
        cases x i
        · simp at h
        · simp at h
          have hneq : SpinState.down ≠ SpinState.up := by
            simp
          have h2 : ¬localField net x i < 0 := by
            intro h2
            have h3 := not_lt_of_gt hpos h2
            contradiction
          have h4 : ¬localField net x i = 0 := by
            intro h4
            have h5 := h h4
            contradiction
          contradiction
      have hmul : (localField net x i) * (x i).toReal < (localField net x i) * 1 := by gcongr
      linarith
    linarith
  · simp [SpinState.down]
    have hspin : (SpinState.down).toReal = -1 := by simp
    have hlt : - (localField net x i * -1) + (localField net x i * (x i).toReal) < 0 := by
      have hneg : (localField net x i) < 0 := by assumption
      simp [hneg]
      have hcomp : (x i).toReal > -1 := by
        cases x i
        · simp at h
          have hneq : SpinState.up ≠ SpinState.down := by
            simp
          have h2 : ¬0 < localField net x i := by
            intro h2
            have h3 := not_lt_of_gt h2 hneg
            contradiction
          have h4 : ¬localField net x i = 0 := by
            intro h4
            have h5 := h h4
            contradiction
          contradiction
        · simp at h
      have hmul : (localField net x i) * (x i).toReal < (localField net x i) * -1 := by gcongr
      linarith
    linarith
  · simp at h

end HopfieldState
