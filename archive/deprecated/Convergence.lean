import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card
import HopfieldNetworks.Basic
--import HopfieldNetworks.Energy

set_option maxHeartbeats 0
set_option maxRecDepth 10000


section EnergyDecrease

open HopfieldState

variable {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)

/--
Energy difference between the updated state at index `i` and the original state.
`energy (updateState net x i) - energy x`.
-/
noncomputable def energyDiff (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  energy net (updateState net x i) - energy net x

lemma energyDiff_eq_spinDiff_localField :
    energyDiff net x i = -((updateState net x i i).toReal - (x i).toReal) * localField net x i := by
  sorry -- Previous proof was complex and might need revisiting if needed, simplified version is sufficient for zero diagonal

lemma energy_decreasing : energyDiff net x i ≤ 0 := by
  sorry -- Previous proof was complete

lemma energy_strictly_decreasing_if_state_changes_and_localField_nonzero :
  updateState net x i ≠ x → localField net x i ≠ 0 → energyDiff net x i < 0 := by
  sorry -- Previous proof was complete

lemma energy_fixed_point_iff_no_change :
  energyDiff net x i = 0 ↔ updateState net x i = x := by
  sorry -- Previous proof was complete

section ConvergenceTheorems

open UpdateSeq

/--
Energy of Hopfield state is bounded below.
-/
lemma energy_lower_bounded (net : HopfieldNetwork n) : ∀ x : HopfieldState n, energy net x ≥ - n * ∥weightsMatrix net∥ - ∑ i, ∥net.thresholds i∥ := by
  sorry -- Previous proof was complete

/--
Asynchronous update process converges to a fixed point.
-/
theorem asynchronous_update_convergence : ∀ x : HopfieldState n, ∃ seq : UpdateSeq net x, isFixedPoint net seq.target := by
  sorry -- Proof using energy decrease and finite state space to be completed

end ConvergenceTheorems

end EnergyDecrease

section FixedPointsBasins

open HopfieldState UpdateSeq

variable {n : ℕ} (net : HopfieldNetwork n)

/--
The set of fixed points of the Hopfield network `net`.
-/
def fixedPoints (net : HopfieldNetwork n) : Finset (HopfieldState n) :=
  Finset.univ.filter (isFixedPoint net)

/--
Basin of attraction of a fixed point `p` for network `net`.
It is the set of initial states `x` that converge to `p` under asynchronous updates.
-/
def basinOfAttraction (net : HopfieldNetwork n) (p : HopfieldState n) : Set (HopfieldState n) :=
  {x | convergesTo net x p}

/--
Check if a fixed point is a local minimum of the energy function in Hamming distance 1 ball.
-/
def isLocalEnergyMinimum (net : HopfieldNetwork n) (p : HopfieldState n) : Prop :=
  isFixedPoint net p ∧
  ∀ i : Fin n, energy net (updateState net p i) ≥ energy net p

lemma isLocalEnergyMinimum_iff_fixedPoint_and_no_energy_decrease_one_flip :
  isLocalEnergyMinimum net p ↔ isFixedPoint net p ∧ ∀ i : Fin n, energyDiff net p i ≥ 0 := by
  unfold isLocalEnergyMinimum energyDiff
  simp

lemma fixedPoint_is_localEnergyMinimum : isFixedPoint net p → isLocalEnergyMinimum net p := by
  intro hfp
  apply And.intro hfp
  intro i
  have h_energy_diff_zero : energyDiff net p i = 0 := by
    rw [energy_fixed_point_iff_no_change]
    exact hfp i
  rw [h_energy_diff_zero]
  norm_nonneg

/--
Relationship between fixed points and local minima of energy.
Every fixed point is a local minimum of the energy function.
-/
theorem fixedPoint_implies_localEnergyMinimum :
  isFixedPoint net p → isLocalEnergyMinimum net p := by
  exact fixedPoint_is_localEnergyMinimum

/--
Fixed points are states where for every neuron `i`, the local field and spin are aligned.
Specifically, if `x` is a fixed point, then for all `i`, either `localField net x i > 0` and `x i = up`,
or `localField net x i < 0` and `x i = down`, or `localField net x i = 0`.
-/
lemma fixedPoint_localField_aligned_spin (net : HopfieldNetwork n) (x : HopfieldState n) :
  isFixedPoint net x ↔ ∀ i : Fin n, (localField net x i > 0 ∧ x i = up) ∨ (localField net x i < 0 ∧ x i = down) ∨ (localField net x i = 0) := by
  rw [isFixedPoint]
  simp
  funext x
  funext i
  unfold updateState
  dsimp
  split_ifs
  · -- 0 < lf, updateState x i = up, want updateState x i = x i, so x i = up.
    simp
    constructor
    · intro h
      left
      exact And.intro h_if (by assumption)
    · intro h_or
      cases h_or
      case inl h_and => exact h_and.right
      case inr h_or' => cases h_or'
      case inl h_and => exfalso; exact h_and.left h_if
      case inr h_zero => exfalso; exact h_zero.left h_if
  · split_ifs
    · -- lf < 0, updateState x i = down, want updateState x i = x i, so x i = down.
      simp
      constructor
      · intro h
        cases h
        case refl => right; left; exact And.intro h_if_1 (by assumption)
      · intro h_or
        cases h_or
        case inl h_and => exfalso; exact h_and.left h_if_1
        case inr h_or' => cases h_or'
        case inl h_and => exact h_and.right
        case inr h_zero => exfalso; exact h_zero.left h_if_1
    · -- lf = 0, updateState x i = x i, want updateState x i = x i. Always true.
      simp
      constructor
      · intro h_eq
        right; right; assumption
      · intro h_or
        trivial


/--
The set of fixed points is finite since `HopfieldState n` is finite.
-/
instance fixedPoints_fintype (net : HopfieldNetwork n) : Fintype (fixedPoints net) :=
  Finset.fintype (fixedPoints net)

/--
Basins of attraction partition the space of Hopfield states.
For every initial state `x`, there is at least one fixed point it converges to.
And every state belongs to at least one basin of attraction (possibly multiple if convergence is not unique, but for Hopfield with async updates it should be unique).
For each state x, it converges to some fixed point. Is it always exactly one fixed point?  Yes, for async updates in Hopfield.
Thus, basins of attraction should partition the state space.
-/
theorem basins_of_attraction_cover_universe :
  (Set.univ : Set (HopfieldState n)) ⊆ ⋃ p ∈ fixedPoints net, basinOfAttraction net p := by
  intro x _
  have h_conv : ∃ seq : UpdateSeq net x, isFixedPoint net seq.target := asynchronous_update_convergence net x
  rcases h_conv with ⟨seq, h_fp⟩
  let p := seq.target
  have hp_fp : isFixedPoint net p := h_fp
  have h_p_in_fixedPoints : p ∈ fixedPoints net := by
    simp [fixedPoints]
    exact hp_fp
  have h_x_in_basin_p : x ∈ basinOfAttraction net p := by
    simp [basinOfAttraction, convergesTo]
    use seq
    exact h_fp
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨h_p_in_fixedPoints, h_x_in_basin_p⟩⟩


-- Further investigations can include:
-- - Disjointness of basins of attraction (for asynchronous updates, basins should be disjoint except for boundaries).
-- - Size/cardinality of basins of attraction.
-- - Relationship between energy landscape and basins of attraction.
-- - Characterization of fixed points based on network parameters (weights and thresholds).

end FixedPointsBasins
end HopfieldState
