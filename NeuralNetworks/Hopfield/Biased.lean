/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import NeuralNetworks.Hopfield.Basic

section BiasedHopfieldNetwork
open HopfieldState
variable {n : ℕ}
/--
`BiasedHopfieldNetwork` extends `HopfieldNetwork` by adding a bias term
to the local field.  The bias is a function of the neuron index.
-/
structure BiasedHopfieldNetwork (n : ℕ) extends HopfieldNetwork n where
  bias : Fin n → ℝ

/--
Local field for `BiasedHopfieldNetwork` includes the bias term.
`localField_biased(x, i) = (Wx)_i - threshold[i] + bias[i]`.
-/
def biasedLocalField (net : BiasedHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  localField net.toHopfieldNetwork x i + net.bias i
  -- Equivalent, more expanded form:
  -- (weightsMatrix net.toHopfieldNetwork).mulVec (toRealVector x) i - net.thresholds i + net.bias i

/--
Asynchronous update rule for `BiasedHopfieldNetwork` using the biased local field.
-/
noncomputable def biasedUpdateState (net : BiasedHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : HopfieldState n :=
  Function.update x i $
    let lf := biasedLocalField net x i
    if 0 < lf then SpinState.up
    else if lf < 0 then SpinState.down
    else x i

/--
Energy function for `BiasedHopfieldNetwork`.
A possible energy function for biased Hopfield network is:
`E(x) = -1/2 xᵀWx - bᵀx - cᵀx`, where `c` is the bias vector.
In our notation: `E(x) = -1/2 xᵀWx - (thresholds + bias)ᵀx`.
Or equivalently, we can absorb the bias into the thresholds: `thresholds' = thresholds - bias`.
Then `E(x) = -1/2 xᵀWx - thresholds'ᵀx`.
And `localField_biased(x, i) = (Wx)_i - thresholds'[i]`.

We keep the original thresholds and add a separate bias term in the energy function.
`E_biased(x) = -1/2 xᵀWx - bᵀx - biasᵀx = E(x) - biasᵀx`.
`E_biased(x) = -1/2 xᵀWx - Finset.sum Finset.univ (fun i => net.thresholds i * xVec i) - Finset.sum Finset.univ (fun i => net.bias i * xVec i)`
`E_biased(x) = -1/2 xᵀWx - Finset.sum Finset.univ (fun i => (net.thresholds i + net.bias i) * xVec i)`

**Refined Energy function for Biased Hopfield Network**:
`E_biased(x) = -1/2 xᵀWx - (thresholds + bias)ᵀx`.
-/
def biasedEnergy (net : BiasedHopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let hopfield_net := net.toHopfieldNetwork
  let xVec := toRealVector x;
  let W := weightsMatrix hopfield_net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - Finset.sum Finset.univ (fun i => (net.thresholds i + net.bias i) * xVec i)

/--
UpdateSeq for BiasedHopfieldNetwork.
-/
inductive BiasedUpdateSeq {n : ℕ} (net : BiasedHopfieldNetwork n) : HopfieldState n → Type
  | nil : (x : HopfieldState n) → BiasedUpdateSeq net x
  | cons : (x : HopfieldState n) → (i : Fin n) → BiasedUpdateSeq net (biasedUpdateState net x i) → BiasedUpdateSeq net x

namespace BiasedUpdateSeq
/--
Extract the final state from a biased update sequence.
-/
noncomputable def target {n : ℕ} {net : BiasedHopfieldNetwork n} {x : HopfieldState n}
  : BiasedUpdateSeq net x → HopfieldState n
  | nil x => x
  | cons _ _ s => s.target

/--
A state `x` is a fixed point under `BiasedHopfieldNetwork` if no single-neuron update changes the state.
-/
def biasedIsFixedPoint {n : ℕ} (net : BiasedHopfieldNetwork n) (x : HopfieldState n) : Prop :=
  ∀ i, biasedUpdateState net x i = x

/--
A state `x` converges to a fixed point `p` for BiasedHopfieldNetwork if there is an update
sequence from `x` that terminates at `p`, and `p` is a biased fixed point.
-/
def biasedConvergesTo {n : ℕ} (net : BiasedHopfieldNetwork n) (x p : HopfieldState n) : Prop :=
  ∃ (seq : BiasedUpdateSeq net x), seq.target = p ∧ biasedIsFixedPoint net p
end BiasedUpdateSeq

section BiasedEnergyDecrease

open HopfieldState BiasedUpdateSeq

variable {n : ℕ} (net : BiasedHopfieldNetwork n) (x : HopfieldState n) (i : Fin n)

/--
Energy difference for BiasedHopfieldNetwork.
-/
noncomputable def biasedEnergyDiff (net : BiasedHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  biasedEnergy net (biasedUpdateState net x i) - biasedEnergy net x

lemma biasedEnergyDiff_eq_neg_spinDiff_biasedLocalField :
    biasedEnergyDiff net x i = -((biasedUpdateState net x i i).toReal - (x i).toReal) * biasedLocalField net x i := by
  sorry -- Similar proof as for regular Hopfield network, just replace localField with biasedLocalField and energy with biasedEnergy

lemma biasedEnergy_decreasing : biasedEnergyDiff net x i ≤ 0 := by
  sorry -- Similar proof as for regular Hopfield network, using biasedLocalField and biasedEnergyDiff

lemma biasedEnergy_strictly_decreasing_if_state_changes_and_biasedLocalField_nonzero :
  biasedUpdateState net x i ≠ x → biasedLocalField net x i ≠ 0 → biasedEnergyDiff net x i < 0 := by
  sorry -- Similar proof

lemma biasedEnergy_fixed_point_iff_no_change :
  biasedEnergyDiff net x i = 0 ↔ biasedUpdateState net x i = x := by
  sorry -- Similar proof

section BiasedConvergenceTheorems

open BiasedUpdateSeq

/--
Biased asynchronous update process converges to a fixed point.
-/
theorem biased_asynchronous_update_convergence : ∀ x : HopfieldState n, ∃ seq : BiasedUpdateSeq net x, biasedIsFixedPoint net seq.target := by
  sorry -- Proof using biased energy decrease and finite state space, similar to regular Hopfield network convergence proof

end BiasedConvergenceTheorems

end BiasedEnergyDecrease

section DifferentUpdateRules

-- Synchronous Update Rule

/--
Synchronous update rule for Hopfield network.  All neurons are updated simultaneously
based on the local fields of the *current* state.
Returns the *next* state after one synchronous update.
-/
noncomputable def synchronousUpdateState (net : HopfieldNetwork n) (x : HopfieldState n) : HopfieldState n :=
  fun i => let lf := localField net x i
           if 0 < lf then SpinState.up
           else if lf < 0 then SpinState.down
           else x i -- Or could be random choice, or keep current state, as in asynchronous case.

/--
Synchronous update sequence.  Each step is a synchronous update of all neurons.
-/
inductive SyncUpdateSeq {n : ℕ} (net : HopfieldNetwork n) : HopfieldState n → Type
  | nil : (x : HopfieldState n) → SyncUpdateSeq net x
  | cons : (x : HopfieldState n) → SyncUpdateSeq net (synchronousUpdateState net x) → SyncUpdateSeq net x

namespace SyncUpdateSeq
/--
Target state of synchronous update sequence.
-/
noncomputable def target {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n}
  : SyncUpdateSeq net x → HopfieldState n
  | nil x => x
  | cons _ s => s.target

/--
Is fixed point for synchronous updates?
-/
def syncIsFixedPoint {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n) : Prop :=
  synchronousUpdateState net x = x

/--
Convergence to synchronous fixed point.
-/
def syncConvergesTo {n : ℕ} (net : HopfieldNetwork n) (x p : HopfieldState n) : Prop :=
  ∃ (seq : SyncUpdateSeq net x), seq.target = p ∧ syncIsFixedPoint net p
end SyncUpdateSeq

-- Stochastic Update Rule (Example - Probabilistic update based on local field)

/-
Stochastic update rule: Neuron `i` updates to `up` with probability p(localField(x, i)),
and to `down` with probability 1 - p(localField(x, i)).
Here, p is a probability function, e.g., sigmoid function.
For simplicity, let's consider a simple stochastic rule:
If localField > 0, always up. If localField < 0, always down. If localField = 0, flip a coin (e.g., 50% up, 50% down).
Or, simpler stochastic rule:  with probability depending on local field, flip to align with field, otherwise, flip opposite.
Example: Probability of flipping to `up` = sigmoid(localField(x, i)).

For now, let's consider a simpler stochastic rule:
if lf > 0, update to up with prob 1, else to down with prob 0. (Deterministic up)
if lf < 0, update to up with prob 0, else to down with prob 1. (Deterministic down)
if lf = 0, update to up with prob 0.5, else to down with prob 0.5. (Random choice)

This rule is still somewhat complex to formalize directly in `def`.  We would need to use probability monads or similar structures.
For a simpler formalization, we might need to define properties of stochastic Hopfield networks rather than concrete update rules directly in `def`.
For example, we can talk about expected energy change under a stochastic update rule.

Alternatively, for formalizing *properties*, we can consider abstract update rules defined by certain axioms,
e.g., "update rule that decreases energy on average", or "update rule that converges to some distribution".
-/

-- Example of different thresholding function: Sigmoid function

/--
Sigmoid function: `sigmoid(x) = 1 / (1 + exp(-x))`.  Maps ℝ to (0, 1).
Can be used to define probabilistic update rules.
-/
noncomputable def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

-- We could define an update rule based on sigmoid:
-- Probability of neuron i being `up` in the next state is sigmoid(localField(x, i)).

-- Further explorations / TODOs:
-- - Analyze convergence of synchronous updates (less guaranteed than asynchronous, can have cycles).
-- - Formalize and analyze stochastic update rules and their properties (e.g., stationary distributions).
-- - Investigate different thresholding functions and their impact on network dynamics.
-- - Consider Hopfield networks with continuous spins instead of discrete SpinState.

end DifferentUpdateRules

end BiasedHopfieldNetwork
