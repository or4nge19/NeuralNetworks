import NeuralNetworks.Hopfield.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Asymmetric Hopfield Networks

This module provides an implementation of asymmetric Hopfield networks, which are neural networks
with potentially non-symmetric weight matrices. The implementation includes:

## Main Components

* `AsymmetricHopfieldNetwork`: A structure representing asymmetric Hopfield networks
* `updateStateAsym`: A function for updating network states
* `SequentialUpdateSeq`: An inductive type representing update sequences
* `potentialFunction`: A function measuring network energy/stability
* `localFieldAsym`: A function computing local fields in asymmetric networks

## Key Theorems and Lemmas

* `potential_function_bounded`: Shows that the potential function is bounded
* `potential_function_change`: Analyzes how the potential changes during updates
* `localFieldAsym_update`: Describes local field behavior after state updates
* `updatedSpinValue_eq`: Relates updated spin values to local fields

## Mathematical Details

The implementation is based on the decomposition of asymmetric weight matrices into:
* An antisymmetric component A (where A_{ij} = -A_{ji})
* A positive definite symmetric component S
* A non-negative diagonal constraint

## References

TODO

## Implementation Notes

The implementation uses:
* Matrix decomposition for convergence analysis
* Sequential update scheme
* Custom potential function for discrete-time updates
* Standard proof techniques for boundedness and convergence

-/


open SpinState

@[simp] lemma SpinState.toReal_up : SpinState.up.toReal = 1 := rfl
@[simp] lemma SpinState.toReal_down : SpinState.down.toReal = -1 := rfl
open HopfieldState
open UpdateSeq

variable {n : ℕ}

/--
Redefines the updateState function to work with a Matrix directly for the weights and uses Fin n for the state.
-/
noncomputable def updateStateAsym (weights : Matrix (Fin n) (Fin n) ℝ) (thresholds : Fin n → ℝ) (x : HopfieldState n) (i : Fin n) : HopfieldState n :=
  Function.update x i $
    let lf := (∑ j ∈ Finset.univ, weights i j * (x j).toReal) - thresholds i
    if 0 < lf then SpinState.up
    else if lf < 0 then SpinState.down
    else x i

/- A sufficient condition for convergence of asymmetric Hopfield networks. ... (rest of the docstring) ... -/

/-- An asymmetric Hopfield network with `n` neurons. ... (rest of the docstring) ... -/
structure AsymmetricHopfieldNetwork (n : ℕ) : Type where
  weights : Matrix (Fin n) (Fin n) ℝ
  thresholds : Fin n → ℝ
  is_asymmetric : ∃ (A S : Matrix (Fin n) (Fin n) ℝ),
                    (∀ i j, A i j = -A j i) ∧  -- A is antisymmetric
                    (Matrix.PosDef S) ∧       -- S is positive definite
                    weights = A + S ∧
                    (∀ i, weights i i ≥ 0)    -- Non-negative diagonal

-- We can then define a function to check if a given HopfieldNetwork can be represented as an AsymmetricHopfieldNetwork

/--
  Defines when a Hopfield network is considered asymmetric.

  A network is asymmetric if its weight matrix can be decomposed as a sum
  of an antisymmetric matrix A and a positive definite matrix S, with the
  additional constraint that the diagonal elements of the weight matrix
  are non-negative.

  This decomposition is important for analyzing the dynamics and stability
  properties of Hopfield networks with non-symmetric weights.

  * `net` - The Hopfield network to check for asymmetry
-/
def isAsymmetric (net : HopfieldNetwork n) : Prop :=
  ∃ (A S : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, A i j = -A j i) ∧
    (Matrix.PosDef S) ∧
    net.weights.val = A + S ∧
    (∀ i, net.weights.val i i ≥ 0)


/-!
`SequentialUpdateSeq` represents a sequence of state updates in an asymmetric Hopfield network.

It is defined inductively, representing a sequence of `k` updates to the network's state, starting from an initial state `x`.
Each update involves selecting a neuron index and updating the state of that neuron based on the network's weights and thresholds.

- `net` : The asymmetric Hopfield network.
- `x` : The initial Hopfield state.
- `k` : The number of updates in the sequence.

The inductive structure ensures that the sequence is built step-by-step, with each step updating the state based on a chosen neuron index.

Constructors:
- `nil` : Represents an empty sequence (0 updates).
- `cons` : Represents a sequence with at least one update. It takes the current state `x`, the number of updates `k`, the index of the neuron to update `next_index`, and a proof that `next_index` is equal to `k % n` if `k > 0` and `0` if `k = 0`. It also takes the next sequence in the chain, which represents the remaining updates after the current one.
-/
inductive SequentialUpdateSeq {n : ℕ} (net : AsymmetricHopfieldNetwork n) : HopfieldState n → ℕ → Type
  | nil : (x : HopfieldState n) → SequentialUpdateSeq net x 0
  | cons : (x : HopfieldState n) → (k : ℕ) → (next_index : Fin n) →
           (h_next : k > 0 → next_index = ⟨k % n, Nat.mod_lt k (by exact Fin.pos next_index)⟩) →
           (h_zero : k = 0 → next_index = ⟨0, by exact Fin.pos next_index⟩) →
           SequentialUpdateSeq net (updateStateAsym net.weights net.thresholds x next_index) (k+1) →  -- Using updateStateAsym
           SequentialUpdateSeq net x k

namespace SequentialUpdateSeq

-- Length of the sequence
noncomputable def length {n : ℕ} {net : AsymmetricHopfieldNetwork n} {x : HopfieldState n} {k : ℕ} :
  SequentialUpdateSeq net x k → ℕ
  | nil _ => 0
  | cons _ _ _ _ _ seq' => seq'.length + 1

-- Final state of the sequence
noncomputable def target {n : ℕ} {net : AsymmetricHopfieldNetwork n} {x : HopfieldState n} {k : ℕ} :
  SequentialUpdateSeq net x k → HopfieldState n
  | nil x => x
  | cons _ _ _ _ _ seq' => seq'.target

end SequentialUpdateSeq

-- Define localField for AsymmetricHopfieldNetwork
noncomputable def localFieldAsym (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ, net.weights i j * (x j).toReal - net.thresholds i

-- Potential Function (Attempt 1)
noncomputable
def potentialFunction (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ,
    ∑ j ∈ Finset.univ,
      net.weights i j *
      (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then
        (if localFieldAsym net x i > 0 then 1 else -1)
      else (x i).toReal) *
      (x j).toReal

-- Lemma: potentialFunction is bounded
lemma potential_function_bounded (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (k : ℕ) : ∃ (lowerBound upperBound : ℝ), lowerBound ≤ potentialFunction net x k ∧ potentialFunction net x k ≤ upperBound := by
  let maxSum : ℝ := ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, |net.weights i j|
  use -maxSum, maxSum
  constructor
  · -- Instead of using Finset.sum_le_sum directly, we'll work with the definition of potentialFunction
    unfold potentialFunction

    -- Show that for each term, the product is at least -|weights_ij|
    have hbound : ∀ (i j : Fin n),
      net.weights i j *
      (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) *
      (x j).toReal ≥ -|net.weights i j| := by
        intro i j
        have h1 : |(if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal)| = 1 := by
          split_ifs with h h_field
          · simp
          · simp
          · cases x i
            · simp [SpinState.toReal]
            · simp [SpinState.toReal]
        have h2 : |(x j).toReal| = 1 := by
          cases x j
          · simp [SpinState.toReal]
          · simp [SpinState.toReal]

        calc
          net.weights i j * (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) * (x j).toReal
          ≥ -|net.weights i j * (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) * (x j).toReal| := by
            exact
              neg_abs_le
                ((net.weights i j *
                    if i = ⟨k % n, Nat.mod_lt k (Fin.pos i)⟩ then
                      if localFieldAsym net x i > 0 then 1 else -1
                    else (x i).toReal) *
                  (x j).toReal)
          _ = -|net.weights i j| * |(if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal)| * |(x j).toReal| := by
            split_ifs with h h_field
            · -- i = index case with positive field
              simp only [abs_mul, abs_one]
              simp only [neg_mul, mul_neg, neg_neg]
            · -- i = index case with non-positive field
              simp only [abs_mul, abs_neg, abs_one]
              ring_nf
            · -- i ≠ index case
              cases x i <;> simp [SpinState.toReal, abs_mul]
              · cases x j <;> simp [abs_neg, abs_mul]
              · cases x j <;> simp [abs_neg, abs_mul]

          _ = -|net.weights i j| * 1 * 1 := by rw [h1, h2]
          _ = -|net.weights i j| := by ring_nf

    -- Now use the bound to establish the inequality with the sum
    calc
      potentialFunction net x k
      = ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          net.weights i j *
          (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) *
          (x j).toReal := by rfl
      _ ≥ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, -|net.weights i j| := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          exact hbound i j
      _ = -(∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, |net.weights i j|) := by
          simp [Finset.sum_neg_distrib]
      _ = -maxSum := by rfl

  · apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h1 : |(if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal)| = 1 := by
        split_ifs with h h_field
        · exact abs_one
        · simp_all only [Finset.mem_univ, gt_iff_lt, not_lt, abs_neg, abs_one]
        cases x i
        · simp [SpinState.toReal]
        · simp [SpinState.toReal]
    have h2: |(x j).toReal| = 1 := by
      cases x j
      · simp [SpinState.toReal]
      · simp [SpinState.toReal]
    calc
      net.weights i j * (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) * (x j).toReal
      ≤ |net.weights i j * (if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal) * (x j).toReal| := by
          apply le_abs_self
      _ = |net.weights i j| * |(if i = ⟨k % n, Nat.mod_lt k (by exact Fin.pos i)⟩ then (if localFieldAsym net x i > 0 then 1 else -1) else (x i).toReal)| * |(x j).toReal| := by
          rw [abs_mul, abs_mul]
      _ = |net.weights i j| * 1 * 1 := by rw [h1, h2]
      _ = |net.weights i j| := by ring

-- Helper Lemma 1: Value of the updated spin (toReal)
noncomputable def updatedSpinValue (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  (updateStateAsym net.weights net.thresholds x i i).toReal

-- Lemma for updatedSpinValue in terms of localFieldAsym
lemma updatedSpinValue_eq (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) :
  updatedSpinValue net x i = if localFieldAsym net x i > 0 then 1 else if localFieldAsym net x i < 0 then -1 else (x i).toReal := by
  unfold updatedSpinValue updateStateAsym localFieldAsym
  split_ifs with h1 h2
  · -- case: localFieldAsym net x i > 0
    simp [Function.update]
    rw [@Fin.sum_univ_def]
    rw [@Finset.sum_list_map_count]
    simp_all only [gt_iff_lt, sub_pos, List.toFinset_finRange, List.count_finRange, one_smul, ↓reduceIte]
    simp [SpinState.toReal_up]
  · -- case: localFieldAsym net x i < 0
    simp [Function.update]
    split_ifs;
    simp_all only [gt_iff_lt, sub_pos, not_true_eq_false]
    simp_all only [gt_iff_lt, sub_pos, not_false_eq_true, sub_neg, not_lt, SpinState.toReal_down]
    simp_all only [gt_iff_lt, sub_pos, not_false_eq_true, sub_neg]

  · -- case: localFieldAsym net x i ≤ 0 and localFieldAsym net x i ≥ 0
    have h_eq : (∑ j ∈ Finset.univ, net.weights i j * (x j).toReal) - net.thresholds i = 0 :=
      by { apply le_antisymm
           { exact not_lt.1 h1 }
           { exact not_lt.1 h2 } }
    rw [h_eq, Function.update_self]
    simp_all only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, ↓reduceIte]


-- Helper Lemma 2:  localFieldAsym after an update
lemma localFieldAsym_update {n : ℕ} (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (i : Fin n) :
    localFieldAsym net (updateStateAsym net.weights net.thresholds x i) i =
    (∑ j ∈ Finset.univ, net.weights i j * (if j = i then (updatedSpinValue net x i) else (x j).toReal)) - net.thresholds i := by
    unfold localFieldAsym
    -- The key is to understand how updateStateAsym affects the sum
    have h_update : ∀ j : Fin n, (updateStateAsym net.weights net.thresholds x i j).toReal =
      if j = i then updatedSpinValue net x i else (x j).toReal := by
      intro j
      unfold updatedSpinValue updateStateAsym
      by_cases h_j_eq_i : j = i
      · subst h_j_eq_i
        simp [Function.update_self]
      simp_all only [sub_pos, sub_neg, ne_eq, not_false_eq_true, Function.update_of_ne, ↓reduceIte]
    simp_all only [mul_ite]

-- Helper Lemma 3: Expressing x'_j in terms of x_j and updatedSpinValue
lemma x'_eq_x_update {n : ℕ} (net: AsymmetricHopfieldNetwork n) (x: HopfieldState n) (i j : Fin n) :
  let x' := updateStateAsym net.weights net.thresholds x i
  (x' j).toReal = (if j = i then (updatedSpinValue net x i) else (x j).toReal)
  := by
    by_cases h_j_eq_i : j = i
    · subst h_j_eq_i
      unfold updatedSpinValue updateStateAsym
      simp [Function.update_self]
    · unfold updateStateAsym
      simp [Function.update_of_ne h_j_eq_i]
      simp_all only [↓reduceIte]


/-!
  `potential_function_change` calculates the change in the potential function of an asymmetric Hopfield network
  after a single state update. It decomposes the change into three cases:

  - Case 1: The updated index `i'` (derived from `k % n`).
  - Case 2: The next index `i''` (derived from `(k + 1) % n`).
  - Case 3: All other indices `i` that are neither `i'` nor `i''`.

  The lemma expresses the difference `potentialFunction net x' (k+1) - potentialFunction net x k`
  as a sum of differences in weighted sums over the network's nodes, considering the local fields
  and state values before and after the update.

  Parameters:
  - `n`: The number of nodes in the Hopfield network.
  - `net`: The `AsymmetricHopfieldNetwork` object.
  - `x`: The current `HopfieldState`.
  - `k`: The current update step.
  - `h_k_lt_n`: Proof that `k < n`.

  Returns:
  An equality expressing the change in the potential function in terms of weighted sums
  related to the state update. The proof involves simplifying the sums by considering
  the update rule and the definition of the local field.
-/
lemma potential_function_change {n : ℕ} (net : AsymmetricHopfieldNetwork n) (x : HopfieldState n) (k : ℕ)
    (h_k_lt_n : k < n) :
    let nextIndex : Fin n := ⟨k % n, Nat.mod_lt k (Nat.zero_lt_of_lt h_k_lt_n)⟩
    let x' := updateStateAsym net.weights net.thresholds x nextIndex
    let i' : Fin n := nextIndex
    let i'' : Fin n := ⟨(k + 1) % n, Nat.mod_lt (k + 1) (Nat.zero_lt_of_lt h_k_lt_n)⟩
    potentialFunction net x' (k+1) - potentialFunction net x k =
      -- Case 1: i = i'
      (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
      (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) +
      -- Case 2: i = i''
      (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) -
      (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal) +
      -- Case 3: i ≠ i' and i ≠ i''
      (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
        (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
        (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
      else 0)
    := by
      -- Define the variables from the let-bindings to use in the proof
      let nextIndex : Fin n := ⟨k % n, Nat.mod_lt k (Nat.zero_lt_of_lt h_k_lt_n)⟩
      let x' := updateStateAsym net.weights net.thresholds x nextIndex
      let i' : Fin n := nextIndex
      let i'' : Fin n := ⟨(k + 1) % n, Nat.mod_lt (k + 1) (Nat.zero_lt_of_lt h_k_lt_n)⟩

      -- Case 1 Simplification (using helper lemmas)
      have h_case1 : (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
                     (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) =
                     (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (if j = i' then updatedSpinValue net x i' else (x j).toReal)) -
                     (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) := by
        -- Replace each x' j with the correct value based on the update rule
        have h_update : ∀ j, (x' j).toReal = if j = i' then updatedSpinValue net x i' else (x j).toReal := by
          intro j
          exact x'_eq_x_update net x i' j

        -- Let's rewrite the left-hand sum using our substitution rule
        congr
        · exact
          (Set.eqOn_univ
                (fun j ↦
                  (net.weights i' j * if localFieldAsym net x' i' > 0 then 1 else -1) *
                    (x' j).toReal)
                fun j ↦
                (net.weights i' j * if localFieldAsym net x' i' > 0 then 1 else -1) *
                  if j = i' then updatedSpinValue net x i' else (x j).toReal).mp
            fun ⦃x_1⦄ a ↦
            congrArg
              (HMul.hMul (net.weights i' x_1 * if localFieldAsym net x' i' > 0 then 1 else -1))
              (h_update x_1)

      -- Further simplification of Case 1 would involve substituting the definition of localFieldAsym net x' i'
      -- and considering the cases where the update *does* and *does not* flip the spin.

      -- Continue simplification of Case 1
      have h_case1_simplified : ∃ Δ₁ : ℝ, (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
                     (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) = Δ₁ := by
        -- This would typically involve analysis of how the local field changes after update
        -- For now, we just assert existence of some Δ₁ that represents this difference
        use (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal)

      -- Case 2 Simplification: i = i''
      have h_case2 : ∃ Δ₂ : ℝ, (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) -
                     (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal) = Δ₂ := by
        -- Apply similar transformation as in Case 1
        use (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal)

      -- Case 3 Simplification: i ≠ i' and i ≠ i''
      have h_case3 : ∃ Δ₃ : ℝ, (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
        (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
        (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
      else 0) = Δ₃ := by
        use (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
          (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
          (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
        else 0)

      -- Extract the values from our existence proofs
      rcases h_case1_simplified with ⟨Δ₁, h_Δ₁⟩
      rcases h_case2 with ⟨Δ₂, h_Δ₂⟩
      rcases h_case3 with ⟨Δ₃, h_Δ₃⟩

      -- Establish the definition of potentialFunction
      have h_pot_def1 : potentialFunction net x k =
        (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) +
        (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal) +
        (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
          (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
        else 0) := by
        sorry  -- This would require the detailed expansion of potentialFunction net x k

      have h_pot_def2 : potentialFunction net x' (k+1) =
        (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) +
        (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) +
        (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
          (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal)
        else 0) := by
        sorry  -- This would require the detailed expansion of potentialFunction net x' (k+1)

      -- Now we can compute the difference
      calc
        potentialFunction net x' (k+1) - potentialFunction net x k
        = ((∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) +
           (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) +
           (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
             (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal)
           else 0)) -
          ((∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) +
           (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal) +
           (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
             (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
           else 0)) := by rw [h_pot_def2, h_pot_def1]
        _ = ((∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal)) +
           ((∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal)) +
           ((∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal)
            else 0) -
            (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
            else 0)) := by ring
        _ = Δ₁ + Δ₂ + Δ₃ := by
          have h1 : ∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal -
                    ∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal = Δ₁ := h_Δ₁
          have h2 : ∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal -
                    ∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal = Δ₂ := h_Δ₂
          have h3 : (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
                      (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
                      (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
                    else 0) = Δ₃ := h_Δ₃

          -- The key is to show that the difference of sums equals the sum of differences
          have h_difference :
            (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              ∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal
            else 0) -
            (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              ∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal
            else 0) =
            (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
              (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
            else 0) := by
            sorry

          rw [h1, h2, h_difference, h3]

        _ = (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x' i' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i' j * (if localFieldAsym net x i' > 0 then 1 else -1) * (x j).toReal) +
            (∑ j ∈ Finset.univ, net.weights i'' j * (if localFieldAsym net x' i'' > 0 then 1 else -1) * (x' j).toReal) -
            (∑ j ∈ Finset.univ, net.weights i'' j * (x i'').toReal * (x j).toReal) +
            (∑ i ∈ Finset.univ, if i ≠ i' ∧ i ≠ i'' then
              (∑ j ∈ Finset.univ, net.weights i j * (x' i).toReal * (x' j).toReal) -
              (∑ j ∈ Finset.univ, net.weights i j * (x i).toReal * (x j).toReal)
            else 0) := by
            rw [h_Δ₁]
            --rw [h_Δ₂]
            rw [h_Δ₃]
            -- Fix the expression by grouping the second sum term properly
            sorry
