import NeuralNetworks.Hopfield.Basic
import NeuralNetworks.Hopfield.Energy

/-!
# Convergence Theorems for Hopfield Networks

This file proves the convergence of Hopfield networks under certain conditions.
Specifically, it shows that starting from any initial state, a finite sequence of
single-neuron updates leads to a stable fixed point.

The key ideas behind the proof are:

1.  **Energy Function:** The Hopfield network has an energy function that decreases
  whenever a neuron's state is updated.

2.  **Finite State Space:** The state space of the Hopfield network is finite.

3.  **No Infinite Descending Chains:** In a finite state space, it is impossible to
  have an infinite strictly decreasing chain of energy values.

4.  **Well-Foundedness:** The energy order is well-founded, meaning there are no
  infinite descending chains.

5.  **Convergence:** By well-founded induction on the energy order, we can show that
  starting from any initial state, there is a finite sequence of updates that leads
  to a stable fixed point.
  This convergence result relies on the assumption that all thresholds are zero,
  i.e., `(h_threshold_zero : ∀ j, net.thresholds j = 0)`.

## Key Definitions

*   `HopfieldState`: Represents the state of the Hopfield network, i.e., the spin
  configuration of all neurons.
*   `HopfieldNetwork`: Represents the Hopfield network, including the weight matrix
  and thresholds.
*   `energy`: The energy function of the Hopfield network.
*   `updateState`: Updates the state of a single neuron in the network.
*   `UpdateSeq`: A namespace for defining functions and lemmas related to sequences
  of neuron updates.
*   `isFixedPoint`: Checks if a given state is a fixed point of the network, i.e.,
  no single-neuron update can change the state.

## Main Results

*   `energy_strict_decrease`: The energy strictly decreases if we actually flip the
  i-th spin.
*   `no_infinite_descending_chain`: A strictly decreasing chain in a finite set is
  impossible.
*   `energy_wf`: Well‐foundedness of the `energy_order`: any infinite descending
  chain in energy would require infinitely many distinct states from a finite set,
  which is impossible.
*   `convergence`: Main convergence theorem: from any initial state `x₀`, there is
  a finite sequence of single-neuron updates leading to a stable fixed point.
-/

namespace HopfieldState

open SpinState

variable {n : ℕ}

section ConvergenceTheorems

open UpdateSeq

instance fintype_SpinState : Fintype SpinState :=
{ elems := {SpinState.up, SpinState.down},
  complete := by
    intro s
    cases s with
    | up =>
      rw [Finset.mem_insert]
      left;
      rfl
    | down =>
      rw [Finset.mem_insert]
      right;
      rw [Finset.mem_singleton]
       }

instance finite_HopfieldState {n : ℕ} : Finite (HopfieldState n) :=
  Pi.finite

--instance fintype_HopfieldState {n : ℕ} : Fintype (HopfieldState n) :=
noncomputable
instance fintype_HopfieldState {n : ℕ} : Fintype (HopfieldState n) :=
  Fintype.ofFinite (HopfieldState n)

/--
Energy strictly decreases if we actually flip the i-th spin.
-/
lemma energy_strict_decrease {n : ℕ} (net : HopfieldNetwork n)
    (x : HopfieldState n) (i : Fin n)
    (h_threshold_zero : ∀ j, net.thresholds j = 0)
    (h_not_fixed : updateState net x i ≠ x) :
    energy net (updateState net x i) < energy net x := by
  have h_ediff : energy net (updateState net x i) - energy net x = energyDiff net x i := by rfl

  suffices h_diff_neg : energyDiff net x i < 0 from lt_of_sub_neg (by rw [h_ediff]; exact h_diff_neg)

  apply energy_strictly_decreasing_if_state_changes_and_localField_nonzero
  · intro j
    exact h_threshold_zero j

  · exact h_not_fixed
  have h_lf_ne_zero : localField net x i ≠ 0 := by
    intro h_lf_eq_zero
    apply h_not_fixed
    funext j
    by_cases hj : j = i
    · rw [hj]
      unfold updateState
      simp [h_lf_eq_zero]
    · unfold updateState
      simp [hj]
  exact h_lf_ne_zero

def energy_order (net : HopfieldNetwork n) (x y : HopfieldState n) : Prop :=
  HopfieldState.energy net x < HopfieldState.energy net y

lemma state_space_finite (n : ℕ) : Finite (HopfieldState n) := by
  have : HopfieldState n = (Fin n → SpinState) := rfl
  rw [this]
  exact Pi.finite

/-
A strictly decreasing chain in a finite set is impossible.
-/
lemma no_infinite_descending_chain {n : ℕ} (net : HopfieldNetwork n) :
    ¬ (∃ (f : ℕ → HopfieldState n),
      ∀ k, energy_order net (f (k+1)) (f k)) := by
  rintro ⟨f, hdesc⟩
  -- Because the state space is finite, an infinite sequence must revisit some state
  have : ∃ i j, i < j ∧ f i = f j := by
    haveI : Fintype (HopfieldState n) := inferInstance
    -- Pigeonhole principle: an infinite sequence in a finite set must repeat
    let N := Fintype.card (HopfieldState n)
    have h_card_HopfieldState : N > 0 := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨fun _ => SpinState.up⟩

    -- Consider N+1 elements, which must contain a duplicate by pigeonhole principle
    let seq : Fin (N+1) → HopfieldState n := fun i => f i.val

    have h_card_fin : Fintype.card (Fin (N+1)) = N+1 := by
      exact Fintype.card_fin (N+1)

    have h_card_lt : Fintype.card (HopfieldState n) < Fintype.card (Fin (N+1)) := by
      rw [h_card_fin]
      exact Nat.lt_succ_self N

    have h_exists_pair : ∃ (x y : Fin (N+1)), x ≠ y ∧ seq x = seq y := by
      exact Fintype.exists_ne_map_eq_of_card_lt seq h_card_lt

    have not_inj : ¬Function.Injective seq := by
      intro h_inj
      rcases h_exists_pair with ⟨x, y, hxy, heq⟩
      apply hxy
      exact h_inj heq

    obtain ⟨i, j, hi_ne_hj, heq⟩ := Function.not_injective_iff.mp not_inj
    have hij : i ≠ j := by
      intro h
      rw [h] at hi_ne_hj
      exact heq h

    have h_val_ne : i.val ≠ j.val := by
      intro h_eq
      apply hij
      exact Fin.eq_of_val_eq h_eq

    have h_lt_cases : i.val < j.val ∨ j.val < i.val := by
      omega

    -- Handle both cases
    cases h_lt_cases with
    | inl h_i_lt_j =>
      -- Case i.val < j.val
      use i.val, j.val
    | inr h_j_lt_i =>
      -- Case j.val < i.val
      use j.val, i.val
      constructor
      · exact h_j_lt_i
      · -- Show f j.val = f i.val
        have : f j.val = seq j := by rfl
        have : f i.val = seq i := by rfl
        rw [this]
        exact id (Eq.symm hi_ne_hj)

  -- Extract witnesses i, j where f i = f j and i < j
  obtain ⟨i, j, hij, heq⟩ := this
  -- Show that E(f j) = E(f i) since f j = f i
  have eqEnergy : energy net (f j) = energy net (f i) := by
    rw [heq]
  -- But we also have the strict chain E(f j) < ... < E(f i)
  have descent : ∀ k m, k < m → energy net (f m) < energy net (f k) := by
    intro k m hkm
    induction h : (m - k) generalizing m k with
    | zero =>
      -- In the zero case of the induction, m - k = 0
      have h_eq_zero : m - k = 0 := by exact h

      -- But we also have k < m which implies m - k > 0
      have h_pos : m - k > 0 := by
        apply Nat.sub_pos_of_lt
        exact hkm

      -- These two facts contradict each other
      have h_not_zero : m - k ≠ 0 := by
        exact Nat.ne_of_gt h_pos

      simp_all only

    | succ d ih =>
      by_cases h : m = k + 1
      · -- Case: m = k + 1
        rw [h]
        exact hdesc k
      · -- Case: m > k + 1
        have k_lt_kplus1 : k < k + 1 := Nat.lt_succ_self k
        have kplus1_le_m : k + 1 ≤ m := Nat.succ_le_of_lt hkm
        have e1 : energy net (f (k + 1)) < energy net (f k) := hdesc k

        -- Show that k+1 < m
        have k_plus_1_lt_m : k + 1 < m := by
          apply Nat.lt_of_le_of_ne kplus1_le_m
          exact Ne.symm h

        -- Show that m-(k+1) < m-k
        have m_minus_k_plus_1_plus_1_eq_m_minus_k : m - (k + 1) + 1 = m - k :=
          calc
            m - (k + 1) + 1 = (m + 1) - (k + 1) := by
              have : k + 1 ≤ m := Nat.succ_le_of_lt hkm
              rw [Nat.sub_add_comm hkm]
            _ = m - k := by rw [Nat.succ_sub_succ]


        have m_minus_k_plus_1_lt_m_minus_k : m - (k + 1) < m - k := by
          rw [← m_minus_k_plus_1_plus_1_eq_m_minus_k]
          exact Nat.lt_succ_self (m - (k + 1))

        have e2 : energy net (f m) < energy net (f (k + 1)) := by
          apply (ih (k + 1) m)
          · exact k_plus_1_lt_m
          simp_all only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, add_left_inj]

        exact lt_trans e2 e1

  have chain : energy net (f j) < energy net (f i) :=
    descent i j hij
  -- Contradiction: can't have both E(f j) = E(f i) and E(f j) < E(f i)
  exact lt_irrefl _ (eqEnergy.symm ▸ chain)

/--
Well‐foundedness of the `energy_order`: any infinite descending chain
in energy would require infinitely many distinct states from a finite set,
which is impossible.
-/
def energy_wf {n : ℕ} (net : HopfieldNetwork n) : WellFounded (energy_order net) := by
  have fin : Fintype (HopfieldState n) := inferInstance
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  apply IsEmpty.mk
  intro ⟨f, hf⟩
  apply no_infinite_descending_chain net
  use f

/--
Main convergence theorem: from any initial state `x₀`, there is
a finite sequence of single-neuron updates leading to a stable fixed point.
-/
theorem convergence {n : ℕ} (net : HopfieldNetwork n) (x₀ : HopfieldState n)
    (h_thresholds_zero : ∀ j, net.thresholds j = 0) :
    ∃ (y : HopfieldState n) (path : List (Fin n)),
      UpdateSeq.isFixedPoint net y ∧
      y = path.foldl (fun s i => updateState net s i) x₀ := by
  apply WellFounded.induction (energy_wf net) x₀
  intro x IH
  by_cases h : UpdateSeq.isFixedPoint net x
  · -- If x is already a fixed point, we are done.
    use x, []
    exact ⟨h, rfl⟩
  · -- Otherwise, pick an i that changes x
    -- Not fixed point means there's an i where update changes the state
    have h_exists : ∃ i, updateState net x i ≠ x := by
      simp [UpdateSeq.isFixedPoint] at h
      push_neg at h
      exact h
    obtain ⟨i, hi⟩ := h_exists

    let x' := updateState net x i
    have h_dec := by exact n
    have h_energy_order : energy_order net x' x := by
      apply energy_strict_decrease
      · exact h_thresholds_zero
      · exact hi
    -- By induction, starting from x', we get a terminal stable state y with a path
    obtain ⟨y, path, hy⟩ := IH x' h_energy_order
    use y, i :: path
    constructor
    · exact hy.1
    · simp [List.foldl]
      rw [hy.2]
