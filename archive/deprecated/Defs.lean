import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic
import Mathlib.Data.Real.Sign

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-!
# Hopfield Networks Formalization

This file contains a Lean 4 formalization of Hopfield networks. We model
neurons as spins in `SpinState`, build `HopfieldState` as a configuration
of those spins, define a standard Hamming metric, and introduce the
`HopfieldNetwork` structure with an associated energy function.
We then provide update rules, stable states (fixed points), and a
simple content-addressable memory structure.
-/


/--
`SpinState` represents a binary spin, either up or down.
We interpret this as `+1` or `-1`, respectively, in `toReal`.
This structure is isomorphic to `Bool` and `Fin 2`, and also admits
a group structure isomorphic to `ℤ₂` under multiplication.
-/
inductive SpinState : Type
  | up : SpinState
  | down : SpinState
  deriving DecidableEq, Inhabited, Fintype

namespace SpinState

/--
Map `SpinState` to real numbers: `up ↦ 1`, `down ↦ -1`.
-/
def toReal : SpinState → ℝ
  | up => 1
  | down => -1

/--
`SpinState` forms a commutative group under multiplication,
with `up` as the identity element.
-/
instance : CommGroup SpinState where
  mul := fun s₁ s₂ => match s₁, s₂ with
    | up, up => up
    | down, down => up
    | _, _ => down
  one := up
  inv := id
  mul_assoc := by
    intros a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  mul_comm := by
    intros a b
    cases a <;> cases b <;> rfl
  inv_mul_cancel := by intro a; cases a <;> rfl -- Kept `cases` for now, might revisit

/--
Interpret `up` as `true` and `down` as `false`.
-/
def toBool : SpinState → Bool
  | up => true
  | down => false

/--
Inverse of `toBool`: `true ↦ up`, `false ↦ down`.
-/
def ofBool (b : Bool) : SpinState :=
  if b then up else down

@[simp]
lemma ofBool_toBool (b : Bool) : (ofBool b).toBool = b := by
  cases b <;> rfl

@[simp]
lemma toBool_ofBool (s : SpinState) : ofBool (s.toBool) = s := by
  cases s <;> rfl

@[simp]
lemma up_down_distinct : up.toReal ≠ down.toReal := by
  simp [toReal]; norm_num

@[simp]
lemma up_down_diff : up.toReal - down.toReal = 2 := by
  simp [toReal]; norm_num

@[simp]
lemma down_up_diff : down.toReal - up.toReal = -2 := by
  simp [toReal]; norm_num

/--
If two spin states have the same real value, they must be equal.
-/
@[simp]
lemma eq_of_toReal_eq {s₁ s₂ : SpinState} (h : s₁.toReal = s₂.toReal) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> try rfl
  all_goals {
    simp [toReal] at h
    norm_num at h
  }

/-- Equivalence between `SpinState` and `Bool`. -/
def spinStateEquivBool : SpinState ≃ Bool :=
{ toFun := toBool
  invFun := ofBool
  left_inv := toBool_ofBool
  right_inv := ofBool_toBool }

/-- Equivalence between `SpinState` and `ZMod 2`. -/
def spinStateEquivZmod2 : SpinState ≃ ZMod 2 :=
{ toFun := fun s => match s with | up => 0 | down => 1
  invFun := fun z => if z = 0 then up else down
  left_inv := by intro z; cases z <;> simp
  right_inv := by
    intro z
    fin_cases z
    · simp [SpinState.up];
    · simp [SpinState.down];
}


end SpinState

/--
A Hopfield state for `n` neurons is a function from `Fin n` to `SpinState`.
-/
def HopfieldState (n : ℕ) := Fin n → SpinState

namespace HopfieldState

variable {n : ℕ}

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.
-/
noncomputable instance : MetricSpace (HopfieldState n) where
  dist := fun x y => (Finset.card {i | x i ≠ y i} : ℝ)
  dist_self := by simp [Finset.card_eq_zero]
  dist_comm := by
    intro x y
    simp [Dist]
    congr
    ext i
    exact ne_comm
  dist_triangle := by
    intro x y z
    simp [Dist]
    have : Finset.filter (fun i => x i ≠ z i) Finset.univ ⊆
          Finset.filter (fun i => x i ≠ y i) Finset.univ ∪
          Finset.filter (fun i => y i ≠ z i) Finset.univ := by
      intro i hi
      simp at *
      by_contra h
      push_neg at h
      have h1 := h.1
      have h2 := h.2
      have : x i = y i := by
        by_contra hxy
        exact hxy h1
      have : y i = z i := by
        by_contra hyz
        exact hyz h2
      have : x i = z i := Eq.trans h1 h2
      exact hi this
    calc (Finset.card (Finset.filter (fun i => x i ≠ z i) Finset.univ) : ℝ)
      ≤ Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ ∪
                     Finset.filter (fun i => y i ≠ z i) Finset.univ) :=
        Nat.cast_le.mpr (Finset.card_le_card this)
      _ ≤ Finset.card {i | x i ≠ y i} + Finset.card {i | y i ≠ z i} := by
        rw [←Nat.cast_add]
        apply Nat.cast_le.2
        apply Finset.card_union_le
  eq_of_dist_eq_zero := by
    intro x y h
    simp [Dist, Finset.card_eq_zero] at h
    funext i
    by_contra h'
    have : i ∈ Finset.filter (fun i => x i ≠ y i) Finset.univ := by
      simp [h']
    rw [h] at this
    exact absurd this (Finset.not_mem_empty i)

/--
Convert a Hopfield state to a real vector of dimension `n`, where
each coordinate is either `+1` or `-1`.
-/
def toRealVector (x : HopfieldState n) : Fin n → ℝ :=
  fun i => (x i).toReal

@[simp]
lemma toRealVector_apply (x : HopfieldState n) (i : Fin n) :
  x.toRealVector i = (x i).toReal := rfl

@[ext]
lemma hopfieldState_ext {x y : HopfieldState n} (h : ∀ i, x i = y i) : x = y := funext h


/--
`HopfieldNetwork` consists of:
1. A real-valued weight matrix `weights` of size `n × n`, which is Hermitian (symmetric in ℝ)
   and has zero diagonal.
2. A threshold vector `thresholds` with one real value per neuron.
-/
structure HopfieldNetwork (n : ℕ) : Type where
  weights : {M : Matrix (Fin n) (Fin n) ℝ // M.IsHermitian ∧ Matrix.diag M = 0}
  thresholds : Fin n → ℝ

/--
Convenience accessor for the underlying weights matrix.
-/
def weightsMatrix (net : HopfieldNetwork n) : Matrix (Fin n) (Fin n) ℝ := net.weights.val

@[simp]
lemma weights_symmetric (net : HopfieldNetwork n) :
  Matrix.IsSymm (weightsMatrix net) := net.weights.prop.1

@[simp]
lemma weights_hermitian (net : HopfieldNetwork n) :
  (weightsMatrix net).IsHermitian := net.weights.prop.1

@[simp]
lemma weights_diag_zero (net : HopfieldNetwork n) :
  Matrix.diag (weightsMatrix net) = 0 := net.weights.prop.2

/--
Energy function of the Hopfield network for a given state `x`.
Typical Hopfield energy: `E(x) = -1/2 xᵀWx - bᵀx`.
-/
noncomputable def energy (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - Finset.sum Finset.univ (fun i => net.thresholds i * xVec i)

/--
Local field (net input) for neuron `i` in state `x`,
`(Wx)_i - threshold[i]`.
-/
def localField (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  (weightsMatrix net).mulVec (toRealVector x) i - net.thresholds i

/--
Asynchronous update rule for neuron `i` in state `x`: flips the spin
according to the sign of the local field.
If the local field is zero, no change is made.
-/
noncomputable def update (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : HopfieldState n :=
  fun j =>
    if j = i then
      let lf := localField net x i
      if 0 < lf then SpinState.up
      else if lf < 0 then SpinState.down
      else x i
    else x j

/--
`UpdateSeq net x` is an inductive type representing a sequence of
asynchronous updates on the Hopfield network `net` starting from state `x`.
-/
inductive UpdateSeq {n : ℕ} (net : HopfieldNetwork n) : HopfieldState n → Type
  | nil : (x : HopfieldState n) → UpdateSeq net x
  | cons : (x : HopfieldState n) → (i : Fin n) → UpdateSeq net (update net x i) → UpdateSeq net x

namespace UpdateSeq
/--
Extract the final state from an update sequence.
-/
noncomputable def target {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n}
  : UpdateSeq net x → HopfieldState n
  | nil x => x
  | cons _ _ s => s.target

end UpdateSeq

/--
`IsFixedPoint net x` means `x` is stable under single-neuron updates;
no single asynchronous update changes the state.
-/
def IsFixedPoint {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n) : Prop :=
  ∀ i, update net x i = x

lemma isFixedPoint_iff_localField_sign (net : HopfieldNetwork n) (x : HopfieldState n) :
  IsFixedPoint net x ↔ ∀ i, (0 < localField net x i ↔ x i = SpinState.up) ∧ (localField net x i < 0 ↔ x i = SpinState.down) := by
  constructor
  · -- (→) direction
    intro hfp i
    constructor
    · -- Handle positive local field case
      constructor
      · intro h_pos
        have := hfp i
        unfold update at this
        simp [h_pos] at this
        have : x i = SpinState.up := by
          have h_at_i := congr_fun this i
          simp [h_pos] at h_at_i
          exact id (Eq.symm h_at_i)
        exact this
      · intro h_up
        by_contra h
        push_neg at h
        have := hfp i
        unfold update at this
        by_cases h_neg : localField net x i < 0
        · simp [h_neg] at this
          let this_i := congr_fun this i
          simp at this_i
          rw [h_up] at this_i
          simp_all only [ite_eq_left_iff, not_lt, reduceCtorEq, imp_false, not_true_eq_false]
        · have h_nonpos : localField net x i ≤ 0 := by linarith
          have h_zero : localField net x i = 0 := by linarith
          have h_eq : update net x i = x := hfp i
          unfold update at h_eq
          simp [h_zero] at h_eq
          -- Since x i = SpinState.up (from h_up) and local field is 0,
          -- this contradicts the fixed point property
          have h_at_i := congr_fun h_eq i
          simp [h_zero] at h_at_i
          -- The state should be unchanged when local field is 0, contradicting our assumption
          exact SpinState.up_down_distinct
          exact SpinState.up_down_distinct h_state
    · -- Handle negative local field case
      constructor
      · intro h_neg
        have := hfp i
        unfold update at this
        simp [h_neg] at this
        have h_at_i := congr_fun this i
        simp [h_neg] at h_at_i
        rw [if_neg (not_lt_of_lt h_neg)] at h_at_i
        exact Eq.symm h_at_i
      · intro h_down
        by_contra h
        push_neg at h
        have := hfp i
        unfold update at this
        by_cases h_pos : 0 < localField net x i
        · simp [h_pos] at this
          have h_eq := congr_fun this i
          simp [h_pos] at h_eq
          have h_not : SpinState.up ≠ x i := by
            intro h_contra
            rw [h_down] at h_contra
            exact SpinState.up_down_distinct (by rw [h_contra])
          exact absurd h_eq h_not
        · have h_nonpos : localField net x i ≤ 0 := by linarith
          have h_zero : localField net x i = 0 := by linarith
          have h_fixed := hfp i
          unfold update at h_fixed
          simp [h_zero] at h_fixed
          have h_at_i := congr_fun h_fixed i
          simp [h_zero] at h_at_i
          rw [h_down] at h_at_i
          -- When local field is 0 and current state is down,
          -- the update should change it to up
          exact SpinState.up_down_distinct (Eq.symm h_at_i)
  · -- (←) direction
    intro h i
    funext j
    have h_i := h i
    by_cases hj : j = i
    · -- Case j = i
      subst hj
      unfold update
      by_cases h_pos : 0 < localField net x j
      · simp [h_pos]
        aesop
      · by_cases h_neg : localField net x j < 0
        · simp [h_neg]
          aesop
        · have h_zero : localField net x j = 0 := by linarith
          simp [h_zero]
    · -- Case j ≠ i
      unfold update
      simp [hj]


/--
A state `x` converges to a fixed point `p` if there is an update
sequence from `x` that terminates at `p`, and `p` is a fixed point.
-/
def converges_to' {n : ℕ} (net : HopfieldNetwork n) (x p : HopfieldState n) : Prop :=
  ∃ (seq : UpdateSeq net x), seq.target = p ∧ IsFixedPoint net p

/--
The overlap measures similarity between two states by taking
the dot product of their corresponding ±1 vectors.
-/
def overlap (x y : HopfieldState n) : ℝ :=
  ∑ i : Fin n, (x i).toReal * (y i).toReal

lemma real_vector_sq_one (x : HopfieldState n) (i : Fin n) : (x i).toReal * (x i).toReal = 1 := by cases x i <;> simp [SpinState.toReal]

@[simp]
lemma overlap_self (x : HopfieldState n) :
    overlap x x = n :=
  calc
    overlap x x = ∑ i : Fin n, (x i).toReal * (x i).toReal := by rw [overlap]
    _ = ∑ i : Fin n, 1 := by simp [real_vector_sq_one x]
    _ = n := by simp


/--
`ContentAddressableMemory` wraps a `HopfieldNetwork` and a finite set of
stored patterns with a threshold criterion guaranteeing pattern completion.
-/
structure ContentAddressableMemory (n : ℕ) : Type where
  network : HopfieldNetwork n
  patterns : Finset (HopfieldState n)
  threshold : ℝ
  completes :
    ∀ p ∈ patterns, ∀ x : HopfieldState n,
      overlap x p ≥ threshold →
      ∃ y : HopfieldState n,
        IsFixedPoint network y ∧ overlap y p = (n : ℝ)

/--
Convenience coercion from `ContentAddressableMemory` to its underlying `HopfieldNetwork`.
-/
instance contentAddressableMemoryToHopfieldNetwork {n : ℕ} :
    Coe (ContentAddressableMemory n) (HopfieldNetwork n) where
  coe c := c.network
