import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

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
a commutative group structure isomorphic to `ℤ₂` under multiplication.
-/
inductive SpinState : Type
  | up : SpinState
  | down : SpinState
  deriving DecidableEq, Inhabited, Fintype

namespace SpinState

/--
Map `SpinState` to real numbers: `up ↦ 1`, `down ↦ -1`.
-/
def toReal (s : SpinState) : ℝ := if s = up then 1 else -1

/--
`SpinState` forms a commutative group under multiplication,
with `up` as the identity element. This group is isomorphic to `ℤ₂`.
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
  inv_mul_cancel := by intro a; cases a <;> rfl

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

@[simp]
lemma mul_toBool (s₁ s₂ : SpinState) : (s₁ * s₂).toBool = (s₁.toBool = s₂.toBool) := by
  cases s₁ <;> cases s₂
  · -- up.up case
    simp [toBool]
  · -- up.down case
    simp [toBool]
  · -- down.up case
    simp [toBool]
  · -- down.down case
    simp [toBool]

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
def spinStateEquivZmod2 : SpinState ≃ ZMod 2 where
  toFun := fun s => match s with | up => 1 | down => 0
  invFun := fun z => if z = 1 then up else down
  left_inv := by intro s; cases s <;> simp
  right_inv := by
    intro z
    fin_cases z
    · simp [SpinState.down]
    · simp [SpinState.up]

end SpinState

/--
A Hopfield state for `n` neurons is a function from `Fin n` to `SpinState`.
-/
def HopfieldState (n : ℕ) := Fin n → SpinState

namespace HopfieldState

open SpinState

variable {n : ℕ}

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.
-/
instance : MetricSpace (HopfieldState n) where
  dist := fun x y => (Finset.card {i | x i ≠ y i} : ℝ)
  dist_self := by simp [Finset.card_eq_zero]
  dist_comm := by
    intro x y
    simp
    congr
    ext i
    exact ne_comm
  dist_triangle := by
    intro x y z
    simp
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
    simp [Finset.card_eq_zero] at h
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
def energy (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - Finset.sum Finset.univ (fun i => net.thresholds i * xVec i)

/--
Equivalent definition aimed at making the energy function more computationally friendly
(using the vector dot product ⬝ᵥ)
-/
def energy' (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - (fun i => net.thresholds i) ⬝ᵥ xVec

/--
Proof that the two energy functions are equivalent
-/
lemma energy_eq_energy' (net : HopfieldNetwork n) (x : HopfieldState n) : energy net x = energy' net x := by
  let xVec := toRealVector x
  let W := weightsMatrix net
  let B := Matrix.toBilin' W
  rfl

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
noncomputable def updateState (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : HopfieldState n :=
  Function.update x i $
    let lf := localField net x i
    if 0 < lf then SpinState.up
    else if lf < 0 then SpinState.down
    else x i

/--
`UpdateSeq net x` is an inductive type representing a sequence of
asynchronous updates on the Hopfield network `net` starting from state `x`.
-/
inductive UpdateSeq {n : ℕ} (net : HopfieldNetwork n) : HopfieldState n → Type
  | nil : (x : HopfieldState n) → UpdateSeq net x
  | cons : (x : HopfieldState n) → (i : Fin n) → UpdateSeq net (updateState net x i) → UpdateSeq net x

/--
Defines a function to generate a specific UpdateSeq
-/
noncomputable
def updateSeqOfList (net : HopfieldNetwork n) (x : HopfieldState n) (l : List (Fin n)) : HopfieldState.UpdateSeq net x :=
     match l with
     | [] => HopfieldState.UpdateSeq.nil x
     | i :: is => HopfieldState.UpdateSeq.cons x i (updateSeqOfList net (updateState net x i) is)

namespace UpdateSeq
/--
Extract the final state from an update sequence.
-/
noncomputable def target {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n}
  : UpdateSeq net x → HopfieldState n
  | nil x => x
  | cons _ _ s => s.target

/--
A state `x` is a fixed point under `net` if no single-neuron update changes the state.
-/
def isFixedPoint {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n) : Prop :=
  ∀ i, updateState net x i = x

/--
Decidability of fixed points.
-/
noncomputable
instance {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n} : Decidable (HopfieldState.UpdateSeq.isFixedPoint net x) :=
  by
  unfold HopfieldState.UpdateSeq.isFixedPoint
  have : DecidablePred fun i => updateState net x i = x := by
    intro i
    exact Classical.propDecidable ((fun i ↦ updateState net x i = x) i)
  apply Fintype.decidableForallFintype

/--
A state `x` converges to a fixed point `p` if there is an update
sequence from `x` that terminates at `p`, and `p` is a fixed point.
-/
def convergesTo {n : ℕ} (net : HopfieldNetwork n) (x p : HopfieldState n) : Prop :=
  ∃ (seq : UpdateSeq net x), seq.target = p ∧ isFixedPoint net p

/--
The overlap measures similarity between two states by taking
the dot product of their corresponding ±1 vectors.
-/
def overlap (x y : HopfieldState n) : ℝ :=
  ∑ i : Fin n, (x i).toReal * (y i).toReal

lemma real_vector_sq_one (x : HopfieldState n) (i : Fin n) : (x i).toReal * (x i).toReal = 1 := by
  cases x i <;> simp [SpinState.toReal]

@[simp]
lemma overlap_self (x : HopfieldState n) :
    overlap x x = n :=
  calc
    overlap x x = ∑ i : Fin n, (x i).toReal * (x i).toReal := by rw [overlap]
    _ = ∑ i : Fin n, 1 := by simp [real_vector_sq_one x]
    _ = n := by simp

lemma overlap_comm (x y : HopfieldState n) : overlap x y = overlap y x := by
  simp [overlap, mul_comm]

/- TODO :
  -- Relate the overlap function to the Hamming distance.
  -- Define a bounded version of convergesTo with a maximum
     sequence length and provide decidability instance
  -- Consider an alternative, equivalent formulation of the
     update rule, based on a function that chooses a random neuron to update.
-/
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
        isFixedPoint network y ∧ overlap y p = (n : ℝ)

/--
Convenience coercion from `ContentAddressableMemory` to its underlying `HopfieldNetwork`.
-/
instance contentAddressableMemoryToHopfieldNetwork {n : ℕ} :
    Coe (ContentAddressableMemory n) (HopfieldNetwork n) where
  coe c := c.network

end UpdateSeq
end HopfieldState
