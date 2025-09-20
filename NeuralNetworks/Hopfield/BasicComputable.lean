/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

open Matrix.IsHermitian

variable {n : ℕ}

/-!
# Hopfield Networks Formalization - Computable

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
    · simp
    · simp

end SpinState

/--
A Hopfield state for `n` neurons is a function from `Fin n` to `SpinState`.
-/
def HopfieldState (n : ℕ) := Fin n → SpinState

namespace HopfieldState

open SpinState

@[ext]
lemma hopfieldState_ext {x y : HopfieldState n} (h : ∀ i, x i = y i) : x = y := funext h

instance {n : ℕ} : DecidableEq (HopfieldState n) :=
  fun x y => decidable_of_iff (∀ i, x i = y i) ⟨hopfieldState_ext, fun h i => by rw [h]⟩

variable {n : ℕ}

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.
-/
instance : MetricSpace (HopfieldState n) where
  dist := fun x y => (Finset.card {i | x i ≠ y i} : ℝ)
  dist_self := by simp
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
    grind only [= Finset.mem_filter]

/--
Convert a Hopfield state to a real vector of dimension `n`, where
each coordinate is either `+1` or `-1`.
-/
def toRealVector {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [CharZero α] (x : HopfieldState n) : Fin n → α :=
  fun i => (if x i = SpinState.up then 1 else -1)

@[simp]
lemma toRealVector_apply {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (x : HopfieldState n) (i : Fin n) :
  x.toRealVector i = (x i).toReal := rfl

/--
`HopfieldNetwork` consists of:
1. A real-valued weight matrix `weights` of size `n × n`, which is Hermitian (symmetric in ℝ)
   and has zero diagonal.
2. A threshold vector `thresholds` with one real value per neuron.
-/
structure HopfieldNetwork (α : Type*) [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] (n : ℕ) where
  weights : {M : Matrix (Fin n) (Fin n) α // M.IsHermitian ∧ Matrix.diag M = 0}
  thresholds : Fin n → α

/--
Convenience accessor for the underlying weights matrix.
-/
def weightsMatrix {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] (net : HopfieldNetwork α n) : Matrix (Fin n) (Fin n) α := net.weights.val

@[simp]
lemma weights_symmetric {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α]
  (h_star_triv : ∀ a : α, star a = a) (net : HopfieldNetwork α n) :
  Matrix.IsSymm (weightsMatrix net) := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  have h := net.weights.prop.1
  simp only [Matrix.IsHermitian] at h
  have eq1 : (Matrix.transpose (weightsMatrix net)) i j = (weightsMatrix net) j i := by
    rfl
  have eq2 : (weightsMatrix net) j i = (weightsMatrix net) i j :=
    by rw [← h_star_triv ((weightsMatrix net) j i)]; erw [apply h i j]; exact rfl
  simp only [weightsMatrix] at *
  rw [← eq1, ← eq2]
  exact eq1

@[simp]
lemma weights_hermitian {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] (net : HopfieldNetwork α n) :
  (weightsMatrix net).IsHermitian := net.weights.prop.1

@[simp]
lemma weights_diag_zero {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] (net : HopfieldNetwork α n) :
  Matrix.diag (weightsMatrix net) = 0 := net.weights.prop.2

/--
Energy function of the Hopfield network for a given state `x`.
Typical Hopfield energy: `E(x) = -1/2 xᵀWx - bᵀx`.
-/
def energy
{α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
  (net : HopfieldNetwork α n) (x : HopfieldState n) : α :=
  let xVec := toRealVector x
  let W := weightsMatrix net
  let B := Matrix.toBilin' W;
  -((0.5 : α) * (B xVec xVec)) - Finset.sum Finset.univ (fun i => net.thresholds i * xVec i)

/--
Equivalent definition aimed at making the energy function more computationally friendly
(using the vector dot product ⬝ᵥ)
-/
def energy' {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    (net : HopfieldNetwork α n) (x : HopfieldState n) : α :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -((0.5 : α) * (B xVec xVec)) - (fun i => net.thresholds i) ⬝ᵥ xVec

/--
Proof that the two energy functions are equivalent
-/
lemma energy_eq_energy' {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
 (net : HopfieldNetwork α n) (x : HopfieldState n) :
  energy net x = energy' net x := by
  let xVec := toRealVector (α := α) x
  let W := weightsMatrix net
  let B := Matrix.toBilin' W
  rfl

/--
Local field (net input) for neuron `i` in state `x`,
`(Wx)_i - threshold[i]`.
-/
def localField {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α] (net : HopfieldNetwork α n) (x : HopfieldState n) (i : Fin n) : α :=
  (weightsMatrix net).mulVec (toRealVector x) i - net.thresholds i

/--
Asynchronous update rule for neuron `i` in state `x`: flips the spin
according to the sign of the local field.
If the local field is zero, no change is made.
-/
def updateState {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α] (net : HopfieldNetwork α n) (x : HopfieldState n) (i : Fin n) : HopfieldState n :=
  Function.update x i $
    let lf := localField net x i
    if 0 < lf then SpinState.up
    else if lf < 0 then SpinState.down
    else x i

/--
`UpdateSeq net x` is an inductive type representing a sequence of
asynchronous updates on the Hopfield network `net` starting from state `x`.
-/
inductive UpdateSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} (net : HopfieldNetwork α n) : HopfieldState n → Type
  | nil : (x : HopfieldState n) → UpdateSeq net x
  | cons : (x : HopfieldState n) → (i : Fin n) → UpdateSeq net (updateState net x i) → UpdateSeq net x
/--
Defines a function to generate a specific UpdateSeq
-/
def updateSeqOfList {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    (net : HopfieldNetwork α n) (x : HopfieldState n) (l : List (Fin n)) : HopfieldState.UpdateSeq net x :=
     match l with
     | [] => HopfieldState.UpdateSeq.nil x
     | i :: is => HopfieldState.UpdateSeq.cons x i (updateSeqOfList net (updateState net x i) is)
namespace UpdateSeq

/--
Get the length of an update sequence.
-/
def length {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} {net : HopfieldNetwork α n} {x : HopfieldState n} : UpdateSeq net x → ℕ
  | nil _ => 0
  | cons _ _ s => s.length + 1
/--
Extract the final state from an update sequence.
-/
def target {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} {net : HopfieldNetwork α n} {x : HopfieldState n}
  : UpdateSeq net x → HopfieldState n
  | nil x => x
  | cons _ _ s => s.target
/--
A state `x` is a fixed point under `net` if no single-neuron update changes the state.
-/
def isFixedPoint {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α]
    {n : ℕ} (net : HopfieldNetwork α n) (x : HopfieldState n) : Prop :=
  ∀ i, updateState net x i = x
/--
Decidability of fixed points.
-/
instance {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α]
    {n : ℕ} {net : HopfieldNetwork α n} {x : HopfieldState n} : Decidable (HopfieldState.UpdateSeq.isFixedPoint net x) :=
  by
  unfold HopfieldState.UpdateSeq.isFixedPoint
  have : DecidablePred fun i => updateState net x i = x := by
    intro i
    exact decEq (updateState net x i) x
  apply Fintype.decidableForallFintype
/--
A state `x` converges to a fixed point `p` if there is an update
sequence from `x` that terminates at `p`, and `p` is a fixed point.
-/
def convergesTo {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} (net : HopfieldNetwork α n) (x p : HopfieldState n) : Prop :=
  ∃ (seq : UpdateSeq net x), seq.target = p ∧ isFixedPoint net p


/--
Bounded convergence: There exists an update sequence from `x` that terminates at `p`,
`p` is a fixed point, and the sequence length is at most `maxSteps`.
-/
def convergesToBounded {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} (net : HopfieldNetwork α n) (x p : HopfieldState n) (maxSteps : ℕ) : Prop :=
  ∃ (seq : HopfieldState.UpdateSeq net x), seq.target = p ∧ HopfieldState.UpdateSeq.isFixedPoint net p ∧
      -- Add a condition on the length of the sequence
      seq.length ≤ maxSteps

/-
Decidability of bounded convergence
-/
noncomputable instance {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} {net : HopfieldNetwork α n} {x p : HopfieldState n} {maxSteps : ℕ} :
    Decidable (convergesToBounded net x p maxSteps) := by
  classical
  exact inferInstance

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

/-
The overlap function is symmetric.
-/
lemma overlap_comm (x y : HopfieldState n) : overlap x y = overlap y x := by
  simp [overlap, mul_comm]

/-
The overlap function is related to the Hamming distance.
-/
lemma overlap_and_distance {n : ℕ} (x y : HopfieldState n) :
  overlap x y = (n : ℝ) - 2 * dist x y := by
  rw [overlap, dist]
  have h : ∀ i, (x i).toReal * (y i).toReal = 1 - 2 * if x i ≠ y i then 1 else 0 := by
    intro i
    cases x i <;> cases y i <;> simp [SpinState.toReal] <;> norm_num
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp [Finset.card_univ]
  rw [@Fin.sum_univ_def]
  rw [@List.sum_map_ite]
  simp only [List.map_const', List.sum_replicate, smul_zero, decide_not, nsmul_eq_mul, zero_add]
  norm_cast
  ring_nf
  have : (List.filter (fun a => !decide (x a = y a)) (List.finRange n)).length =
         (Finset.filter (fun i => x i ≠ y i) Finset.univ).card := by
    simp only [ne_eq]
    congr
    ext i
    simp only
    simp only [decide_not]
  rw [this]
  simp [PseudoMetricSpace.toDist]
  exact rfl

/--
A type representing a selection function that chooses which neuron to update next.
-/
def NeuronSelector (n : ℕ) := HopfieldState n → Option (Fin n)

/--
A random update rule that uses a selector to choose which neuron to update.
Returns None if no update is needed or possible.
-/
def randomUpdate {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α]
    {n : ℕ} (net : HopfieldNetwork α n) (selector : NeuronSelector n)
    (x : HopfieldState n) : Option (HopfieldState n) := do
  let i ← selector x
  let x' := updateState net x i
  return x'

/-
`ContentAddressableMemory` wraps a `HopfieldNetwork` and a finite set of
stored patterns with a threshold criterion guaranteeing pattern completion.
-/
universe u

structure ContentAddressableMemory {α : Type u} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [CharZero α]
    (n : ℕ) : Type (u+1) where
  /-- The underlying Hopfield network used for pattern storage and recall. -/
  network : HopfieldNetwork α n
  /-- The set of stored patterns that can be recalled. -/
  patterns : Finset (HopfieldState n)
  /-- The overlap threshold required for pattern completion. -/
  threshold : ℝ
  completes :
    ∀ p ∈ patterns, ∀ x : HopfieldState n,
      overlap x p ≥ threshold →
      ∃ y : HopfieldState n,
        isFixedPoint network y ∧ overlap y p = (n : ℝ)

/--
Convenience coercion from `ContentAddressableMemory` to its underlying `HopfieldNetwork`.
-/
instance contentAddressableMemoryToHopfieldNetwork {α : Type u} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Star α] [InvolutiveStar α] [CharZero α]
    {n : ℕ} :
    Coe (ContentAddressableMemory (α := α) n) (HopfieldNetwork α n) where
  coe c := c.network


end UpdateSeq
end HopfieldState
