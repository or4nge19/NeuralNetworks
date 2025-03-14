import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.Algebra.Star.Subalgebra
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

**Refinement:**  Using `ℤ₂` directly or `Bool` might be more idiomatic in Mathlib. However, `SpinState` as a separate inductive type improves readability in this domain. We can still leverage the isomorphism to `ℤ₂` or `Bool` for operations if needed.
-/
inductive SpinState : Type
  | up : SpinState
  | down : SpinState
  deriving DecidableEq, Inhabited, Fintype

namespace SpinState

/--
Map `SpinState` to real numbers: `up ↦ 1`, `down ↦ -1`.

**Refinement:**  Using `1` and `-1` directly as literals is clearer than `if s = up then 1 else -1`.
-/
def toReal : SpinState → ℝ
  | up => 1
  | down => -1

/--
`SpinState` forms a commutative group under multiplication,
with `up` as the identity element. This group is isomorphic to `ℤ₂`.

**Refinement:** While mathematically correct, defining a custom `CommGroup` instance for such a simple type is verbose.  It's better to leverage the isomorphism to `Multiplicative (ZMod 2)` or even directly use `Multiplicative Bool` or `Multiplicative (Fin 2)`.  However, for pedagogical purposes and to maintain the `SpinState` abstraction, we can keep it but simplify the proof using `equiv_zmod2_group`.

**Further Refinement:** Let's use `Multiplicative Bool` which is already in Mathlib and isomorphic to ℤ₂. We can define conversions to and from `SpinState`. This is more Mathlib-friendly.
-/
instance : MulOneClass SpinState where
  mul := fun s₁ s₂ => ofBool (xor (toBool s₁) (toBool s₂)) -- Corrected multiplication
  one := up

instance : CommSemigroup SpinState where
  mul_assoc := by
    intros a b c
    simp [mul, toBool, ofBool, Bool.xor_assoc]
  mul_comm := by
    intros a b
    simp [mul, toBool, ofBool, Bool.xor_comm]

instance : OneHomClass SpinState SpinState where
  one_hom_one := rfl
  one_hom_mul _ _ := rfl

instance : Monoid SpinState where
  one_mul := by
    intro a
    simp [mul, one, toBool, ofBool]
  mul_one := by
    intro a
    simp [mul, one, toBool, ofBool]

instance : CommMonoid SpinState := { SpinState.Monoid, SpinState.CommSemigroup with }

instance : InvolutiveInv SpinState where
  inv := id
  inv_inv := id

instance : DivInvMonoid SpinState := { SpinState.Monoid, SpinState.InvolutiveInv with }

instance : CommGroup SpinState := { SpinState.CommMonoid, SpinState.DivInvMonoid with }

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
    simp [toBool, mul, ofBool]
  · -- up.down case
    simp [toBool, mul, ofBool]
  · -- down.up case
    simp [toBool, mul, ofBool]
  · -- down.down case
    simp [toBool, mul, ofBool]
    simp [Bool.xor_def]

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

**Refinement:**  `HopfieldState n` is just a vector type. We could consider using `Vector SpinState n` if fixed size vectors are beneficial, or keep `Fin n → SpinState` which is mathematically cleaner for functions.
-/
def HopfieldState (n : ℕ) := Fin n → SpinState

namespace HopfieldState

open SpinState
open Matrix hiding IsSymm IsHermitian diag mulVec vecMul dotProduct toBilin' toBilin'_apply'
open BigOperators
open Finset

variable {n : ℕ}

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.

**Refinement:**  The `MetricSpace` instance is good.  The distance should probably be a natural number (`ℕ`) representing the count, then cast to `ℝ` for the `MetricSpace` structure.  Using `NNReal` might also be appropriate for distances.

**Further Refinement:** Let's keep `ℝ` as the codomain of `dist` for `MetricSpace`, but cast from `Nat` after computing the cardinality. The `dist_triangle` proof can be simplified using `Nat.cast_add_le`.
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
    let diff_xz := {i | x i ≠ z i}
    let diff_xy := {i | x i ≠ y i}
    let diff_yz := {i | y i ≠ z i}
    have h : diff_xz ⊆ diff_xy ∪ diff_yz := by
      intro i hi
      simp at *
      by_contra h'
      push_neg at h'
      exact hi (h'.1 ▸ h'.2 ▸ rfl)
    calc dist x z = Nat.cast (card diff_xz)
      ≤ Nat.cast (card (diff_xy ∪ diff_yz)) := by gcongr; apply card_le_card h
      _ ≤ Nat.cast (card diff_xy + card diff_yz) := by
         rw [Nat.cast_add]
         apply Nat.cast_le.2
         apply card_union_le
      _ = dist x y + dist y z := by rw [dist, dist]; rfl
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

**Refinement:**  Using a subtype `{M : Matrix ... // ...}` is a good way to represent the constraints.  Alternatively, we could define a predicate `IsHopfieldWeights` and use that.  The subtype approach is generally preferred in Mathlib for bundling data with properties.
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
  Matrix.IsSymm (weightsMatrix net) := Matrix.IsHermitian.isSymm net.weights.prop.1

@[simp]
lemma weights_hermitian (net : HopfieldNetwork n) :
  (weightsMatrix net).IsHermitian := net.weights.prop.1

@[simp]
lemma weights_diag_zero (net : HopfieldNetwork n) :
  Matrix.diag (weightsMatrix net) = 0 := net.weights.prop.2

/--
A `QuadraticForm` given by `x ↦ xᵀ W x`, where `W` is a symmetric matrix over `ℝ`.
This directly constructs the quadratic form from the matrix using the dot product
of x with Wx.

The hypothesis `(h_symm : W.IsHermitian)` ensures that the matrix is symmetric.

**Refinement:**  The construction of `hopfieldQuadraticForm` is quite verbose, especially the `exists_companion'` proof. We should try to simplify this using existing Mathlib tools for quadratic forms and bilinear forms from matrices.  Since `W` is symmetric, the associated bilinear form `B(x, y) = xᵀ W y` is symmetric, and we can directly use `QuadraticForm.ofBilinearForm` if we can show the bilinear form is symmetric.

**Further Refinement:**  Let's use `BilinearForm.toQuadraticForm` and leverage the symmetry of `W`. We can define a bilinear form from `W` and then convert it to a quadratic form. The symmetry condition is already part of `HopfieldNetwork` definition.  The `sorry` in the original code is in the `exists_companion'` proof, which we should be able to avoid now.
-/
def hopfieldQuadraticForm {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : W.IsHermitian) : -- Removed diag condition from type as it's not needed for QuadraticForm itself
    QuadraticForm ℝ (Fin n → ℝ) :=
  by exact W.toQuadraticMap'

lemma hopfieldQuadraticForm_apply {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : W.IsHermitian) (x : Fin n → ℝ) :
  (hopfieldQuadraticForm W h_symm).toFun x = x ⬝ᵥ (W.mulVec x) :=
by
  unfold hopfieldQuadraticForm BilinearForm.toQuadraticForm Matrix.toBilin'
  rfl

/--
Energy function of the Hopfield network for a given state `x`.
Typical Hopfield energy: `E(x) = -1/2 xᵀWx - bᵀx`.
-/
def energy (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let Q := hopfieldQuadraticForm W net.weights.prop.1; -- Pass Hermitian property
  let lin := Basis.mk n ℝ net.thresholds; -- Use LinearForm for threshold term
  -0.5 * Q xVec - lin xVec

/-
Equivalent definition aimed at making the energy function more computationally friendly
(using the vector dot product ⬝ᵥ)

**Refinement:** `energy'` is already quite close to the most direct form. Let's keep `energy` and remove `energy'` and `energy''` for now, as `energy` with `hopfieldQuadraticForm` and `LinearForm` is already a good abstraction. If needed, we can add back a more explicit dot product version later but for now, clarity is better than multiple equivalent definitions.
-/

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

**Refinement:** The update rule logic is clear. `noncomputable` is likely needed because of the use of `Classical.propDecidable` in the decidability instance later. We can keep the definition as is.
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

**Refinement:**  `UpdateSeq` is a reasonable way to represent update sequences.  We can keep it as is for now.
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
Get the length of an update sequence.
-/
noncomputable def length {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n} : UpdateSeq net x → ℕ
  | nil _ => 0
  | cons _ _ s => s.length + 1

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
noncomputable instance {n : ℕ} {net : HopfieldNetwork n} {x : HopfieldState n} : Decidable (HopfieldState.UpdateSeq.isFixedPoint net x) :=
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

/-
Since convergesTo is undecidable in general, we define a bounded version-/
def convergesToBounded {n : ℕ} (net : HopfieldNetwork n) (x p : HopfieldState n) (maxSteps : ℕ) : Prop :=
  ∃ (seq : HopfieldState.UpdateSeq net x), seq.target = p ∧ HopfieldState.UpdateSeq.isFixedPoint net p ∧
      -- Add a condition on the length of the sequence
      seq.length ≤ maxSteps
/-
Decidability of bounded convergence
-/
noncomputable instance {n : ℕ} {net : HopfieldNetwork n} {x p : HopfieldState n} {maxSteps : ℕ} :
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
  have : ∀ i, (2 : ℝ) * (if x i ≠ y i then 1 else 0) = (if x i ≠ y i then 2 else 0) := by
    intro i; split_ifs <;> simp
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
    simp only [List.mem_filter, List.mem_finRange, Fin.val_eq_val, true_and]
    simp only [decide_not]
  rw [this]
  simp [PseudoMetricSpace.toDist]
  exact rfl

/- TODO :

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
