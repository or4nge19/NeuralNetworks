import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

set_option maxHeartbeats 0

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
  cases s₁ <;> cases s₂ <;> simp [toBool]

/--
If two spin states have the same real value, they must be equal.
-/
@[simp]
lemma eq_of_toReal_eq {s₁ s₂ : SpinState} (h : s₁.toReal = s₂.toReal) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> try rfl
  all_goals { simp [toReal] at h; norm_num at h }

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
  right_inv := by intro z; fin_cases z <;> simp [SpinState.down, SpinState.up]

end SpinState

/--
A Hopfield state for `n` neurons is a function from `Fin n` to `SpinState`.
-/
def HopfieldState (n : ℕ) := Fin n → SpinState

namespace HopfieldState

open SpinState
open LinearMap

variable {n : ℕ}

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.
-/
instance : MetricSpace (HopfieldState n) where
  dist := fun x y => (Finset.card {i | x i ≠ y i} : ℝ)
  dist_self := by simp [Finset.card_eq_zero]
  dist_comm := by intro x y; simp; congr; ext i; exact ne_comm
  dist_triangle := by
    intro x y z
    simp
    have : Finset.filter (fun i => x i ≠ z i) Finset.univ ⊆
          Finset.filter (fun i => x i ≠ y i) Finset.univ ∪
          Finset.filter (fun i => y i ≠ z i) Finset.univ := by
      intro i hi; simp at *; by_contra h; push_neg at h; have h1 := h.1; have h2 := h.2
      have : x i = y i := by by_contra hxy; exact hxy h1
      have : y i = z i := by by_contra hyz; exact hyz h2
      have : x i = z i := Eq.trans h1 h2; exact hi this
    calc (Finset.card (Finset.filter (fun i => x i ≠ z i) Finset.univ) : ℝ)
      ≤ Finset.card (Finset.filter (fun i => x i ≠ y i) Finset.univ ∪
                     Finset.filter (fun i => y i ≠ z i) Finset.univ) :=
        Nat.cast_le.mpr (Finset.card_le_card this)
      _ ≤ Finset.card {i | x i ≠ y i} + Finset.card {i | y i ≠ z i} := by
        rw [←Nat.cast_add]; apply Nat.cast_le.2; apply Finset.card_union_le
  eq_of_dist_eq_zero := by
    intro x y h; simp [Finset.card_eq_zero] at h; funext i; by_contra h'
    have : i ∈ Finset.filter (fun i => x i ≠ y i) Finset.univ := by simp [h']
    have : i ∈ (∅ : Finset (Fin n)) := by rw [← h]; exact this
    simp at this

/--
Convert a Hopfield state to a real vector of dimension `n`, which is in `EuclideanSpace ℝ n`
each coordinate is either `+1` or `-1`.
-/
def toRealVector (x : HopfieldState n) : EuclideanSpace ℝ (Fin n) :=
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

/--
Convenience accessor for the BilinearForm of the weights matrix.
-/
@[simp]
def weightsBilinForm (net : HopfieldNetwork n) :
    LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
  Matrix.toBilin' (weightsMatrix net)

@[simp]
lemma weights_symmetric (net : HopfieldNetwork n) :
  Matrix.IsSymm (weightsMatrix net) := net.weights.prop.1

@[simp]
lemma weights_hermitian (net : HopfieldNetwork n) :
  (weightsMatrix net).IsHermitian := net.weights.prop.1

@[simp]
lemma weights_diag_zero (net : HopfieldNetwork n) :
  Matrix.diag (weightsMatrix net) = 0 := net.weights.prop.2

open scoped BigOperators


open Matrix
open scoped BigOperators

variable {n : ℕ}
variable (W : Matrix (Fin n) (Fin n) ℝ)
variable (x y : Fin n → ℝ)

/--
A small helper lemma showing that
∑ i, ∑ j, x i * W i j * y j = x ⬝ᵥ W.mulVec y.
-/
@[simp]
lemma sum_eq_dot :
    ∑ i, ∑ j, x i * W i j * y j = x ⬝ᵥ W.mulVec y := by
  -- Unfold the definitions
  simp only [Matrix.mulVec, dotProduct]

  -- Rewrite both sides into a more explicit form
  have h1 : ∑ i, ∑ j, x i * W i j * y j = ∑ i, x i * (∑ j, W i j * y j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

  have h2 : ∑ i, x i * (∑ j, W i j * y j) = x ⬝ᵥ W.mulVec y := by
    simp only [Matrix.mulVec, dotProduct]

  -- Chain the equalities
  rw [h1, h2]

@[simp]
lemma toBilin'_apply (x y : Fin n → ℝ) :
    (Matrix.toBilin' W) x y = x ⬝ᵥ W.mulVec y := by
  -- Unfold the definition of toBilin'
  simp only [Matrix.toBilin', Matrix.dotProduct_mulVec]
  -- Use the fact that Matrix.dotProduct_mulVec proves the identity
  rw [@BilinForm.toMatrix'_symm]
  rw [@toBilin'_apply']
  rw [@dotProduct_mulVec]

@[simp]
lemma hermitian_implies_symmetric :
    W.IsHermitian →
    W.diag = 0     →
    ∀ x y, (Matrix.toBilin' W) (x + y) (x + y) =
           (Matrix.toBilin' W) x x + (Matrix.toBilin' W) y y + 2 * (Matrix.toBilin' W) x y := by
  intros h_symm h_diag x y

  -- First, establish that the bilinear form respects the matrix multiplication
  have bilin_form_def : ∀ a b, (Matrix.toBilin' W) a b = a ⬝ᵥ W.mulVec b := by
    intro a b
    exact toBilin'_apply W a b

  -- Using the bilinear form definition for all components
  rw [bilin_form_def (x + y) (x + y)]
  rw [bilin_form_def x x]
  rw [bilin_form_def y y]
  rw [bilin_form_def x y]

  -- Expand the matrix multiplication and dot product
  simp only [Matrix.mulVec_add, dotProduct_add]

  -- For a real symmetric matrix W, we have y ⬝ᵥ W.mulVec x = x ⬝ᵥ W.mulVec y
  have symm_dot : y ⬝ᵥ W.mulVec x = x ⬝ᵥ W.mulVec y := by
    simp only [dotProduct, Matrix.mulVec]

    calc ∑ i, y i * (∑ j, W i j * x j)
        = ∑ i, ∑ j, y i * W i j * x j := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Finset.mul_sum]
          ring_nf
        _ = ∑ j, ∑ i, y i * W i j * x j := by
          rw [Finset.sum_comm]
        _ = ∑ j, ∑ i, x j * W j i * y i := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          -- Use Hermitian property (for real matrices, means symmetric)
          have h : W i j = W j i := by
            have h₁ := Matrix.IsHermitian.apply h_symm i j
            -- For real matrices, conjugate transpose is just transpose
            simp at h₁
            exact _root_.id (Eq.symm h₁)
          rw [h]
          ring
        _ = ∑ j, x j * (∑ i, W j i * y i) := by
          rw [@sum_eq_dot]
          exact rfl
        _ = x ⬝ᵥ W.mulVec y := by
          simp only [dotProduct, Matrix.mulVec]

  -- Complete the calculation with ring arithmetic
  ring_nf
  rw [← bilin_form_def]
  simp only [map_add, LinearMap.add_apply, toBilin'_apply, add_dotProduct]
  simp_all only [toBilin'_apply, implies_true]
  ring_nf


-- etc.


/--
A `QuadraticForm` given by `x ↦ xᵀ W x`, where `W` is a symmetric matrix over `ℝ`.
This directly constructs the quadratic form from the matrix using the dot product
of x with Wx.

The hypothesis `(h_symm : W.IsHermitian)` ensures that the matrix is symmetric,
and `h_diag` ensures the diagonal is zero.
-/
def hopfieldQuadraticForm {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : W.IsHermitian)
    (h_diag : Matrix.diag W = 0) :
    QuadraticForm ℝ (Fin n → ℝ) :=
  { toFun := fun x => x ⬝ᵥ (W.mulVec x)
    toFun_smul := by
      intro r x
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      exact Eq.symm (mul_assoc r r (x ⬝ᵥ W.mulVec x))
    exists_companion' := by
      use Matrix.toBilin' W
      intro x y

      -- First, establish the bilinear form definition
      have bilin_def : Matrix.toBilin' W x y = x ⬝ᵥ W.mulVec y := by
        simp [Matrix.toBilin'_apply]

      -- Prove symmetry using the Hermitian property
      have symm_dot : y ⬝ᵥ W.mulVec x = x ⬝ᵥ W.mulVec y := by
        simp only [dotProduct, Matrix.mulVec]

        calc ∑ i, y i * (∑ j, W i j * x j)
            = ∑ i, ∑ j, y i * W i j * x j := by
              apply Finset.sum_congr rfl
              intro i _
              simp [Finset.mul_sum]
              ring_nf
            _ = ∑ j, ∑ i, y i * W i j * x j := by
              rw [Finset.sum_comm]
            _ = ∑ j, ∑ i, x j * W j i * y i := by
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro i _
              have h : W i j = W j i := by
                have h₁ := Matrix.IsHermitian.apply h_symm i j
                simp at h₁
                exact _root_.id (Eq.symm h₁)
              rw [h]
              ring
            _ = x ⬝ᵥ W.mulVec y := by simp [dotProduct, Matrix.mulVec]

      -- Calculate each side
      simp [bilin_def]
      -- Expand (x + y) ⬝ᵥ W *ᵥ (x + y)
      -- After establishing symm_dot: y ⬝ᵥ W *ᵥ x = x ⬝ᵥ W *ᵥ y

      -- Calculate quadratic form for (x + y)
      have h1 : (x + y) ⬝ᵥ W *ᵥ (x + y) = (x + y) ⬝ᵥ (W *ᵥ x + W *ᵥ y) := by
        simp [Matrix.mulVec_add]

      -- Expand using dot product distributivity
      have h2 : (x + y) ⬝ᵥ (W *ᵥ x + W *ᵥ y) =
                x ⬝ᵥ (W *ᵥ x) + y ⬝ᵥ (W *ᵥ x) + x ⬝ᵥ (W *ᵥ y) + y ⬝ᵥ (W *ᵥ y) := by
        simp [dotProduct_add]
        ring_nf

      -- Use symmetry of the bilinear form
      have h3 : y ⬝ᵥ (W *ᵥ x) = x ⬝ᵥ (W *ᵥ y) := symm_dot

      -- We need to establish additional steps to make the calculation work properly
      have h_add : (x + y) ⬝ᵥ W *ᵥ (x + y) =
                   x ⬝ᵥ W *ᵥ (x + y) + y ⬝ᵥ W *ᵥ (x + y) := by simp [dotProduct_add]

      have h_x_distrib : x ⬝ᵥ W *ᵥ (x + y) = x ⬝ᵥ W *ᵥ x + x ⬝ᵥ W *ᵥ y := by
        simp [dotProduct, Matrix.mulVec_add]
        ring_nf
        exact Finset.sum_add_distrib

      have h_y_distrib : y ⬝ᵥ W *ᵥ (x + y) = y ⬝ᵥ W *ᵥ x + y ⬝ᵥ W *ᵥ y := by
        simp [dotProduct, Matrix.mulVec_add]
        ring_nf
        exact Finset.sum_add_distrib
      rw [h_x_distrib]; rw [h_y_distrib]; rw [← bilin_def]; rw [symm_dot]; simp only [toBilin'_apply]
      --rw [h1, h2]  -- Apply the first two expansions

      -- Now we have: x ⬝ᵥ (W *ᵥ x) + y ⬝ᵥ (W *ᵥ x) + x ⬝ᵥ (W *ᵥ y) + y ⬝ᵥ (W *ᵥ y)

      -- Use symmetry to replace y ⬝ᵥ (W *ᵥ x) with x ⬝ᵥ (W *ᵥ y)
      --rw [h3]
      rw [← symm_dot]
      rw [← @sum_eq_dot]
      -- Now we have: x ⬝ᵥ (W *ᵥ x) + x ⬝ᵥ (W *ᵥ y) + x ⬝ᵥ (W *ᵥ y) + y ⬝ᵥ (W *ᵥ y)
      -- Factor out the common term
      have h4 : x ⬝ᵥ (W *ᵥ y) + x ⬝ᵥ (W *ᵥ y) = 2 * (x ⬝ᵥ (W *ᵥ y)) := by ring
      --rw [h4]

      -- Now we have: x ⬝ᵥ (W *ᵥ x) + 2 * (x ⬝ᵥ (W *ᵥ y)) + y ⬝ᵥ (W *ᵥ y)
      --rw [← symm_dot]
      -- Rearrange terms
      rw [add_assoc]; simp [add_comm (2 * (x ⬝ᵥ (W *ᵥ y)))]
      -- Now we have: x ⬝ᵥ (W *ᵥ x) + y ⬝ᵥ (W *ᵥ y) + 2 * (x ⬝ᵥ (W *ᵥ y))
      rw [symm_dot]
      -- Finally, rewrite using bilin_def
      rw [← bilin_def]
      ring_nf
      simp
      rw [@mul_right_eq_iff_eq_mul_invOf]
      rw [@dotProduct_mulVec]
      simp [dotProduct_add]
      sorry
       }

/--
Helper lemma, this shows explicitly that
`hopfieldQuadraticForm W h_symm x = xᵀ W x` (the usual matrix product form).
-/
lemma hopfieldQuadraticForm_apply {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : W.IsHermitian) (h_diag : Matrix.diag W = 0) (x : EuclideanSpace ℝ (Fin n)) :
  (hopfieldQuadraticForm W h_symm h_diag).toFun x = x ⬝ᵥ (W.mulVec x) :=
by
  rw [hopfieldQuadraticForm]


/--
Energy function of the Hopfield network for a given state `x`.
Typical Hopfield energy: `E(x) = -1/2 xᵀWx - bᵀx`.
-/
noncomputable
def energy (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec : EuclideanSpace ℝ (Fin n) := toRealVector x
  let Q := hopfieldQuadraticForm (weightsMatrix net) (net.weights.prop.1) (net.weights.prop.2)
  let linear_thresholds := (fun i => net.thresholds i) ⬝ᵥ xVec;
  -0.5 * (Q xVec) - linear_thresholds

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
  let Q := hopfieldQuadraticForm (weightsMatrix net) (net.weights.prop.1) (net.weights.prop.2)

  unfold energy energy'

  -- The quadratic form evaluates to the dot product with the matrix
  have h1 : Q.toFun xVec = xVec ⬝ᵥ (W.mulVec xVec) := by
    exact hopfieldQuadraticForm_apply W (net.weights.prop.1) (net.weights.prop.2) xVec

  -- The bilinear form applied twice is the same as the dot product
  have h2 : B xVec xVec = xVec ⬝ᵥ (W.mulVec xVec) := by
    dsimp only [Matrix.toBilin'_apply]
    exact Matrix.toBilin'_apply' W xVec xVec

  -- Now we can complete the proof
  simp [h1, h2]
  exact mul_eq_mul_left_iff.mp rfl



/--
Definition of the energy function using a quadratic form.
-/
def energy'' (net : HopfieldNetwork n) (x : HopfieldState n) : ℝ :=
  let xVec : EuclideanSpace ℝ (Fin n) := toRealVector x
  let Q := hopfieldQuadraticForm (weightsMatrix net) (net.weights.prop.1) (net.weights.prop.2);
    -0.5 * (Q.toFun xVec) - ∑ i, net.thresholds i * xVec i

/-
Proof that the energy function using the quadratic form is equivalent to the original energy function.
-/
lemma energy_eq_energy'' (net : HopfieldNetwork n) (x : HopfieldState n) : energy'' net x = energy net x := by
  let xVec : EuclideanSpace ℝ (Fin n) := toRealVector x
  let Q := hopfieldQuadraticForm (weightsMatrix net) (net.weights.prop.1) (net.weights.prop.2)
  have h1 : Q.toFun xVec = xVec ⬝ᵥ (weightsMatrix net).mulVec xVec := by
    rw [hopfieldQuadraticForm_apply]
  have h2 : ∑ i, net.thresholds i * xVec i = ∑ i, net.thresholds i * (x i).toReal := by
    congr
  rw [energy'', h1, h2]
  simp [energy]
  rw [← h1]
  rw [h1]
  exact rfl


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
