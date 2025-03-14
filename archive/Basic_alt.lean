import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

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
structure SpinState' where
  val : Fin 2

/-def SpinState := ZMod 2

instance : CommGroup SpinState := ZMod.commGroup 2

def toReal (s : SpinState) : ℝ := if s = 0 then -1 else 1-/


noncomputable
instance : DecidableEq SpinState' :=
  fun s₁ s₂ => by
    have := inferInstanceAs (DecidableEq (Fin 2))
    exact Classical.propDecidable (s₁ = s₂)

noncomputable
instance : Fintype SpinState' where
  elems := {⟨0, by simp [Nat.zero_lt_two]⟩, ⟨1, by simp [Nat.one_lt_two]⟩}
  complete s := by
    cases' s with val prop
    simp only [Finset.mem_insert, Finset.mem_singleton]
    fin_cases val
    · left; rfl
    · right; rfl

instance : Inhabited SpinState' := ⟨⟨1, by simp⟩⟩

namespace SpinState'

/--
Map `SpinState` to real numbers: `up ↦ 1`, `down ↦ -1`.
-/
@[simp]
def toReal (s : SpinState') : ℝ := if s.val = 1 then 1 else -1

/--
`SpinState` forms a commutative group under multiplication,
with `up` as the identity element. This group is isomorphic to `ℤ₂`.
-/
@[simp]
lemma ext_spinstate' : ∀ {s₁ s₂ : SpinState'}, s₁ = s₂ ↔ s₁.val = s₂.val := by
  intros s₁ s₂
  apply Iff.intro
  · intro h
    rw [h]
  · intro h
    cases' s₁ with val₁ prop₁
    cases' s₂ with val₂ prop₂
    simp at h ⊢
    exact h



/--
Interpret `up` as `true` and `down` as `false`.
-/
def toBool (s : SpinState') : Bool := s.val = 1

/--
Inverse of `toBool`: `true ↦ up`, `false ↦ down`.
-/
def ofBool (b : Bool) : SpinState' := ⟨if b then 1 else 0, by {
  cases b
  · simp
  · simp
}⟩

@[simp]
lemma ofBool_toBool (b : Bool) : (ofBool b).toBool = b := by
  cases b <;> simp [toBool, ofBool]

@[simp]
lemma toBool_ofBool (s : SpinState') : ofBool (s.toBool) = s := by
  cases' s with val prop
  fin_cases val
  <;> simp
  rfl
  rfl

/--
If two spin states have the same real value, they must be equal.
-/
@[simp]
lemma eq_of_toReal_eq {s₁ s₂ : SpinState'} (h : s₁.toReal = s₂.toReal) : s₁ = s₂ := by
  apply ext_spinstate'.mpr
  cases' s₁ with val₁
  cases' s₂ with val₂
  fin_cases val₁
  · fin_cases val₂
    · rfl
    · simp [toReal] at h
      norm_num at h
  · fin_cases val₂
    · simp [toReal] at h
      norm_num at h
    · rfl

@[simp]
lemma up_down_distinct : ∀ (s₁ s₂ : SpinState'), s₁ ≠ s₂ → s₁.toReal ≠ s₂.toReal := by
  intros s₁ s₂ h
  simp [toReal]
  contrapose! h
  exact eq_of_toReal_eq h

@[simp]
lemma up_down_diff : (⟨1, by simp⟩ : SpinState').toReal - (⟨0, by norm_num⟩ : SpinState').toReal = 2 := by
  simp [toReal]
  norm_num

@[simp]
lemma down_up_diff : (⟨0, by {
    have := Nat.not_lt_zero 0;
    exact Nat.zero_lt_two
  }⟩ : SpinState').toReal - (⟨1, by simp⟩ : SpinState').toReal = -2 := by
  simp [toReal]
  norm_num

/-- Equivalence between `SpinState` and `Bool`. -/
def spinState'EquivBool : SpinState' ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := fun s => toBool_ofBool s
  right_inv := fun b => ofBool_toBool b

instance : CommGroup SpinState' where
  mul s₁ s₂ :=
    if s₁.toBool = s₂.toBool then
      ofBool true
    else
      ofBool false
  one := ofBool true
  inv s := s
  mul_assoc := by
    intros a b c
    apply SpinState'.ext_spinstate'.mpr
    unfold toBool ofBool
    simp
    cases' a with a_val _
    cases' b with b_val _
    cases' c with c_val _
    fin_cases a_val
    · fin_cases b_val
      · fin_cases c_val
        · simp; exact rfl
        · simp; exact rfl
      · fin_cases c_val
        · simp; exact rfl
        · simp; exact rfl
    · fin_cases b_val
      · fin_cases c_val
        · simp; exact rfl
        · simp; exact rfl
      · fin_cases c_val
        · simp; exact rfl
        · simp; exact rfl
  one_mul := by
    intro a
    apply SpinState'.ext_spinstate'.mpr
    cases' a with a_val _
    fin_cases a_val
    · simp [Mul, One, toBool, ofBool]
      rfl
    · simp [Mul, One, toBool, ofBool]
      rfl
  mul_one := by
    intro a
    apply SpinState'.ext_spinstate'.mpr
    cases' a with a_val _
    fin_cases a_val
    · simp [Prod.instCommGroup, PUnit.addCommGroup, toBool, ofBool]
      exact rfl
    · simp [Prod.instCommGroup, PUnit.addCommGroup, toBool, ofBool]
      exact rfl
  mul_comm := by
    intros a b
    apply SpinState'.ext_spinstate'.mpr
    cases' a with a_val _
    cases' b with b_val _
    fin_cases a_val
    · fin_cases b_val
      · simp [Prod.instCommGroup, toBool, ofBool]
      · simp [Prod.instCommGroup, toBool, ofBool]
        exact rfl
    · fin_cases b_val
      · simp [Prod.instCommGroup, toBool, ofBool]; exact rfl
      · simp [Prod.instCommGroup, toBool, ofBool]
  inv_mul_cancel := by
    intro a
    apply SpinState'.ext_spinstate'.mpr
    cases' a with a_val _
    fin_cases a_val
    · simp [toBool, ofBool]
      rfl
    · simp [toBool, ofBool]
      rfl




/-- Equivalence between `SpinState` and `ZMod 2`. -/
def spinState'EquivZmod2 : SpinState' ≃ ZMod 2 where
  toFun := fun s => if s.val = 1 then 1 else 0
  invFun := fun z => ⟨if z = 0 then 0 else 1, by {
      split_ifs with h
      · simp
      · simp
  }⟩
  left_inv := by
    intro s
    cases' s with val prop
    apply SpinState'.ext_spinstate'.mpr
    fin_cases val
    · simp only [cond_true, cond_false]
      norm_num
    · simp only [cond_true, cond_false]
      norm_num
  right_inv := by
    intro z
    match z with
    | 0 =>
      simp
    | 1 =>
      simp



instance : CoeTC SpinState' (Fin 2) where
  coe s := s.val

def coeNonzero (s : SpinState') (h : s.toBool = true) : {x : Fin 2 // x ≠ 0} :=
⟨s.val, by
  rw [SpinState'.toBool] at h;
  -- since s is up, s.val = 1, and 1 ≠ 0:
  simp_all only [Fin.isValue, decide_eq_true_eq, ne_eq, one_ne_zero, not_false_eq_true]⟩

end SpinState'

/--
A Hopfield state for `n` neurons is a function from `Fin n` to `SpinState`.
-/
def HopfieldState' (n : ℕ) := Fin n → SpinState'

namespace HopfieldState'

open SpinState'

variable {n : ℕ}

@[ext]
lemma hopfieldState'_ext {x y : HopfieldState' n} (h : ∀ i, x i = y i) : x = y := funext h

noncomputable
instance : Dist (HopfieldState' n) where
  dist x y := Finset.sum Finset.univ fun i => if x i = y i then 0 else 1

/--
We endow `HopfieldState n` with the Hamming distance as a `MetricSpace`.
`dist x y` is the number of coordinates in which `x` and `y` differ.
-/
noncomputable
instance : MetricSpace (HopfieldState' n) where
  dist := fun x y => Finset.sum Finset.univ fun i => if x i = y i then 0 else 1 -- Hamming distance: count differing spins
  dist_self := by simp [dist, Finset.sum_const_zero]
  dist_comm := by
    intro x y
    simp [dist]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i = y i
    · simp [h]
    · have h' : y i ≠ x i := by
        contrapose! h
        rw [h]
      simp_all only [Finset.mem_univ, SpinState'.ext_spinstate', ne_eq, ↓reduceIte]
  dist_triangle := by
    intro x y z
    let indicator (P : Prop) [Decidable P] : ℝ := if P then 1 else 0
    have indicator_nonneg (P : Prop) [Decidable P] : 0 ≤ indicator P := by
      simp [indicator]
      split_ifs <;> norm_num
    have indicator_triangle (P Q : Prop) [Decidable P] [Decidable Q] : indicator (P ∨ Q) ≤ indicator P + indicator Q := by
      simp [indicator]
      by_cases hP : P
      · simp [hP]
        by_cases hQ : Q
        · simp [hQ]
        · simp [hQ]
      · simp [hP]
    calc
      dist x z = ∑ i, indicator (x i ≠ z i) := by simp [dist, indicator]
      _ ≤ ∑ i, indicator ((x i ≠ y i) ∨ (y i ≠ z i)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h₁ : x i = y i
        · by_cases h₂ : y i = z i
          · simp [h₁, h₂]
          · simp [h₁, h₂]
        · by_cases h₂ : y i = z i
          · simp [h₁, h₂]
          · simp [h₁, h₂]
            simp [indicator]
            by_cases h : x i = z i
            · simp [h, indicator]
            · dsimp only [indicator]; simp_all only [Finset.mem_univ, SpinState'.ext_spinstate', ↓reduceIte, le_refl,
              indicator]
      _ ≤ ∑ i, (indicator (x i ≠ y i) + indicator (y i ≠ z i)) := by
        apply Finset.sum_le_sum
        intro i _
        apply indicator_triangle
      _ = (∑ i, indicator (x i ≠ y i)) + ∑ i, indicator (y i ≠ z i) := by simp [Finset.sum_add_distrib]
      _ = dist x y + dist y z := by simp [dist, indicator]
  eq_of_dist_eq_zero := by
    sorry


/--
Convert a Hopfield state to a real vector of dimension `n`, where
each coordinate is either `+1` or `{-1}`.
-/
def toRealVector (x : HopfieldState' n) : Fin n → ℝ :=
  fun i => (x i).toReal

@[simp]
lemma toRealVector_apply (x : HopfieldState' n) (i : Fin n) :
  x.toRealVector i = (x i).toReal := rfl

/--
`HopfieldNetwork` consists of:
1. A real-valued weight matrix `weights` of size `n × n`, which is Hermitian (symmetric in ℝ)
   and has zero diagonal.
2. A threshold vector `thresholds` with one real value per neuron.
-/
structure HopfieldNetwork' (n : ℕ) : Type where
  weights : {M : Matrix (Fin n) (Fin n) ℝ // Matrix.IsHermitian M ∧ Matrix.diag M = 0}
  thresholds : Fin n → ℝ

/--
Convenience accessor for the underlying weights matrix.
-/
def weightsMatrix (net : HopfieldNetwork' n) : Matrix (Fin n) (Fin n) ℝ := net.weights.val

@[simp]
lemma weights_symmetric (net : HopfieldNetwork' n) :
  Matrix.IsSymm (weightsMatrix net) := net.weights.prop.1

@[simp]
lemma weights_is_symm (net : HopfieldNetwork' n) :
  (weightsMatrix net).IsSymm := net.weights.prop.1

@[simp]
lemma weights_diag_zero (net : HopfieldNetwork' n) :
  Matrix.diag (weightsMatrix net) = 0 := net.weights.prop.2

/--
Energy function of the Hopfield network for a given state `x`.
Typical Hopfield energy: `E(x) = -1/2 xᵀWx - bᵀx`, where b is the bias (threshold).
-/
noncomputable def energy (net : HopfieldNetwork' n) (x : HopfieldState' n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - Finset.sum Finset.univ (fun i => net.thresholds i * xVec i)

noncomputable def energy' (net : HopfieldNetwork' n) (x : HopfieldState' n) : ℝ :=
  let xVec := toRealVector x;
  let W := weightsMatrix net;
  let B := Matrix.toBilin' W;
  -0.5 * B xVec xVec - (fun i => net.thresholds i) ⬝ᵥ xVec

lemma energy_eq_energy' (net : HopfieldNetwork' n) (x : HopfieldState' n) : energy net x = energy' net x := by
  let xVec := toRealVector x
  let W := weightsMatrix net
  let B := Matrix.toBilin' W
  rfl

/--
Local field (net input) for neuron `i` in state `x`,
`(Wx)_i - threshold[i]`.
-/
def localField (net : HopfieldNetwork' n) (x : HopfieldState' n) (i : Fin n) : ℝ :=
  (weightsMatrix net).mulVec (toRealVector x) i - net.thresholds i

/--
Asynchronous update rule for neuron `i` in state `x`: flips the spin
according to the sign of the local field.
If the local field is zero, no change is made.
-/
noncomputable def updateState (net : HopfieldNetwork' n) (x : HopfieldState' n) (i : Fin n) : HopfieldState' n :=
  let lf := localField net x i
  Function.update x i $
    if 0 < lf then ⟨1, by simp⟩
    else if lf < 0 then ⟨0, by {
      simp
    }⟩
    else x i

/--
`UpdateSeq net x` is an inductive type representing a sequence of
asynchronous updates on the Hopfield network `net` starting from state `x`.
-/
inductive UpdateSeq {n : ℕ} (net : HopfieldNetwork' n) : HopfieldState' n → Type
  | nil : (x : HopfieldState' n) → UpdateSeq net x
  | cons : (x : HopfieldState' n) → (i : Fin n) → UpdateSeq net (updateState net x i) → UpdateSeq net x

namespace UpdateSeq
/--
Extract the final state from an update sequence.
-/
noncomputable def target {n : ℕ} {net : HopfieldNetwork' n} {x : HopfieldState' n}
  : UpdateSeq net x → HopfieldState' n
  | nil x => x
  | cons _ _ s => s.target

end UpdateSeq

/--
A state `x` is a fixed point under `net` if no single-neuron update changes the state.
-/
def isFixedPoint {n : ℕ} (net : HopfieldNetwork' n) (x : HopfieldState' n) : Prop :=
  ∀ i, updateState net x i = x

/--
A state `x` converges to a fixed point `p` if there is an update
sequence from `x` that terminates at `p`, and `p` is a fixed point.
-/
def convergesTo {n : ℕ} (net : HopfieldNetwork' n) (x p : HopfieldState' n) : Prop :=
  ∃ (seq : UpdateSeq net x), seq.target = p ∧ isFixedPoint net p

/--
The overlap measures similarity between two states by taking
the dot product of their corresponding ±1 vectors.
-/
def overlap (x y : HopfieldState' n) : ℝ :=
  Finset.sum Finset.univ fun i => (x i).toReal * (y i).toReal

lemma real_vector_sq_one (x : HopfieldState' n) (i : Fin n) : (x i).toReal * (x i).toReal = 1 := by
  simp [SpinState.toReal]
  fin_cases (x i).val
  <;> norm_num

@[simp]
lemma overlap_self (x : HopfieldState' n) :
    overlap x x = n := by
  rw [overlap]
  simp [real_vector_sq_one x]
  rw [Finset.sum_const, Finset.card_univ]
  simp

/--
`ContentAddressableMemory` wraps a `HopfieldNetwork` and a finite set of
stored patterns with a threshold criterion guaranteeing pattern completion.
-/
structure ContentAddressableMemory (n : ℕ) : Type where
  network : HopfieldNetwork' n
  patterns : Finset (HopfieldState' n)
  threshold : ℝ
  completes :
    ∀ p ∈ patterns, ∀ x : HopfieldState' n,
      overlap x p ≥ threshold →
      ∃ y : HopfieldState' n,
        isFixedPoint network y ∧ overlap y p = (n : ℝ)

/--
Convenience coercion from `ContentAddressableMemory` to its underlying `HopfieldNetwork`.
-/
instance contentAddressableMemoryToHopfieldNetwork {n : ℕ} :
    Coe (ContentAddressableMemory n) (HopfieldNetwork' n) where
  coe c := c.network
