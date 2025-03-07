/-
Copyright (c) 2024 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib

--import Mathlib.Analysis.SpecificLimits.Basic
--import Mathlib.Analysis.SpecialFunctions.Geometric

open Matrix BigOperators Real Pow Finset Function Fin List Nat Set

/--
  A minimal structure for a linear RNN (identity activation).
  We keep `inputDim` separate so that `x_t` can be a vector.
-/
structure LinearRNN (hiddenDim inputDim : Nat) where
  W_hh : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ
  W_xh : Matrix (Fin inputDim) (Fin hiddenDim) ℝ
  b_h  : Fin hiddenDim → ℝ

namespace LinearRNN

/-- The hidden state of the RNN at a given time step. -/
def HiddenState (hiddenDim : Nat) : Type :=
  Fin hiddenDim → ℝ

@[ext]
theorem HiddenState.ext {hiddenDim : Nat} {h₁ h₂ : HiddenState hiddenDim} :
  (∀ i, h₁ i = h₂ i) → h₁ = h₂ := funext

/-- The input to the RNN at a given time step. -/
def Input (inputDim : Nat) : Type :=
  Fin inputDim → ℝ

/--
  A single step of an RNN with identity activation.
-/
def step (rnn : LinearRNN hiddenDim inputDim)
    (h : HiddenState hiddenDim)
    (x : Input inputDim) : HiddenState hiddenDim := fun i =>
  -- identity activation => no extra nonlinearity
  ∑ j, rnn.W_hh i j * (h j) +
  ∑ k, rnn.W_xh k i * (x k) +
  rnn.b_h i

/--
  We can "unroll" the RNN for `t` time steps with
  an input sequence x₀, x₁, ..., xₜ₋₁.
-/
def unroll (rnn : LinearRNN hiddenDim inputDim)
    (h0 : HiddenState hiddenDim)
    (xs : List (Input inputDim)) : HiddenState hiddenDim :=
  List.foldl (step rnn) h0 xs

/--
  Closed-form solution for a purely linear RNN.

  A more precise statement might be:
    hₜ = (Wₕₕ^t) h₀ + ∑ (τ=0 to t-1) Wₕₕ^(t-1-τ) (Wₓₕ x_τ + bₕ).
-/
lemma linear_solution
    (rnn : LinearRNN hiddenDim inputDim)
    (h0 : HiddenState hiddenDim)
    (xs : List (Input inputDim)) :
    let t := xs.length
    let zeroInput : Input inputDim := fun _ => 0
    unroll rnn h0 xs =
(fun i =>
  ∑ τ in Finset.range t,
    (((rnn.W_hh ^ (t - 1 - τ)).mulVec (fun j => ∑ k, rnn.W_xh k j * (xs.get? τ).getD zeroInput k) +
     (rnn.W_hh ^ (t - 1 - τ)).mulVec rnn.b_h) i))
      + (rnn.W_hh ^ t).mulVec h0 := by
  induction xs generalizing h0 with
  | nil =>
    simp [unroll, List.foldl]
    ext i
    simp
  | cons x xs' ih =>
    simp only [unroll, List.foldl, List.length_cons]
    let t := xs'.length
    have : xs'.length = t := rfl
    rw [ih (rnn.step h0 x)]
    simp [List.get?, Finset.sum_range_succ]
    ext i
    rw [pow_succ, Matrix.mul_mulVec]
    congr

    have : ∀ (A B : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) (v : Fin hiddenDim → ℝ),
      (A * B).mulVec v = A.mulVec (B.mulVec v) := by
      intros A B v
      ext j
      simp [Matrix.mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      congr
      ext k
      congr
      ext l
      ring
    simp_rw [this]
    congr 1
    simp only [add_left_inj]
    congr
    rw [← add_assoc]
    congr
    ext j
    simp [Matrix.mulVec, Matrix.mul_apply, add_comm]

end LinearRNN

namespace LinearRNN

open Matrix

/-
  Suppose we assume we have a norm on matrices such that
  ∥A B∥ ≤ ∥A∥ ∥B∥ (submultiplicative).
-/
variable {hiddenDim inputDim : Nat}

/-import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Operators-/

namespace Matrix

variable {m : Type} {R : Type}
  [Fintype m] [DecidableEq m]
  [Field R] [NormedField R] [NontriviallyNormedField R]
  [Module R R] [Semiring R] [RCLike R]
  [StarRing R] [NormedRing R] [CompleteSpace R]
  [HMul (Matrix m m R) (Matrix m m R) (Matrix m m R)]

/-- Matrix exponentiation with natural number exponent. -/
def matPow (A : Matrix m m R) [One R] [Zero R] [DecidableEq m] : ℕ → Matrix m m R
| 0   => Matrix.diagonal fun _ => 1
| n+1 => A * (matPow A n)

/-- Operator norm of a matrix induced by the Euclidean norm. -/
noncomputable def opNorm (A : Matrix m m R) : ℝ :=
  Real.sqrt (Finset.sup' Finset.univ 0 (fun i => ∑ j, (A i j)^2) (by apply Finset.univ_nonempty))

lemma opNorm_mul (A B : Matrix m m R) :
  opNorm (A * B) ≤ opNorm A * opNorm B := by
  -- Proof sketch using submultiplicativity of operator norm
  sorry

lemma opNorm_nonneg (A : Matrix m m R) :
  0 ≤ opNorm A := by
  unfold opNorm
  apply Real.sqrt_nonneg

lemma pow_opNorm (A : Matrix m m R) (n : ℕ) :
  opNorm (matPow A n) ≤ (opNorm A)^n := by
  induction n with
  | zero =>
    simp [matPow, opNorm]
    sorry
  | succ n ih =>
    simp [matPow]
    apply le_trans (opNorm_mul _ _)
    exact mul_le_mul ih (le_refl _) (opNorm_nonneg _) (pow_nonneg (opNorm_nonneg _) n)

end Matrix

-- We'll use the operator norm for matrices.
noncomputable def matrixNorm (A : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) : ℝ :=
  Matrix.opNorm A

lemma matrixNorm_nonneg (A : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) :
  0 ≤ matrixNorm A := by
  unfold matrixNorm
  apply Real.sqrt_nonneg

noncomputable instance : Norm (Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) :=
  ⟨matrixNorm⟩

noncomputable instance : Norm (Fin hiddenDim → ℝ) :=
  ⟨fun v => Real.sqrt (∑ i, (v i) ^ 2)⟩

/-- Norm instance for Input type -/
noncomputable instance {inputDim : Nat} : Norm (Input inputDim) :=
  ⟨fun v => Real.sqrt (∑ i, (v i) ^ 2)⟩

/-- Norm instance for HiddenState type -/
noncomputable instance {hiddenDim : Nat} : Norm (HiddenState hiddenDim) :=
  ⟨fun v => Real.sqrt (∑ i, (v i) ^ 2)⟩

lemma matrixNorm_submultiplicative
  (A B : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) :
    matrixNorm (A * B) ≤ matrixNorm A * matrixNorm B :=
  Matrix.opNorm_mul A B

lemma matrixNorm_pow_le_pow_matrixNorm
  (A : Matrix (Fin hiddenDim) (Fin hiddenDim) ℝ) (n : ℕ) :
    matrixNorm (A ^ n) ≤ (matrixNorm A) ^ n := by
  induction n with
  | zero =>
    simp [matrixNorm]
    apply le_of_eq
    sorry  -- This requires proving that the norm of the identity matrix is 1
  | succ n ih =>
    rw [pow_succ, pow_succ]
    apply le_trans (matrixNorm_submultiplicative _ _)
    apply mul_le_mul
    · exact ih
    · rfl
    · exact matrixNorm_nonneg A
    · exact pow_nonneg (matrixNorm_nonneg A) n

theorem hasSum_geometric_of_norm_lt_1 {α : Type*} [NormedField α] [CompleteSpace α]
    {ξ : α} (h : ‖ξ‖ < 1) : HasSum (fun n : ℕ ↦ ξ ^ n) (1 - ξ)⁻¹ := by
  -- For now, we use sorry as this requires complex analysis machinery
  -- The full proof would use:
  -- 1. Geometric series convergence for real numbers
  -- 2. Extension to normed fields via completeness
  -- 3. The fact that the sum equals (1-ξ)⁻¹
  sorry

theorem hasSum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_1 h

/--
  If ∥Wₕₕ∥ < 1, then the hidden state remains bounded
  for any bounded input sequence and bounded initial state.
-/
lemma hidden_state_bounded
    (rnn : LinearRNN hiddenDim inputDim)
    (h0 : HiddenState hiddenDim)
    (xs : List (Input inputDim))
    (H : matrixNorm rnn.W_hh < 1)
    (Hx : ∃ C, ∀ x ∈ xs, (‖x‖) ≤ C)
    : ∃ D, (‖unroll rnn h0 xs‖) ≤ D := by
  -- The real proof would:
  -- 1) Show that repeatedly applying Wₕₕ shrinks vectors => Wₕₕ^t -> 0 as t -> ∞
  -- 2) Summation of inputs contributes a finite amount => geometric series argument
  -- 3) Conclude that hₜ remains in a bounded ball
  have ⟨C, Hx⟩ := Hx
  let t := xs.length
  have Hnorm_pow : ∀ n : ℕ, ‖rnn.W_hh ^ n‖ ≤ matrixNorm rnn.W_hh ^ n := fun n =>
    matrixNorm_pow_le_pow_matrixNorm rnn.W_hh n
  have Hgeom : HasSum (fun n : ℕ => (matrixNorm rnn.W_hh) ^ n) (1 / (1 - matrixNorm rnn.W_hh)) := by
    have := hasSum_geometric_of_abs_lt_1 (by
      rw [abs_of_nonneg (matrixNorm_nonneg _)]
      exact H)
    rw [inv_eq_one_div] at this
    exact this
    · exact matrixNorm_nonneg rnn.W_hh
    · exact H
  have Hsum : Summable (fun n : ℕ => (matrixNorm rnn.W_hh) ^ n) :=
    Hgeom.summable
  have Ht : ∀ τ : ℕ, τ ∈ Finset.range t →
    norm ((rnn.W_hh ^ (t - 1 - τ)).mulVec
      (fun j => ∑ k, rnn.W_xh k j * ((xs.get? τ).getD (fun _ => 0) k)))
      ≤ matrixNorm rnn.W_hh ^ (t - 1 - τ) * C * (Matrix.colNorm rnn.W_xh) := by
    intro τ hτ
    have h_get : ∃ i, xs.get? τ?.elim 0 (fun a => a) = xs.get i ∧ i < xs.length := by
      cases τ? with
      | none =>
        exists (0 : Fin xs.length)
        simp
      | some τ' =>
        exists (⟨τ', by apply List.get?_is_some⟩ : Fin xs.length)
        simp
    rcases h_get with ⟨⟨i, hi⟩, rfl, _⟩
    apply le_trans (Matrix.norm_mulVec_le _ _)
    apply mul_le_mul_of_nonneg_right (Hnorm_pow _) (norm_nonneg _)
    apply le_trans (Matrix.norm_mulVec_le _ _)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Hx _ (List.get_mem _ _ _)
    apply Matrix.colNorm_le_opNorm
    simp
  have Hb : ∀ τ : ℕ, τ ∈ Finset.range t →
    ∥(rnn.W_hh ^ (t - 1 - τ)).mulVec rnn.b_h∥ ≤
      matrixNorm rnn.W_hh ^ (t - 1 - τ) * (norm rnn.b_h) := by
      intro τ hτ
      apply le_trans (Matrix.norm_mulVec_le _ _)
      apply mul_le_mul_of_nonneg_right (Hnorm_pow _) (norm_nonneg _)
  have : ∥unroll rnn h0 xs∥ ≤
      ∑ τ in Finset.range t, matrixNorm rnn.W_hh ^ (t - 1 - τ) * (C * (Matrix.colNorm rnn.W_xh) + norm rnn.b_h)
      + (matrixNorm rnn.W_hh) ^ t * ∥h0∥ := by
    rw [linear_solution]
    apply le_trans (norm_add_le _ _)
    apply add_le_add_right
    rw [Matrix.norm_mulVec_le]
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum (fun τ hτ => _)
    simp only [norm_add_le]
    apply add_le_add
    apply Ht
    apply Hb
    apply le_trans (Hnorm_pow t)
    apply le_mul_of_one_le_of_nonneg
    simp
    apply norm_nonneg
  apply le_trans this
  apply add_le_add_right
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => _))
  simp only [Finset.sum_coe_sort_eq_sum_range]
  have : ∀ (i : ℕ),
    matrixNorm rnn.W_hh ^ i * (C * Matrix.colNorm rnn.W_xh + norm rnn.b_h) ≤
      (matrixNorm rnn.W_hh) ^ i * (C * (Matrix.colNorm rnn.W_xh) + norm rnn.b_h) := by
    intro i
    apply mul_le_mul_of_nonneg_right (Hnorm_pow i) (by simp)
  apply le_trans (sum_le_tsum _ (by simp) Hsum)
  rw [← mul_tsum (by simp) Hsum]
  apply le_mul_of_one_le_right (by simp)
  simp [Hgeom]
  apply norm_nonneg

  all_goals {
    simp
    apply mul_nonneg (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _)
    simp
  }

end LinearRNN

structure TransformerBlock (dim seqLen contextWindow : Nat) where
  W_q : Matrix (Fin dim) (Fin dim) ℝ
  W_k : Matrix (Fin dim) (Fin dim) ℝ
  W_v : Matrix (Fin dim) (Fin dim) ℝ
  W_out : Matrix (Fin dim) (Fin dim) ℝ
  b_out : Fin dim → ℝ

namespace TransformerBlock

/-- A token is a vector in the `dim`-dimensional space. -/
def Token (dim : Nat) : Type :=
  Fin dim → ℝ

/-- An input sequence is a sequence of `seqLen` tokens. -/
def InputSequence (dim seqLen : Nat) : Type :=
  Fin seqLen → Token dim

/--
  The self-attention mechanism for a transformer block.
  For each position `i`, it computes a weighted sum of the
  values `v` at positions `j` that are in the context window
  of `i`, where the weights are determined by the compatibility
  of the queries `q` at `i` and the keys `k` at `j`.
-/
def selfAttention
    (block : TransformerBlock dim seqLen contextWindow)
    (input : InputSequence dim seqLen)
    (i : Fin seqLen)
    : Token dim :=
  let qi := (fun d => ∑ e, block.W_q d e * (input i e))
  -- gather local indices
  let validIndices : List (Fin seqLen) :=
    ((List.range contextWindow).filterMap (fun offset =>
      let j := i.val - offset
      if h : 0 ≤ j ∧ j < seqLen then
        some ⟨j, h.2⟩
      else
        none
    )) ++ [i]

  let attnVec : Token dim := fun d =>
    List.sum (validIndices.map (fun j =>
      let kjd := ∑ e, block.W_k d e * (input j e)
      let vjd := ∑ e, block.W_v d e * (input j e)
      qi d * kjd * vjd
    ))

  fun d => ∑ e, block.W_out d e * (attnVec e) + block.b_out d

/-- Helper function to compute valid indices for attention at position i -/
def getValidIndices (block : TransformerBlock dim seqLen contextWindow) (i : Fin seqLen) : List (Fin seqLen) :=
  ((List.range contextWindow).filterMap (fun offset =>
    let j := i.val - offset
    if h : 0 ≤ j ∧ j < seqLen then
      some ⟨j, h.2⟩
    else
      none
  )) ++ [i]

/--
  Positions used in `selfAttention` for index `i` are
  precisely the set of indices j with j in [max 0 (i - contextWindow + 1), i].
-/
lemma attends_only_local_range
    (block : TransformerBlock dim seqLen contextWindow)
    (input : InputSequence dim seqLen)
    (i : Fin seqLen)
    : ∀ (j : Fin seqLen), j ∈ getValidIndices block i →
      max 0 (i.val - contextWindow + 1) ≤ j.val ∧ j.val ≤ i.val := by
  let validIndices : List (Fin seqLen) :=
    ((List.range contextWindow).filterMap (fun offset =>
      let j := i.val - offset
      if h : 0 ≤ j ∧ j < seqLen then
        some (Fin.mk j h.2)
      else
        none
    )) ++ [i]

  intro j hj
  have hj_mem_valid : j ∈ getValidIndices block i := by
    rw [getValidIndices] at hj
    exact hj
    rw [h_support] at hj
    have : ∀ d, j ∈ (getValidIndices.map (fun j =>
      fun (d : Fin dim) =>
        let kjd := ∑ e, block.W_k d e * (input j e)
        let vjd := ∑ e, block.W_v d e * (input j e)
        (fun d => ∑ e, block.W_q d e * (input i e)) d * kjd * vjd
    )).foldr (fun x acc => x.support ∪ acc) ∅ ↔ j ∈ validIndices := by
      intro d
      simp only [List.mem_map, List.foldr_map, Set.mem_union, Finset.mem_coe,
        Function.support_eq_empty_iff, ne_eq]
      induction validIndices with
      | nil => simp
      | cons hd tl ih =>
        simp
        tauto
    specialize this j
    simpa using this
  have hj_mem_range : j ∈ (List.range contextWindow).filterMap (fun offset =>
      let j := i.val - offset
      if 0 ≤ j ∧ j < seqLen then
        some (Fin.mk j (by simp [Fin.mk_lt_mk]; tauto))
      else
        none) ∨ j = i := by
    simp [validIndices] at hj_mem_valid
    exact hj_mem_valid
  rcases hj_mem_range with (hj_mem_range | rfl)
  · have hj_mem : ∃ (offset : ℕ) (H : offset ∈ List.range contextWindow), j.val = i.val - offset ∧ 0 ≤ i.val - offset ∧ i.val - offset < seqLen := by
      simp [List.mem_filterMap] at hj_mem_range
      rcases hj_mem_range with ⟨offset, ho, h_j⟩
      use offset, by simpa [List.mem_range] using ho
      simp only [FractionalIdeal.val_eq_coe, Fin.ext_iff] at h_j
      have hj := h_j.1
      rw [hj]
      constructor
      . apply Int.sub_nonneg_of_le
        simp only [List.mem_range] at ho
        apply le_trans (Nat.le_sub_left_of_add_le (Nat.add_comm _ _ ▸ ho)) (Nat.sub_le _ _)
      . simp only [List.mem_range] at ho
        have : j.val < seqLen := by
          simp [← hj]
          have hsub := Nat.sub_lt_sub_left ho (Nat.le_add_left _ _)
          simp only [add_def] at hsub
          rw [Nat.sub_self] at hsub
          have hzero : (0 : ℤ) < seqLen := by simp_all
          apply Int.ofNat_lt.mp at hzero
          simpa using hzero
        exact this
    match hj_mem with
    | ⟨offset, ho, hj, h_nonneg, h_lt_seqLen⟩ =>
      let offset_lt_cw := by simp [List.mem_range] at ho; exact ho
      constructor
      · -- prove lower bound
        simp only [ge_iff_le, max_le_iff]
        constructor
        · -- prove j ≥ 0
          rw [hj]
          have : i.val - contextWindow + 1 ≤ i.val - offset := by
            have : offset ≤ contextWindow - 1 := Nat.le_pred_of_lt offset_lt_cw
            linarith
          exact this
        · -- prove j ≥ i - contextWindow + 1
          rw [hj]
          have : offset < contextWindow := by
            simp [List.mem_range] at ho
            exact ho
          have h1 : offset < contextWindow := this
          have h2 : 1 ≤ contextWindow := by
            apply Nat.one_le_of_lt
            exact h1
          have h3 : i - offset ≤ i := Nat.sub_le _ _
          have h4 : i - contextWindow ≤ i - offset :=
            sub_le_sub (Nat.le_of_lt h1)
          have h5 : i - contextWindow + 1 ≤ i - offset + 1 :=
            Nat.add_le_add_right h4 1
          exact h5
      · -- prove upper bound
        rw [hj]
        simp
    constructor
    . simp only [ge_iff_le, Int.ofNat_le]
      apply Int.le_of_coe_nat_le_of_coe_nat_le
      simp [← hj, Int.ofNat_sub (Nat.le_of_lt offset_lt_cw)]
      simp
    . simp [← hj]
      rw [Int.ofNat_sub (Nat.le_of_lt offset_lt_cw)]
      simp
  · constructor
    . simp
    . simp

/--
  If contextWindow ≤ seqLen, then there is some position i
  that cannot "see" the entire sequence.
-/
lemma not_all_positions_are_visible
    {dim seqLen : Nat} (contextWindow : Nat)
    (block : TransformerBlock dim seqLen contextWindow)
    (h : contextWindow ≤ seqLen)
    (hseq : 0 < seqLen)
    :
    ∃ (i : Fin seqLen), ∃ j : Fin seqLen,
      j.val ∉ (Finset.Icc (max 0 (i.val - contextWindow + 1)) i.val) := by
  rcases eq_or_lt_of_le h with (rfl | h)
  . use ⟨0, hseq⟩
    use ⟨Nat.sub contextWindow 1, Nat.sub_lt hseq (Nat.zero_lt_one)⟩
    simp [Finset.mem_Icc]
    -- rw [Fin.val_mk] Removed as there are no goals to solve
  . use ⟨0, hseq⟩
    use ⟨seqLen - 1, Nat.sub_lt hseq (Nat.zero_lt_one)⟩
    simp [Finset.mem_Icc]
    -- rw [Fin.val_mk]
    -- exact Nat.not_le_of_gt (Nat.sub_pos_of_lt hseq)

end TransformerBlock
