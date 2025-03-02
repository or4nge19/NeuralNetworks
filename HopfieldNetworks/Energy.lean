import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import HopfieldNetworks.Basic


namespace HopfieldState

open SpinState

variable {n : ℕ}

/--
  Helper lemma: For a symmetric matrix M with zero diagonal,
  the bilinear form B(δ,δ) = 0 when δ has only one non-zero component.
-/
lemma bilin_diag_zero_single_component {M : Matrix (Fin n) (Fin n) ℝ}
    (h_diag : Matrix.diag M = 0) (v : Fin n → ℝ) (i : Fin n)
    (h_single : ∀ j : Fin n, j ≠ i → v j = 0) :
    Matrix.toBilin' M v v = 0 := by
  -- Expand the bilinear form definition
  have h_bilin_sum : Matrix.toBilin' M v v = ∑ j, ∑ k, M j k * v j * v k := by
    unfold Matrix.toBilin'
    -- Use the definition of bilinear form
    simp only [LinearMap.BilinForm.toMatrix'_symm]

    -- Expand the sum explicitly
    rw [Matrix.toBilin'_apply']
    --simp only [Matrix.dotProduct, Fin.sum_univ_eq_sum_range]

    -- Convert dot product to sum using simp only
    simp only [dotProduct]
    -- Expand matrix-vector multiplication
    simp only [Matrix.mulVec, dotProduct]

    -- Rewrite nested sums
    have h1 : ∀ (j : Fin n), (∑ k, (M j k * v k)) * v j = ∑ k, M j k * v j * v k := by
      intro j
      rw [@Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

    apply Finset.sum_congr rfl
    intro j _
    -- Rewrite the goal to match the form in h1
    have : v j * ∑ x, M j x * v x = (∑ k, M j k * v k) * v j := by
      rw [mul_comm]

    rw [this]
    exact h1 j

  -- Since v has only one non-zero component at index i,
  -- the only relevant term in the sum is M i i * v i * v i
  have h_sum_eq : ∑ j, ∑ k, M j k * v j * v k = M i i * v i * v i := by
    dsimp only [Finset.sum_pos, Finset.univ_sum_single]

    calc ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, M j k * v j * v k
      = ∑ j ∈ Finset.univ, if j = i then ∑ k ∈ Finset.univ, M j k * v j * v k else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j = i
          · rw [if_pos hj]
          · rw [if_neg hj]
            apply Finset.sum_eq_zero
            intro k _
            rw [h_single j hj, mul_zero]
            exact zero_mul (v k)
      _ = ∑ k ∈ Finset.univ, M i k * v i * v k := by
        simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true]
        simp only [Finset.sum_singleton, Finset.sum_const_zero, add_zero]
      _ = ∑ k ∈ Finset.univ, if k = i then M i k * v i * v k else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = i
        · rw [if_pos hk]
        · rw [if_neg hk, h_single k hk, mul_zero]
      _ = M i i * v i * v i := by
        simp only [Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, if_true]
        simp only [Finset.sum_singleton, Finset.sum_const_zero, add_zero]

  -- The diagonal of M is zero by assumption
  calc Matrix.toBilin' M v v
    = ∑ j, ∑ k, M j k * v j * v k := h_bilin_sum
    _ = M i i * v i * v i := h_sum_eq
    _ = 0 * v i * v i := by rw [←Matrix.diag_apply M i, h_diag]; exact rfl
    _ = 0 := by simp

/--
  Helper lemma: For a vector δ with a single non-zero component at index i,
  B(x,δ) = δ_i * (Wx)_i where W is the weight matrix.
-/
lemma bilin_with_single_component {M : Matrix (Fin n) (Fin n) ℝ}
    (h_symm : Matrix.IsSymm M)
    (x δ : Fin n → ℝ) (i : Fin n)
    (h_single : ∀ j : Fin n, j ≠ i → δ j = 0) :
    Matrix.toBilin' M x δ = δ i * (M.mulVec x) i := by
  -- Expand the bilinear form definition
  have h_bilin_sum : Matrix.toBilin' M x δ = ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, M j k * x j * δ k := by
    unfold Matrix.toBilin'
    simp only [LinearMap.BilinForm.toMatrix'_symm]
    rw [Matrix.toBilin'_apply']
    simp only [dotProduct, Matrix.mulVec]

    -- Convert nested sums
    have h_sum : ∀ j, x j * (∑ k, M j k * δ k) = ∑ k, M j k * x j * δ k := by
      intro j
      rw [@Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

    -- Apply transformation to entire sum
    apply Finset.sum_congr rfl
    intro j _
    exact h_sum j

  -- Since δ has only one non-zero component at index i,
  -- we simplify the sum
  have h_sum_eq : ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, M j k * x j * δ k =
                  ∑ j ∈ Finset.univ, M j i * x j * δ i := by
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_eq_single i
    · intro k _hk h_ne
      rw [h_single k h_ne, mul_zero]
    · intro h_absurd
      exact False.elim (h_absurd (Finset.mem_univ i))

  -- Further simplify using the definition of matrix-vector multiplication
  calc Matrix.toBilin' M x δ
    = ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, M j k * x j * δ k := h_bilin_sum
    _ = ∑ j ∈ Finset.univ, M j i * x j * δ i := h_sum_eq
    _ = (∑ j ∈ Finset.univ, M j i * x j) * δ i := by
        rw [@Finset.sum_mul]
    _ = ((Matrix.transpose M).mulVec x) i * δ i := by
        -- Definition of matrix-vector multiplication
        have h_mul_vec_transpose : ((Matrix.transpose M).mulVec x) i = ∑ j ∈ Finset.univ, (Matrix.transpose M) i j * x j := rfl
        -- Use transpose definition to convert our sum
        have h_transpose : ∑ j ∈ Finset.univ, M j i * x j = ∑ j ∈ Finset.univ, (Matrix.transpose M) i j * x j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Matrix.transpose_apply]
        rw [h_transpose, h_mul_vec_transpose]
    _ = ((Matrix.transpose M).mulVec x) i * δ i := by
        have h_eq_transpose : (Matrix.transpose M) = M := by
          -- Since we're working with Hopfield networks, weights are symmetric
          ext i j
          -- For symmetric matrix, (Matrix.transpose M) i j = M j i and h_symm gives M j i = M i j
          rw [Matrix.transpose_apply]
          unfold Matrix.IsSymm at h_symm
          exact congrFun (congrFun (id (Eq.symm h_symm)) j) i
        rw [h_eq_transpose]
    _ = δ i * (M.mulVec x) i := by ring_nf; rw [Matrix.IsSymm.eq h_symm]; simp_all only [ne_eq]; rw [@NonUnitalNormedCommRing.mul_comm];

/--
  When a vector has a sparse update (change at one position),
  the difference in quadratic forms has a simple expression.
-/
lemma bilin_diff_single_update {M : Matrix (Fin n) (Fin n) ℝ}
    (h_symm : Matrix.IsSymm M)
    (h_diag : Matrix.diag M = 0)
    (x x' : Fin n → ℝ) (i : Fin n)
    (h_diff_i : ∀ j : Fin n, j ≠ i → x' j = x j) :
    Matrix.toBilin' M x' x' - Matrix.toBilin' M x x =
    2 * (x' i - x i) * (M.mulVec x) i := by
  -- Define the difference vector
  let δ : Fin n → ℝ := fun j => if j = i then x' i - x i else 0

  -- Express x' in terms of x and δ
  have h_x'_eq : x' = fun j => x j + δ j := by
    ext j
    by_cases hj : j = i
    · rw [hj]
      simp [δ]
    · simp [δ, hj]
      rw [h_diff_i j hj]

  -- Expand using bilinearity
  have h_bilin_expand : Matrix.toBilin' M x' x' =
                        Matrix.toBilin' M x x +
                        Matrix.toBilin' M x δ +
                        Matrix.toBilin' M δ x +
                        Matrix.toBilin' M δ δ := by
    rw [h_x'_eq]
    have h_add1 : ∀ a b c, Matrix.toBilin' M (fun i => a i + b i) c =
                            Matrix.toBilin' M a c + Matrix.toBilin' M b c := by
        intro a b c
        simp only [Matrix.toBilin'_apply']
        simp [dotProduct, Matrix.mulVec]
        have h_step : ∀ x : Fin n, (a x + b x) * (∑ x_1, M x x_1 * c x_1) =
                      a x * (∑ x_1, M x x_1 * c x_1) + b x * (∑ x_1, M x x_1 * c x_1) := by
          intro x
          rw [add_mul]

        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        exact h_step x
    have h_add2 : ∀ a b c, Matrix.toBilin' M a (fun i => b i + c i) =
                          Matrix.toBilin' M a b + Matrix.toBilin' M a c := by
      intro a b c
      -- Use the definition of bilinear form
      simp only [Matrix.toBilin'_apply']
      simp only [dotProduct, Matrix.mulVec]

      -- Use distributivity of dot product over addition
      have h_sum : ∀ x, ∑ j, M x j * (b j + c j) = ∑ j, M x j * b j + ∑ j, M x j * c j := by
        intro x
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        exact mul_add (M x j) (b j) (c j)

      -- Apply distribution for each term in the outer sum
      have h_each_term : ∀ x, a x * ∑ j, M x j * (b j + c j) =
                             a x * ∑ j, M x j * b j + a x * ∑ j, M x j * c j := by
        intro x
        rw [h_sum x]
        exact mul_add (a x) _ _

      -- Apply to the entire sum
      apply Eq.trans
      · apply Finset.sum_congr rfl
        intro x _
        exact h_each_term x
      · exact Finset.sum_add_distrib

    rw [h_add1 x δ (fun j ↦ x j + δ j)]
    rw [h_add2 x x δ]
    rw [h_add2 δ x δ]
    ring

  -- The quadratic term δ'*M*δ is zero due to the zero diagonal
  have h_δ_quad_zero : Matrix.toBilin' M δ δ = 0 := by
    apply bilin_diag_zero_single_component h_diag δ i
    intro j hj
    simp [δ, hj]

  -- By symmetry, the bilinear terms are equal
  have h_bilin_symm : Matrix.toBilin' M x δ = Matrix.toBilin' M δ x := by
    -- For symmetric matrices, the bilinear form is symmetric
    -- Use the direct property for symmetric bilinear forms
    have h_matrix_symm : Matrix.IsSymm M := h_symm

    -- Use the property that for symmetric matrices, the bilinear form is symmetric
    unfold Matrix.toBilin'
    simp only [LinearMap.BilinForm.toMatrix'_symm]

    -- Express the property in terms of the inner product
    have h_symm_inner : x ⬝ᵥ (M.mulVec δ) = δ ⬝ᵥ (M.mulVec x) := by
      -- For a symmetric matrix M = Mᵀ, we have x ⬝ᵥ (M.mulVec δ) = δ ⬝ᵥ (M.mulVec x)
      have h_transpose_eq : Matrix.transpose M = M := by
        ext i j
        exact congrFun (congrFun h_matrix_symm i) j

      -- Use properties of the dot product and symmetry
      calc x ⬝ᵥ (M.mulVec δ)
        = ∑ i, x i * (M.mulVec δ) i := by simp [dotProduct]
        _ = ∑ i, x i * (∑ j, M i j * δ j) := by simp [Matrix.mulVec]; exact rfl
        _ = ∑ i, ∑ j, x i * M i j * δ j := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = ∑ j, ∑ i, x i * M i j * δ j := by rw [Finset.sum_comm]
        _ = ∑ j, ∑ i, δ j * M j i * x i := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            -- Use matrix symmetry: M j i = M i j
            have h_symm_at_ij : M j i = M i j := by
              rw [← h_transpose_eq]
              exact congrFun (congrFun h_symm j) i
            rw [h_symm_at_ij]
            ring

        _ = ∑ j, δ j * (∑ i, M j i * x i) := by
            apply Finset.sum_congr rfl
            intro j _
            have h_factor : ∑ i, δ j * M j i * x i = δ j * ∑ i, M j i * x i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            exact h_factor
        _ = ∑ j, δ j * (M.mulVec x) j := by simp [Matrix.mulVec]; exact rfl
        _ = δ ⬝ᵥ (M.mulVec x) := by simp [dotProduct]

    -- Connect the bilinear form to the dot product
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    exact h_symm_inner
  -- The bilinear term simplifies using our earlier lemma
  have h_bilin_simple : Matrix.toBilin' M x δ = δ i * (M.mulVec x) i := by
    apply bilin_with_single_component h_symm x δ i
    intro j hj
    simp [δ, hj]

  -- Putting it all together
  calc Matrix.toBilin' M x' x' - Matrix.toBilin' M x x
    = Matrix.toBilin' M x x + Matrix.toBilin' M x δ +
      Matrix.toBilin' M δ x + Matrix.toBilin' M δ δ -
      Matrix.toBilin' M x x := by rw [h_bilin_expand]
    _ = Matrix.toBilin' M x δ + Matrix.toBilin' M δ x +
        Matrix.toBilin' M δ δ := by ring
    _ = Matrix.toBilin' M x δ + Matrix.toBilin' M x δ + 0 := by
        rw [h_bilin_symm, h_δ_quad_zero]
    _ = 2 * Matrix.toBilin' M x δ := by ring
    _ = 2 * (δ i * (M.mulVec x) i) := by rw [h_bilin_simple]
    _ = 2 * ((x' i - x i) * (M.mulVec x) i) := by simp [δ]
  exact Eq.symm (mul_assoc 2 (x' i - x i) (M.mulVec x i))

/--
  For summations that differ at a single point, the difference
  of sums equals the difference at that point.
-/
lemma sum_diff_single_point {α : Type*} [Fintype α] (f g : α → ℝ) (i : α)
    (h_eq : ∀ j : α, j ≠ i → f j = g j) :
    ∑ j, f j - ∑ j, g j = f i - g i := by
  have h_diff_sum : ∑ j, f j - ∑ j, g j = ∑ j, (f j - g j) := by
    rw [Finset.sum_sub_distrib]

  -- Only the i-th term can be non-zero in the difference
  have h_sum_eq : ∑ j, (f j - g j) = f i - g i := by
    apply Finset.sum_eq_single i
    · intro j _hj h_ne
      rw [h_eq j h_ne]
      simp
    · intro h_absurd
      exact False.elim (h_absurd (Finset.mem_univ i))

  rw [h_diff_sum, h_sum_eq]


/-- Calculates the energy difference when flipping a single spin in a Hopfield network.

Given:
* `net` - A Hopfield network with `n` nodes
* `x` - Initial state of the network
* `i` - Index of the spin to flip
* `x'` - Resulting state after flipping spin `i`
* `h_threshold_zero` - Assumption that threshold at position `i` is zero
* `h_diff` - Proof that `x'` differs from `x` only at position `i`

Returns the energy difference `E(x') - E(x)` between the two states, which equals
`-((x'[i] - x[i]) * localField(x, i))`, where:
* `x'[i] - x[i]` represents the change in spin value
* `localField(x, i)` is the local field at position `i`

This lemma is crucial for understanding how local spin flips affect the global energy
of the Hopfield network and is fundamental for proving convergence properties.
-/
lemma energy_diff_single_flip (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)
    (h_threshold_zero : net.thresholds i = 0)
    (x' : HopfieldState n) (h_diff : ∀ j : Fin n, j ≠ i → x' j = x j) :
    energy net x' - energy net x =
    -((x' i).toReal - (x i).toReal) * localField net x i := by
  let W := weightsMatrix net
  let xVec := toRealVector x
  let x'Vec := toRealVector x'

  have h_symm : Matrix.IsSymm W := weights_symmetric net
  have h_diag : Matrix.diag W = 0 := weights_diag_zero net

  have h_diff_i : ∀ j, j ≠ i → x'Vec j = xVec j := by
    intro j hj
    -- Use the hypothesis h_diff to establish that x' j = x j
    have h_states_eq_at_j : x' j = x j := h_diff j hj
    -- Connect the equality of states to equality of real vectors
    simp [x'Vec, xVec, toRealVector]
    -- Apply the equality of states
    rw [h_states_eq_at_j]


  have h_bilin_diff : Matrix.toBilin' W x'Vec x'Vec - Matrix.toBilin' W xVec xVec =
    2 * (x'Vec i - xVec i) * (W.mulVec xVec i) := by
      apply bilin_diff_single_update h_symm h_diag xVec x'Vec i h_diff_i

  have h_threshold_diff :
    (∑ j : Fin n, net.thresholds j * x'Vec j) - (∑ j : Fin n, net.thresholds j * xVec j) =
    net.thresholds i * (x'Vec i - xVec i) := by
      -- First convert to sum of differences
      have h_sum_diff : ∑ j : Fin n, net.thresholds j * x'Vec j - ∑ j : Fin n, net.thresholds j * xVec j =
                        ∑ j : Fin n, (net.thresholds j * x'Vec j - net.thresholds j * xVec j) := by
        rw [Finset.sum_sub_distrib]
      rw [h_sum_diff]

      -- Then use the fact that only at position i are the terms different
      have h_term_eq : ∀ (j : Fin n), j ≠ i →
          net.thresholds j * x'Vec j - net.thresholds j * xVec j = 0 := by
        intro j hj
        rw [h_diff_i j hj]
        simp

      have h_eq_single : ∑ j : Fin n, (net.thresholds j * x'Vec j - net.thresholds j * xVec j) =
                          net.thresholds i * x'Vec i - net.thresholds i * xVec i := by
        apply Finset.sum_eq_single i
        · intro j _ hj_ne
          exact h_term_eq j hj_ne
        · intro h_false
          exact False.elim (h_false (Finset.mem_univ i))

      have h_factor : net.thresholds i * x'Vec i - net.thresholds i * xVec i =
                     net.thresholds i * (x'Vec i - xVec i) := by
        ring

      rw [h_eq_single, h_factor]

      -- Simplify the expression at position i

  -- Substitute the lemmas about bilinear form and threshold differences
  have h_energy_diff :
    energy net x' - energy net x =
    -1/2 * ((Matrix.toBilin' W) x'Vec x'Vec - ((Matrix.toBilin' W) xVec xVec)) -
    (∑ j, net.thresholds j * x'Vec j - ∑ j, net.thresholds j * xVec j) := by
    unfold energy
    simp only [W, xVec, x'Vec]
    ring

  -- Apply our previous lemmas about the differences
  calc energy net x' - energy net x
    = -1/2 * ((Matrix.toBilin' W) x'Vec x'Vec - ((Matrix.toBilin' W) xVec xVec)) -
      (∑ j, net.thresholds j * x'Vec j - ∑ j, net.thresholds j * xVec j) := h_energy_diff
    _ = -1/2 * (2 * (x'Vec i - xVec i) * (W.mulVec xVec i)) -
      net.thresholds i * (x'Vec i - xVec i) := by rw [h_bilin_diff, h_threshold_diff]
    _ = -(x'Vec i - xVec i) * W.mulVec xVec i -
      net.thresholds i * (x'Vec i - xVec i) := by ring_nf
    _ = -(x'Vec i - xVec i) * (W.mulVec xVec i + net.thresholds i) := by ring_nf
    _ = -((x'Vec i) - (xVec i)) * (W.mulVec xVec i - (-net.thresholds i)) := by ring_nf
    _ = -((x'Vec i) - (xVec i)) * (W.mulVec xVec i + net.thresholds i) := by
        have : -(-net.thresholds i) = net.thresholds i := by ring_nf
        rw [@sub_neg_eq_add]
    _ = -((x' i).toReal - (x i).toReal) * (W.mulVec xVec i + net.thresholds i) := by
        simp only [x'Vec, xVec, toRealVector]

    _ = -((x' i).toReal - (x i).toReal) * localField net x i := by
        -- We need to connect the expression with localField definition
        unfold localField
        simp [W, xVec]

        -- First establish that the mulVec expressions match
        have h_mulvec_eq : W.mulVec xVec i = W.mulVec x.toRealVector i := by rfl
        rw [h_mulvec_eq]

        -- Now handle the sign of the threshold term
        -- The key insight: we need to use localField's definition with correct sign
        have h_local_field_rewrite : localField net x i = W.mulVec x.toRealVector i - net.thresholds i := by rfl

        -- The two expressions differ by 2*net.thresholds i
        have h_eq_with_correction : W.mulVec x.toRealVector i + net.thresholds i =
                                    localField net x i + 2*net.thresholds i := by
          rw [h_local_field_rewrite]
          ring_nf

        -- Handle the sign difference directly without assuming thresholds are zero

        have h_eq : W.mulVec x.toRealVector i + net.thresholds i = localField net x i + 2*net.thresholds i := by
          rw [h_local_field_rewrite]
          ring_nf

        -- Using definition of localField
        have h_local_field_def : localField net x i = W.mulVec x.toRealVector i - net.thresholds i := rfl

        -- With zero thresholds, the expressions are equal
        rw [h_threshold_zero] at h_local_field_def ⊢
        simp at h_local_field_def ⊢
