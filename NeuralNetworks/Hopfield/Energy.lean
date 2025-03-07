import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.StarOrdered
import NeuralNetworks.Hopfield.Basic

section EnergyDecrease


/-!
  The energy function for a Hopfield network decreases monotonically with each spin update.

  This theorem demonstrates that for a Hopfield network with zero thresholds:
  1) When a spin update occurs at position `i`, the energy difference is exactly:
     `-((x'[i] - x[i]) * localField(x, i))`
  2) When a spin's state and its local field have inconsistent signs, flipping the spin
     strictly decreases the network's energy
  3) When a spin's state and local field have consistent signs, the energy remains unchanged
  4) As a consequence, for any update sequence, the energy monotonically decreases

  These results establish the fundamental convergence properties of Hopfield networks
  and show that the energy function serves as a Lyapunov function for the dynamics.
-/
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
    · intro a
      simp_all only [ne_eq, Finset.mem_univ, not_true_eq_false]

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

/--
  Helper theorem: When the local field and spin state have inconsistent signs,
  flipping the spin decreases the energy.

Proves that the energy of a Hopfield network decreases when updating a neuron
with inconsistent signs between its state and local field.

Given:
* `net` - A Hopfield network with n neurons
* `x` - Current state of the network
* `i` - Index of the neuron to update
* `h_threshold_zero` - Assumption that threshold at index i is zero
* `h_inconsistent` - Assumption that current state and local field have inconsistent signs

The proof shows that updating neuron i decreases the network's energy by considering two cases:
1. When local field is positive: the neuron must be in down state (-1) and flips to up state (1)
2. When local field is negative: the neuron must be in up state (1) and flips to down state (-1)

In both cases, the energy difference is proven to be negative, confirming that
the update reduces the network's overall energy.

-- TODO:
  Remove the h_threshold_zero condition, and modify the proof
  slightly to account for the threshold term in the energy difference
-/
lemma energy_decreases_on_update_with_inconsistent_signs
    (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)
    (h_threshold_zero : net.thresholds i = 0)
    (h_inconsistent : (x i).toReal * localField net x i < 0) :
    energy net (updateState net x i) < energy net x := by
  let x' := updateState net x i
  let lf := localField net x i

  have h_diff_j : ∀ j : Fin n, j ≠ i → x' j = x j :=
    fun j hj => Function.update_of_ne hj _ _

  have h_energy_diff := energy_diff_single_flip net x i h_threshold_zero x' h_diff_j

  have h_lf_nonzero : lf ≠ 0 := by
    intro h_zero
    have : (x i).toReal * 0 < 0 := by rw [← h_zero]; exact lt_of_lt_of_eq h_inconsistent (id (Eq.symm h_zero))
    simp at this

  by_cases h_pos : 0 < lf
  · -- Case: local field is positive
    -- By the inconsistency condition, x i must be down (-1)
    have h_x_is_down : x i = SpinState.down := by
        cases h : x i with
        | down => rfl
        | up =>
          have h_up_real : (x i).toReal = 1 := by rw [h]; rfl

          have h_lf_neg : lf < 0 := by
            rw [h_up_real] at h_inconsistent
            rw [one_mul] at h_inconsistent
            exact h_inconsistent

          -- This contradicts h_pos : 0 < lf
          exact absurd h_lf_neg (not_lt_of_gt h_pos)

    have h_x'_is_up : x' i = SpinState.up := by
      change updateState net x i i = SpinState.up
      unfold updateState
      simp
      -- When local field is positive, we flip from down to up
      have : lf > 0 := h_pos
      simp [this, h_x_is_down]
      exact h_pos

    -- Calculate the energy difference directly
    have h_diff_simplified : energy net x' - energy net x < 0 := by
      -- Start with the energy difference formula
      rw [h_energy_diff]

      -- Substitute the values for up and down states
      have h1 : (x' i).toReal - (x i).toReal = 1 - (-1) := by
        rw [h_x'_is_up, h_x_is_down]
        simp [SpinState.toReal]

      have h2 : 1 - (-1) = 2 := by ring

      -- Simplify the expression
      rw [h1]

      -- Calculate the result directly
      have : -(1 - (-1)) * lf = -(2 * lf) := by
        rw [@eq_neg_iff_add_eq_zero]
        ring_nf

      -- Now we have -(2 * lf) < 0, which is true when lf > 0
      have h3 : -(2 * lf) < 0 := by
        suffices 2 * lf > 0 by exact neg_neg_iff_pos.mpr this
        apply mul_pos
        · norm_num
        · exact h_pos

      -- Apply our calculation
      rw [this]

      -- We need to show -(2 * lf) < 0
      exact h3

    -- Complete the proof for this case
    exact sub_neg.mp h_diff_simplified

  · -- Case: local field is negative or zero
    push_neg at h_pos
    have h_neg : lf < 0 := by
      apply lt_of_le_of_ne
      · exact h_pos
      · exact h_lf_nonzero

    -- By the inconsistency condition, x i must be up (1)
    have h_x_is_up : x i = SpinState.up := by
      cases h : x i with
      | up => rfl
      | down =>
        have h_down_real : (x i).toReal = -1 := by rw [h]; rfl
        -- When x i is down (-1) and lf < 0, their product is positive
        have h_prod_pos : (x i).toReal * lf > 0 := by
          apply mul_pos_of_neg_of_neg
          · rw [h_down_real]; norm_num
          · exact h_neg
        -- When x i is down (-1) and lf < 0, their product is positive,
        -- which contradicts h_inconsistent
        rw [h_down_real] at h_inconsistent
        have h_contra := not_lt_of_gt h_prod_pos
        -- Rewrite h_inconsistent to match the form needed
        have h_inconsistent' : (x i).toReal * lf < 0 := by
          rw [h_down_real]
          exact h_inconsistent
        exact False.elim (h_contra h_inconsistent')

    -- The update must flip to down (-1)
    have h_x'_is_down : x' i = SpinState.down := by
      change updateState net x i i = SpinState.down
      unfold updateState
      simp
      simp_all only [ne_eq, neg_sub, ↓reduceIte,
        ite_eq_right_iff, reduceCtorEq, imp_false, not_lt, x', lf]

    -- Calculate the energy difference directly
    have h_diff_simplified : energy net x' - energy net x < 0 := by
      -- Start with the energy difference formula
      rw [h_energy_diff]

      -- Substitute the values for up and down states
      have h1 : (x' i).toReal - (x i).toReal = (-1) - 1 := by
        rw [h_x'_is_down, h_x_is_up]
        simp [SpinState.toReal]

      have h2 : (-1) - 1 = -2 := by ring

      -- Simplify the expression
      rw [h1]

      -- Distribute the negative
      have h3 : -(-2 * lf) = 2 * lf := by ring
      --rw [h3]

      -- Now we have 2 * lf < 0, which is true when lf < 0
      apply mul_neg_of_pos_of_neg
      · norm_num
      · exact h_neg

    -- Complete the proof for this case
    exact sub_neg.mp h_diff_simplified

/-!
`energy_decreases_on_update` proves that the energy of a Hopfield network decreases
(or stays the same) after updating the state of a single neuron.

The proof proceeds by cases:
1. If the sign of the local field and the neuron's state are inconsistent, then the energy decreases strictly.
2. If the sign of the local field and the neuron's state are consistent, then we further consider two subcases:
  a. If the local field is zero, then the energy remains the same.
  b. If the local field is non-zero, then the neuron's state is already aligned with the local field, so updating
  it will not change the state or the energy.
-/
@[simp]
lemma energy_decreases_on_update (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)
    (h_threshold_zero : net.thresholds i = 0) :
    energy net (updateState net x i) ≤ energy net x := by
  let lf := localField net x i

  by_cases h_inconsistent : (x i).toReal * lf < 0
  · exact le_of_lt (energy_decreases_on_update_with_inconsistent_signs net x i h_threshold_zero h_inconsistent)
  · push_neg at h_inconsistent
    let x' := updateState net x i
    have h_diff_j : ∀ j : Fin n, j ≠ i → x' j = x j :=
      fun j hj => Function.update_of_ne hj _ _
    have h_energy_diff := energy_diff_single_flip net x i h_threshold_zero x' h_diff_j
    by_cases h_lf_zero : lf = 0
    · simp at h_energy_diff
      -- When local field is zero, the energy difference is zero
      have h_energies_equal : energy net x' = energy net x := by
        rw [← sub_eq_zero]
        rw [h_energy_diff]
        simp [mul_zero]
        rw [← h_lf_zero]
        exact AffineMap.lineMap_eq_lineMap_iff.mp rfl

      -- Since x' is the updated state
      have h_x'_eq : x' = updateState net x i := rfl
      rw [h_energies_equal]

    · have h_same_sign : (x i).toReal = Real.sign lf := by
        cases h_x : x i with
        | down =>
          have h_xi_val : (x i).toReal = -1 := by rw [h_x]; rfl

          have h_lf_neg : lf < 0 := by
            have : -1 * lf ≥ 0 := by rw [← h_xi_val]; exact h_inconsistent
            have : lf ≤ 0 := by simpa using this
            exact lt_of_le_of_ne this h_lf_zero

          rw [← h_x]
          rw [h_xi_val]
          rw [← Real.sign_of_neg h_lf_neg]

        | up =>
          have h_xi_val : (x i).toReal = 1 := by rw [h_x]; rfl

          have h_lf_pos : lf > 0 := by
            have : 1 * lf ≥ 0 := by rw [← h_xi_val]; exact h_inconsistent
            have : lf ≥ 0 := by simpa using this
            exact lt_of_le_of_ne this (Ne.symm h_lf_zero)

          rw [← h_x, h_xi_val]
          exact Eq.symm (Real.sign_of_pos h_lf_pos)
      have h_x'_eq_x : x' = x := by
        ext j
        if h : j = i then
          subst h
          rw [← @Function.graph_id]
          simp [updateState, Real.sign_of_pos, Real.sign_of_neg, h_same_sign, h_lf_zero]
          change updateState net ?_ ?_ ?_ = ?_
          unfold updateState
          simp
          -- if lf > 0, then x j is up (1), and if lf < 0, then x j is down (-1)
          have h1 : lf > 0 ∨ lf < 0 := by exact lt_or_gt_of_ne fun a ↦ h_lf_zero (id (Eq.symm a))
          cases h1 with
          | inl h_pos =>
            have : x j = SpinState.up := by
              cases h_x_j : x j with
              | down =>
                have h_down : (x j).toReal = -1 := by rw [h_x_j]; rfl
                have h_lf_sign : lf.sign = 1 := Real.sign_of_pos h_pos
                rw [h_down, h_lf_sign] at h_same_sign
                exact eq_of_toReal_eq h_same_sign
              | up => rfl
            rw [this]
            simp [h_pos]
            exact fun a ↦ le_of_lt h_pos
          | inr h_neg =>
            have : x j = SpinState.down := by
              cases h_x_j : x j with
              | down => rfl
              | up =>
                have h_up : (x j).toReal = 1 := by rw [h_x_j]; rfl
                have h_lf_sign : lf.sign = -1 := Real.sign_of_neg h_neg
                rw [h_up, h_lf_sign] at h_same_sign
                exact eq_of_toReal_eq h_same_sign
            rw [this]
            simp [h_neg]
            exact le_of_lt h_neg
        else
          rw [h_diff_j j h]

      -- Since x' = x and x' = updateState net x i, we have updateState net x i = x
      rw [← h_x'_eq_x]
      rw [h_x'_eq_x]
      exact le_of_eq (congrArg (energy net) h_x'_eq_x)


/-
**Main Theorem: Energy monotonically decreases during network updates**

This theorem establishes that the energy of a Hopfield network monotonically decreases
during a sequence of state updates, when all thresholds are zero.

Inputs:
- `net : HopfieldNetwork n`: A Hopfield network with n neurons
- `x : HopfieldState n`: A state of the Hopfield network
- `h_zero_thresholds`: A hypothesis that all thresholds in the network are zero
- `seq : UpdateSeq net x`: A sequence of updates starting from state x

The theorem proves that the energy of the final state after updates is less than or
equal to the energy of the initial state.

The proof proceeds by induction on the update sequence:
- Base case: If the sequence is empty, the target state is the same as x
- Inductive case: Uses transitivity of inequality and the fact that each individual
  update decreases energy (from energy_decreases_on_update theorem)

-- TODO:
  More general formulation: Remove the h_threshold_zero condition, and modify the proof
  slightly to account for the threshold term in the energy difference
-/
@[simp]
theorem energy_monotonically_decreases {net : HopfieldNetwork n} {x : HopfieldState n}
    (h_zero_thresholds : ∀ i, net.thresholds i = 0)
    (seq : UpdateSeq net x) : energy net seq.target ≤ energy net x := by
  induction seq with
  | nil x' => simp [UpdateSeq.target]
  | cons x' i seq' ih =>
    simp only [UpdateSeq.target]
    exact le_trans ih (energy_decreases_on_update net x' i (h_zero_thresholds i))


/-!
# Energy Minimality at Fixed Points

This theorem proves that the energy of a Hopfield network is minimal at fixed points,
assuming zero thresholds.  Specifically, if a state `x` is a fixed point of the network
(i.e., updating any single spin leaves the state unchanged), and all thresholds are zero,
then changing the state of a single spin will not decrease the energy.

## Theorem Statement

Given:
- `net : HopfieldNetwork n`: A Hopfield network with `n` spins.
- `x : HopfieldState n`: A state of the Hopfield network.
- `h_fixed : UpdateSeq.isFixedPoint net x`: `x` is a fixed point of the network.
- `h_zero_thresholds : ∀ (i : Fin n), net.thresholds i = 0`: All thresholds of the network are zero.
- `y : HopfieldState n`: Another state of the Hopfield network.
- `i : Fin n`: An index of a spin.
- `h_diff_only_i : ∀ (j : Fin n), j ≠ i → y j = x j`: `y` differs from `x` only at index `i`.

Then:
`energy net x ≤ energy net y`: The energy of `x` is less than or equal to the energy of `y`.

## Proof Strategy

The proof proceeds by case analysis on the states of `x` and `y` at position `i`.
Since each spin can be either up or down, there are four cases:

1.  `x i = up, y i = up`: No change in spin, so the energy remains the same.
2.  `x i = up, y i = down`: The spin flips from up to down. Since `x` is a fixed point,
  the local field at `i` must be non-negative. Therefore, flipping the spin to down
  increases the energy.
3.  `x i = down, y i = up`: The spin flips from down to up. Since `x` is a fixed point,
  the local field at `i` must be non-positive. Therefore, flipping the spin to up
  increases the energy.
4.  `x i = down, y i = down`: No change in spin, so the energy remains the same.

In each case, we show that `energy net x ≤ energy net y`.

## Assumptions

- The thresholds of the Hopfield network are all zero. This simplifies the energy difference
  formula and allows us to relate the sign of the local field to the spin state at a fixed point.
-/
@[simp]
theorem energy_minimality_at_fixed_points (net : HopfieldNetwork n)
    (x : HopfieldState n) (h_fixed : UpdateSeq.isFixedPoint net x)
    (h_zero_thresholds : ∀ (i : Fin n), net.thresholds i = 0)
    (y : HopfieldState n) (i : Fin n)
    (h_diff_only_i : ∀ (j : Fin n), j ≠ i → y j = x j) :
    energy net x ≤ energy net y := by

  -- Get the local field at position i
  let lf := localField net x i

  -- Using the fixed point property: updateState net x i = x
  have h_update_eq_x : updateState net x i = x := by
    exact h_fixed i

  -- Apply the energy difference formula
  have h_energy_diff : energy net y - energy net x =
      -((y i).toReal - (x i).toReal) * lf := by
    exact energy_diff_single_flip net x i (h_zero_thresholds i) y h_diff_only_i

  -- Case analysis on the states of x and y at position i
  by_cases h_x_up : x i = SpinState.up
  · -- Case: x i = up
    by_cases h_y_up : y i = SpinState.up
    · -- Case: x i = up, y i = up
      -- No difference in energy if they're the same at position i
      rw [h_y_up, h_x_up] at h_energy_diff
      simp at h_energy_diff

      -- Since x is a fixed point: updateState net x i = x
      have h_update_eq_x' : updateState net x i = x := h_update_eq_x

      -- Therefore: energy net (updateState net x i) = energy net x
      have h_energy_eq : energy net (updateState net x i) = energy net x := by
        rw [h_update_eq_x']

      -- From h_energy_diff: energy net y = energy net x
      have h_energy_y_eq_x : energy net y = energy net x := by
        dsimp only
        rw [sub_eq_zero] at h_energy_diff
        exact h_energy_diff

      -- Combine the equalities to get the desired inequality
      rw [← h_fixed i]
      rw [h_fixed]
      exact le_of_eq (id (Eq.symm h_energy_y_eq_x))
    · -- Case: x i = up, y i = down
      -- Get the real values for these states
      have h_x_real : (x i).toReal = 1 := by
        cases h : x i
        case down =>
          have h_contra : up = down := by
            rw [← h_x_up, h]
          simp_all only [ne_eq, neg_sub, reduceCtorEq, lf]
        case up => rfl

      -- Since y i is not up (h_y_up), it must be down
      have h_y_down : y i = SpinState.down := by
        have h_y_not_up : ¬ y i = SpinState.up := h_y_up
        cases h : y i
        case down => rfl
        case up => contradiction

      have h_y_real : (y i).toReal = -1 := by
        rw [h_y_down]
        rfl

      -- Since x is a fixed point, the local field at i must have a sign consistent with x i
      have h_consistent_sign : lf ≥ 0 := by
        -- From the fixed point property, we know updateState doesn't change x i
        unfold updateState at h_update_eq_x
        simp at h_update_eq_x
        -- If updateState doesn't change x i from up, then either:
        -- 1) lf > 0 (which would set it to up), or
        -- 2) lf = 0 (which would leave it unchanged)
        -- In either case, lf ≥ 0
        by_cases h_lf_pos : 0 < lf
        · exact le_of_lt h_lf_pos
        · push_neg at h_lf_pos
          by_cases h_lf_neg : lf < 0
          · -- This case is impossible: if lf < 0, updateState would flip to down
            have h_would_update : updateState net x i i = SpinState.down := by
              unfold updateState
              simp [h_lf_neg]
              simp_all only [ne_eq, down_up_diff, neg_neg, reduceCtorEq, not_false_eq_true, ↓reduceIte,
                ite_eq_right_iff, imp_false, not_lt, lf]

            -- The update should have flipped the spin to down
            have h_update_down : updateState net x i i = SpinState.down := by
              unfold updateState
              simp [h_lf_neg]
              rw [← h_update_eq_x]
              rw [← h_zero_thresholds i]
              simp_all only [ne_eq, down_up_diff, neg_neg, reduceCtorEq, not_false_eq_true, ↓reduceIte,
                Function.update_self, ite_self, ite_eq_right_iff, imp_false, not_lt, lf]

            -- But x i is up, so updateState net x i i ≠ x i
            have h_neq : updateState net x i i ≠ x i := by
              rw [h_x_up]
              rw [h_update_down]
              simp

            -- This contradicts the assumption that x is a fixed point
            have h_contra : updateState net x i = x := h_update_eq_x
            have h_contra' : updateState net x i i = x i := by
              rw [h_fixed]
            exact False.elim (h_neq h_contra')

          · -- If not lf < 0 and not 0 < lf, then lf = 0
            push_neg at h_lf_neg
            exact h_lf_neg

      -- Substitute the real values into the energy difference
      rw [h_x_real, h_y_real] at h_energy_diff
      -- Simplify: -(-1 - 1) * lf = -((-2) * lf) = 2 * lf
      have h_diff_simplified : energy net y - energy net x = 2 * lf := by
        simp at h_energy_diff
        rw [h_energy_diff]
        ring

      -- Since lf ≥ 0 and we have 2 * lf, the difference is non-negative
      have h_energy_y_ge_x : energy net y - energy net x ≥ 0 := by
        rw [h_diff_simplified]
        exact mul_nonneg (by norm_num) h_consistent_sign

      -- Therefore, energy net x ≤ energy net y
      exact le_of_sub_nonneg h_energy_y_ge_x

  · -- Case: x i = down (not up)
    have h_x_down : x i = SpinState.down := by
      have h_x_not_up : ¬ x i = SpinState.up := h_x_up
      cases h : x i
      case down => rfl
      case up => contradiction

    by_cases h_y_up : y i = SpinState.up
    · -- Case: x i = down, y i = up
      -- Similar reasoning as the previous case
      have h_x_real : (x i).toReal = -1 := by rw [h_x_down]; rfl
      have h_y_real : (y i).toReal = 1 := by rw [h_y_up]; rfl

      -- Since x is a fixed point, the local field must have consistent sign with x i
      have h_consistent_sign : lf ≤ 0 := by
        -- If x i stays down at a fixed point, then either:
        -- 1) lf < 0 (which would set it to down), or
        -- 2) lf = 0 (which would leave it unchanged)
        unfold updateState at h_update_eq_x
        simp at h_update_eq_x
        by_cases h_lf_neg : lf < 0
        · exact le_of_lt h_lf_neg
        · push_neg at h_lf_neg
          by_cases h_lf_pos : 0 < lf
          · -- This case is impossible: if lf > 0, updateState would flip to up
            have h_would_update : updateState net x i i = SpinState.up := by
              unfold updateState
              simp [h_lf_pos]
              have h_contra : localField net x i ≤ 0 → False := by
                intro h
                exact not_le_of_gt h_lf_pos h
              intro a
              simp_all only [ne_eq, ite_self, up_down_diff, neg_mul, reduceCtorEq, not_false_eq_true,
                not_true_eq_false, lf]


            -- But we know x is a fixed point, so updateState net x i = x
            have h_contra : updateState net x i i = x i := by
              rw [h_fixed i]

            -- And we know x i = down
            rw [h_x_down] at h_contra

            -- This contradicts h_would_update
            have h_neq : SpinState.up ≠ SpinState.down := by simp
            rw [h_would_update] at h_contra
            exact False.elim (h_neq h_contra)

          · -- If not lf < 0 and not 0 < lf, then lf = 0
            push_neg at h_lf_pos
            exact h_lf_pos

      -- Substitute the real values into the energy difference
      rw [h_x_real, h_y_real] at h_energy_diff
      -- Simplify: -(1 - (-1)) * lf = -2 * lf
      have h_diff_simplified : energy net y - energy net x = -2 * lf := by
        simp at h_energy_diff
        rw [h_energy_diff]
        ring

      -- Since lf ≤ 0 and we have -2 * lf, the difference is non-negative
      have h_energy_y_ge_x : energy net y - energy net x ≥ 0 := by
        rw [h_diff_simplified]
        simp only [neg_mul, ge_iff_le, Left.nonneg_neg_iff]
        rw [@mul_nonpos_iff]
        rw [← h_zero_thresholds i] at h_consistent_sign
        rw [h_zero_thresholds] at h_consistent_sign
        constructor
        . norm_num
          simp_all only [ne_eq, neg_mul, sub_neg_eq_add, neg_add_rev, reduceCtorEq, not_false_eq_true, lf]

      -- Therefore, energy net x ≤ energy net y
      exact le_of_sub_nonneg h_energy_y_ge_x

    · -- Case: x i = down, y i = down
      -- No difference in energy if they're the same at position i
      have h_y_down : y i = SpinState.down := by
        cases h_y : y i
        case up =>
          contradiction
        case down =>
          rfl

      rw [h_y_down, h_x_down] at h_energy_diff
      simp at h_energy_diff

      -- Since the energy difference is zero
      have h_energy_equal : energy net y = energy net x := by
        rw [sub_eq_zero] at h_energy_diff
        exact h_energy_diff

      -- Use the fixed point property
      rw [← h_update_eq_x]

      -- Since energy net y = energy net x and x is a fixed point
      rw [h_energy_equal]
      rw [← h_fixed i]
      exact energy_decreases_on_update net (updateState net x i) i (h_zero_thresholds i)

section EnergyDecrease

open HopfieldState

variable {n : ℕ} (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)

/--
Energy difference between the updated state at index `i` and the original state.
`energy (updateState net x i) - energy x`.
-/
noncomputable def energyDiff (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) : ℝ :=
  energy net (updateState net x i) - energy net x

-- The energy difference is non-positive when the local field is zero
@[simp]
lemma energyDiff_eq_spinDiff_localField (h_zero_thresholds : ∀ i, net.thresholds i = 0):
    energyDiff net x i = -((updateState net x i i).toReal - (x i).toReal) * localField net x i := by
  unfold energyDiff
  let x' := updateState net x i
  have h_diff_j : ∀ j : Fin n, j ≠ i → x' j = x j :=
    fun j hj => Function.update_of_ne hj _ _
  have h_energy_diff := energy_diff_single_flip net x i (h_zero_thresholds i) x' h_diff_j
  exact h_energy_diff

-- The energy difference is non-positive when the local field is zero
@[simp]
lemma energy_decreasing (h_zero_thresholds : ∀ i, net.thresholds i = 0): energyDiff net x i ≤ 0 := by
  unfold energyDiff
  rw [sub_nonpos]
  apply energy_decreases_on_update
  apply h_zero_thresholds

-- The energy difference is strictly negative when the state changes and the local field is non-zero
@[simp]
lemma energy_strictly_decreasing_if_state_changes_and_localField_nonzero
    (h_zero_thresholds : ∀ i, net.thresholds i = 0):
  updateState net x i ≠ x → localField net x i ≠ 0 → energyDiff net x i < 0 := by
  intro h_update_ne h_lf_ne
  have h_inconsistent : (x i).toReal * localField net x i < 0 := by
    cases h_x : x i with
    | up =>
      have h_xi_real : (x i).toReal = 1 := by rw [h_x]; rfl
      have h_update_down : updateState net x i = Function.update x i SpinState.down := by
        unfold updateState
        simp [h_lf_ne]
        by_cases h_pos : 0 < localField net x i
        · exfalso
          -- When local field is positive and state is up, updateState preserves the state
          have h_update_up : updateState net x i = x := by
            ext j
            by_cases h_j : j = i
            · rw [h_j]
              unfold updateState
              simp [h_pos]
              rw [h_x]
            · exact Function.update_of_ne h_j _ _
          exact h_update_ne h_update_up
        · have h_neg : localField net x i < 0 := by
            push_neg at h_pos
            exact lt_of_le_of_ne h_pos h_lf_ne
          simp [h_neg]
          rw [← h_zero_thresholds i]
          -- Show that the condition is false, so we get down
          have h_cond : ¬(net.thresholds i < localField net x i) := by
            rw [h_zero_thresholds i]
            simp
            exact le_of_lt h_neg
          simp [h_cond]
      have h_lf_neg : localField net x i < 0 := by
        by_cases h_pos : 0 < localField net x i
        · -- If local field is positive, updateState would preserve up state
          have h_preserve : updateState net x i i = SpinState.up := by
            unfold updateState
            simp [h_pos]
          rw [h_update_down] at h_update_ne
          rw [← h_zero_thresholds i]
          simp_all only [ne_eq, Function.update_self, reduceCtorEq]
        · -- Since local field is not positive and not zero (h_lf_ne),
          -- it must be negative
          push_neg at h_pos
          exact lt_of_le_of_ne h_pos h_lf_ne
      simp_all only [ne_eq, one_mul]
    | down =>
      have h_xi_real : (x i).toReal = -1 := by rw [h_x]; rfl
      have h_update_up : updateState net x i = Function.update x i SpinState.up := by
        unfold updateState
        simp

      -- Since updateState changes the state (h_update_ne) and x i is down,
      -- we must have localField net x i > 0
        have h_lf_pos : 0 < localField net x i := by
          by_cases h_pos : 0 < localField net x i
          · exact h_pos
          · push_neg at h_pos
            by_cases h_neg : localField net x i < 0
            · -- If local field is negative, updateState would keep it down
              have h_stays_down : updateState net x i = x := by
                ext j
                by_cases h_j : j = i
                · rw [h_j]
                  unfold updateState
                  simp [h_neg]
                  rw [h_x]
                  rw [← h_zero_thresholds i]
                  rw [← h_j]
                  subst h_j
                  simp_all only [ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false, not_lt]
                · exact Function.update_of_ne h_j _ _
              contradiction
            · -- If not positive and not negative, must be zero
              push_neg at h_neg
              have h_zero : localField net x i = 0 := by
                exact le_antisymm h_pos h_neg
              contradiction

        -- When local field is positive, updateState flips to up
        simp_all only [ne_eq, ↓reduceIte]
      have h_lf_pos : localField net x i > 0 := by
        have h_update_ne' : updateState net x i i ≠ x i := by
          unfold updateState at h_update_ne
          simp at h_update_ne
          have h_eq : updateState net x i i = Function.update x i (if 0 < localField net x i then up else if localField net x i < 0 then down else x i) i := by
            rfl
          rw [h_eq]
          intro h_absurd
          apply h_update_ne
          ext j
          by_cases h_j : j = i
          · rw [h_j, Function.update_self]
            rw [h_x]
            simp
            by_cases h_pos : 0 < localField net x i
            · rw [← h_zero_thresholds i]
              subst h_j
              simp_all only [↓reduceIte, ne_eq, Function.update_self, reduceCtorEq]
            · rw [← h_zero_thresholds i]
              subst h_j
              simp_all only [↓reduceIte, ite_self, ne_eq, Function.update_self, reduceCtorEq]
          · rw [Function.update_of_ne h_j]
        have h_update_up' : updateState net x i i = SpinState.up := by
          unfold updateState
          simp

          rw [← h_x]
          simp
          by_cases h_lf_neg : localField net x i < 0
          · intro h_le
            exfalso
            -- Local field is both less than zero and less than or equal to zero
            have h_contra := lt_of_le_of_ne h_le h_lf_ne
            have h_not_lf_neg : ¬(localField net x i < 0) := by
              have h_pos : 0 < localField net x i := by
                push_neg at h_lf_neg
                -- Since local field is not negative (h_lf_neg) and not zero (h_lf_ne),
                -- it must be positive
                -- This is a contradiction because we already know the field is negative
                exfalso
                -- We have both:
                -- h_lf_neg : localField net x i < 0
                -- h_update_ne : updateState net x i ≠ x
                -- For a down state with negative field, updateState should not change it
                have h_no_update : updateState net x i = x := by
                  ext j
                  by_cases h_j : j = i
                  · rw [h_j]
                    unfold updateState
                    simp [h_lf_neg]
                    rw [h_x]
                    subst h_j
                    simp_all only [ne_eq, Function.update_self, reduceCtorEq, not_false_eq_true, ite_eq_right_iff,
                      imp_false, not_lt]
                  · exact Function.update_of_ne h_j _ _
                exact h_update_ne h_no_update
              exact not_lt_of_gt h_pos
            exact h_not_lf_neg h_lf_neg
          rw [h_x]
          simp
          -- Since we've eliminated the negative case, and the local field is not zero (h_lf_ne),
          -- it must be positive
          push_neg at h_lf_neg
          exact lt_of_le_of_ne h_lf_neg (id (Ne.symm h_lf_ne))
        rw [h_x] at h_update_ne'
        rw [h_update_up'] at h_update_ne'
        simp at h_update_ne'

        -- Since the updateState changes the state from down to up,
        -- the local field must be positive
        by_cases h_pos : 0 < localField net x i
        · exact h_pos
        · push_neg at h_pos
          have h_no_change : updateState net x i i = x i := by
            unfold updateState
            simp
            rw [h_x]
            by_cases h_neg : localField net x i < 0
            · rw [← h_zero_thresholds i]
              simp_all only [ne_eq, ↓reduceIte, ite_eq_right_iff, reduceCtorEq, imp_false, not_lt]
            · push_neg at h_neg
              have h_zero : localField net x i = 0 := by
                exact le_antisymm h_pos h_neg
              simp [h_zero]
          rw [← h_zero_thresholds i]
          simp_all only [ne_eq, reduceCtorEq]

      exact mul_neg_of_neg_of_pos (by exact neg_one_lt_zero) h_lf_pos
  unfold energyDiff
  rw [sub_neg]
  exact
    energy_decreases_on_update_with_inconsistent_signs net x i (h_zero_thresholds i) h_inconsistent

-- The energy difference is zero if the state doesn't change
@[simp]
lemma energy_fixed_point_iff_no_change (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n)
    (h_zero_thresholds : ∀ i, net.thresholds i = 0) :
  energyDiff net x i = 0 ↔ updateState net x i = x := by
  constructor
  · -- (⟹) If energy doesn't change, the state doesn't change
    intro h_energy_eq
    unfold energyDiff at h_energy_eq
    dsimp only

    by_cases h_update_eq : updateState net x i = x
    · -- If already equal, we're done
      exact h_update_eq
    · -- If not equal, we get a contradiction with h_energy_eq
      have h_lf_nonzero : localField net x i ≠ 0 := by
        -- Proof that if update changes the state, local field must be nonzero
        intro h_lf_zero
        have h_update_same : updateState net x i = x := by
          -- Show that if local field is zero, update doesn't change state
          ext j
          by_cases h_j : j = i
          · -- For position i
            subst h_j
            unfold updateState
            simp [h_lf_zero]
          · -- For positions j ≠ i
            exact Function.update_of_ne h_j _ _
        contradiction  -- Contradicts h_update_eq

      have h_energy_decrease : energy net (updateState net x i) < energy net x := by
        have h_energy_diff_neg : energyDiff net x i < 0 := by
          apply energy_strictly_decreasing_if_state_changes_and_localField_nonzero net x i h_zero_thresholds
          · exact h_update_eq  -- State changes
          · exact h_lf_nonzero  -- Local field is nonzero
        -- Convert from energyDiff to energy difference
        unfold energyDiff at h_energy_diff_neg
        exact sub_neg.mp h_energy_diff_neg

      -- This contradicts our assumption that energy doesn't change
      have h_contradiction : energy net (updateState net x i) ≠ energy net x := by
        exact ne_of_lt h_energy_decrease

      --simp_all only [ne_eq]
      linarith  -- Contradicts h_energy_eq

  · -- (⟸) If state doesn't change, energy doesn't change
    intro h_update_eq
    unfold energyDiff
    rw [← h_zero_thresholds i]
    rw [h_update_eq]
    simp_all only [sub_self]
