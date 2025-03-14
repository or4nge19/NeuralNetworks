import HopfieldNetworks.Basic
import HopfieldNetworks.Tactic

open SpinState HopfieldState UpdateSeq

variable {n : ℕ}

/--
Energy difference after updating neuron `i` from state `x` to `x' = updateState net x i`.
Shows that energy decreases (or stays the same) with each update.
-/
lemma energy_diff_update {net : HopfieldNetwork n} {x : HopfieldState n} (i : Fin n) :
  let x' := updateState net x i
  0 ≤ energy net x - energy net x' := by
  let x' := updateState net x i
  let W := weightsMatrix net
  let θ := net.thresholds
  let xVec := toRealVector x
  let x'Vec := toRealVector x'
  let xi := x i
  let x'i := x' i
  let xiR := xi.toReal
  let x'iR := x'i.toReal
  let lf := localField net x i
  have h_x'_diff_x : x'Vec i - xVec i = x'iR - xiR := by exact rfl
  have h_x'_eq_x_except_i : ∀ j, j ≠ i → x'Vec j = xVec j := by
    intro j hji
    congr
    aesop

  -- Expand energy difference E(x) - E(x')
  have energy_diff : energy net x - energy net x' =
    (-0.5 * (W.toBilin' xVec xVec) - (θ ⬝ᵥ xVec)) - (-0.5 * (W.toBilin' x'Vec x'Vec) - (θ ⬝ᵥ x'Vec)) := rfl
  have energy_diff_simplified : energy net x - energy net x' =
    -0.5 * (W.toBilin' xVec xVec - W.toBilin' x'Vec x'Vec) - (θ ⬝ᵥ xVec - θ ⬝ᵥ x'Vec) := by
    rw [energy_diff]
    ring

  have energy_diff_simplified2 : energy net x - energy net x' =
    -- rw [Matrix.vecMul_sub] -- Not applicable here
    -- Use h_x'_diff_x and h_x'_eq_x_except_i to show that the difference vector only has a non-zero entry at i
    have h_x'_minus_x : x'Vec - xVec = Matrix.col_empty (Fin n) (fun _ => 0) := by
      ext j
      by_cases hji : j = i
      · simp [hji, h_x'_diff_x]
        simp
      · have h_x'_eq_x_j : x'Vec j = xVec j := h_x'_eq_x_except_i j hji
        simp [h_x'_eq_x_j]
      · have h_x'_eq_x_j : x'Vec j = xVec j := h_x'_eq_x_except_i j hji
        rw [h_x'_eq_x_j]
        simp

  have energy_diff_simplified3 : energy net x - energy net x' =
    -0.5 * (W.toBilin' xVec xVec - W.toBilin' x'Vec x'Vec) + (θ ⬝ᵥ (x'Vec - xVec)) := by
    rw [energy_diff_simplified2]
    -- Simplify the goal algebraically
    have h1 : θ ⬝ᵥ xVec - θ ⬝ᵥ x'Vec = θ ⬝ᵥ (xVec - x'Vec) := by
      rw [Matrix.vecMul_sub]

    have h2 : -θ ⬝ᵥ (xVec - x'Vec) = θ ⬝ᵥ (x'Vec - xVec) := by
      simp only [Matrix.vecMul_neg, neg_sub]

    -- Prove the goal step by step
    conv =>
      rhs
      rw [add_comm]
      congr
      rw [h2]

    conv =>
      lhs
      congr
      congr; skip
      conv =>
        rhs
        rw [← neg_neg (θ ⬝ᵥ (xVec - x'Vec))]
        rw [← h2]

    ring
    -- Expand the bilinear form difference
  _ = -0.5 * (∑ j in Finset.univ, ∑ k in Finset.univ, W j k * xVec j * xVec k -
               ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * x'Vec j * x'Vec k) + (θ ⬝ᵥ (x'Vec - xVec)) := by
      simp [Matrix.toBilin'_apply]
      rw [Finset.sum_sub_distrib]
      simp
  _ = -0.5 * (∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)) + (θ ⬝ᵥ (x'Vec - xVec)) := by
      rw [Finset.sum_sub_distrib]
  _ = -0.5 * (∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)) + ∑ j in Finset.univ, θ j * (x'Vec j - xVec j) := by
      simp [Matrix.vecMul_apply]
  _ = -0.5 * (∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)) + θ i * (x'Vec i - xVec i) + ∑ j in Finset.univ.filter (fun j => j ≠ i), θ j * (x'Vec j - xVec j) := by
      rw [Finset.sum_insert (Finset.not_mem_filter.mpr (by simp))]
      simp
  _ = -0.5 * (∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)) + θ i * (x'Vec i - xVec i) + 0 := by
      simp
      apply Finset.sum_eq_zero
      intros j hji
      simp [h_x'_eq_x_except_i j hji]

  -- Focus on the bilinear form difference part.
  have bilinear_diff_term :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ, W i k * (xVec i * xVec k - x'Vec i * x'Vec k) +
      ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k) := by
      rw [Finset.sum_insert (Finset.not_mem_filter.mpr (by simp))]
      simp

  -- Further expand the first term of bilinear_diff_term (j=i)
  have bilinear_diff_i_term :
    ∑ k in Finset.univ, W i k * (xVec i * xVec k - x'Vec i * x'Vec k)
    = W i i * (xVec i * xVec i - x'Vec i * x'Vec i) +
      ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k) := by
      rw [Finset.sum_insert (Finset.not_mem_filter.mpr (by simp))]
      simp

  -- Since W.diag = 0, W i i = 0
  have W_ii_zero : W i i = 0 := weights_diag_zero net i

  -- Simplify bilinear_diff_i_term using W_ii_zero
  have bilinear_diff_i_term_simp :
    ∑ k in Finset.univ, W i k * (xVec i * xVec k - x'Vec i * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k) := by
      rw [bilinear_diff_i_term]
      simp [W_ii_zero]

  -- Rewrite bilinear_diff_term using bilinear_diff_i_term_simp
  have bilinear_diff_term_simp :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k) +
      ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k) := by
      rw [bilinear_diff_term, bilinear_diff_i_term_simp]

  -- Use symmetry of W: W k i = W i k
  have W_symm : ∀ j k, W j k = W k j := Matrix.IsSymm.eq_symm (weights_symmetric net)

  -- Rewrite the first sum in bilinear_diff_term_simp by swapping j and k and using W_symm
  have swapped_sum_term :
    ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W k j * (xVec j * xVec k - x'Vec j * x'Vec k) := by
      rw [Finset.sum_comm]

  have swapped_sum_term_symm :
    ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W j k * (xVec k * xVec j - x'Vec k * x'Vec j) := by
      rw [swapped_sum_term]
      apply Finset.sum_congr rfl
      intros k _
      apply Finset.sum_congr rfl
      intros j _
      rw [W_symm k j]

  -- Split the inner sum of swapped_sum_term_symm into k=i and k≠i parts
  have swapped_sum_term_symm_split :
    ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W j k * (xVec k * xVec j - x'Vec k * x'Vec j)
    = ∑ j in Finset.univ, W j i * (xVec i * xVec j - x'Vec i * x'Vec j) +
      ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W j k * (xVec k * xVec j - x'Vec k * x'Vec j) := by
      rw [Finset.sum_insert (Finset.not_mem_filter.mpr (by simp))]
      simp

  -- Consider the term ∑ j in Finset.univ, W j i * (xVec i * xVec j - x'Vec i * x'Vec j)
  have term_Wji :
    ∑ j in Finset.univ, W j i * (xVec i * xVec j - x'Vec i * x'Vec j)
    = W i i * (xVec i * xVec i - x'Vec i * x'Vec i) +
      ∑ j in Finset.univ.filter (fun j => j ≠ i), W j i * (xVec i * xVec j - x'Vec i * x'Vec j) := by
      rw [Finset.sum_insert (Finset.not_mem_filter.mpr (by simp))]
      simp

  -- Simplify using W_ii_zero
  have term_Wji_simp :
    ∑ j in Finset.univ, W j i * (xVec i * xVec j - x'Vec i * x'Vec j)
    = ∑ j in Finset.univ.filter (fun j => j ≠ i), W j i * (xVec i * xVec j - x'Vec i * x'Vec j) := by
      rw [term_Wji]
      simp [W_ii_zero]

  -- Rewrite swapped_sum_term_symm_split using term_Wji_simp
  have swapped_sum_term_symm_split_simp :
    ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W j k * (xVec k * xVec j - x'Vec k * x'Vec j)
    = ∑ j in Finset.univ.filter (fun j => j ≠ i), W j i * (xVec i * xVec j - x'Vec i * x'Vec j) +
      ∑ k in Finset.univ.filter (fun k => k ≠ i), ∑ j in Finset.univ, W j k * (xVec k * xVec j - x'Vec k * x'Vec j) := by
      rw [swapped_sum_term_symm_split, term_Wji_simp]
      rw [W_symm i j]

  -- Put it all together for bilinear_diff_term_simp
  have bilinear_diff_term_final :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k) +
      ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k) := by
      rw [bilinear_diff_term_simp]

  -- Consider the term ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k)
  have term1 : ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * ((xVec i - x'Vec i) * xVec k + x'Vec i * (xVec k - x'Vec k)) := by
      apply Finset.sum_congr rfl
      intros k _
      ring

  -- Since for k ≠ i, xVec k = x'Vec k, then xVec k - x'Vec k = 0
  have x_eq_x' : ∀ k, k ≠ i → xVec k = x'Vec k := h_x'_eq_x_except_i

  -- Simplify term1 using x_eq_x'
  have term1_simp : ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i * xVec k - x'Vec i * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i - x'Vec i) * xVec k := by
      apply Finset.sum_congr rfl
      intros k _
      simp [x_eq_x' k]

  -- Consider the term ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
  have term2 : ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - xVec j * x'Vec k) := by
      apply Finset.sum_congr rfl
      intros j _
      apply Finset.sum_congr rfl
      intros k _
      simp [x_eq_x' j, x_eq_x' k]

  -- Simplify term2
  have term2_simp : ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * xVec j * (xVec k - x'Vec k) := by
      rw [term2]
      apply Finset.sum_congr rfl
      intros j _
      apply Finset.sum_congr rfl
      intros k _
      ring

  -- Since for k ≠ i, xVec k = x'Vec k, then xVec k - x'Vec k = 0
  have x_eq_x'_again : ∀ k, k ≠ i → xVec k = x'Vec k := h_x'_eq_x_except_i

  -- Simplify term2_simp further
  have term2_simp_zero : ∑ j in Finset.univ.filter (fun j => j ≠ i), ∑ k in Finset.univ, W j k * xVec j * (xVec k - x'Vec k) = 0 := by
    apply Finset.sum_eq_zero
    intros j _
    apply Finset.sum_eq_zero
    intros k hki
    simp [x_eq_x'_again k hki]


  -- Put term1_simp and term2_simp_zero back into bilinear_diff_term_final
  have bilinear_diff_term_final_simp :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i - x'Vec i) * xVec k + 0 := by
      rw [bilinear_diff_term_final, term1_simp, term2_simp_zero]

  -- Simplify bilinear_diff_term_final_simp
  have bilinear_diff_term_final_simp2 :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i - x'Vec i) * xVec k := by
      simp [bilinear_diff_term_final_simp]

  -- Rewrite the sum in bilinear_diff_term_final_simp2 by separating k=i and k≠i
  have sum_split :
    ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i - x'Vec i) * xVec k
    = ∑ k in Finset.univ, W i k * (xVec i - x'Vec i) * xVec k - W i i * (xVec i - x'Vec i) * xVec i := by
      rw [Finset.sum_diff_filter]
      simp

  -- Simplify sum_split using W_ii_zero
  have sum_split_simp :
    ∑ k in Finset.univ.filter (fun k => k ≠ i), W i k * (xVec i - x'Vec i) * xVec k
    = ∑ k in Finset.univ, W i k * (xVec i - x'Vec i) * xVec k := by
      rw [sum_split]
      simp [W_ii_zero]

  -- Rewrite bilinear_diff_term_final_simp2 using sum_split_simp
  have bilinear_diff_term_final_simp3 :
    ∑ j in Finset.univ, ∑ k in Finset.univ, W j k * (xVec j * xVec k - x'Vec j * x'Vec k)
    = ∑ k in Finset.univ, W i k * (xVec i - x'Vec i) * xVec k := by
      rw [bilinear_diff_term_final_simp2, sum_split_simp]

  -- Rewrite energy difference using bilinear_diff_term_final_simp3
  _ = -0.5 * (∑ k in Finset.univ, W i k * (xVec i - x'Vec i) * xVec k) + θ i * (x'Vec i - xVec i) := by
      rw [bilinear_diff_term_final_simp3]

  -- Factor out (x'Vec i - xVec i)
  _ = (x'Vec i - xVec i) * (θ i - 0.5 * ∑ k in Finset.univ, W i k * xVec k) := by
      ring_nf
      rw [smul_sum]
      ring

  _ = (x'Vec i - xVec i) * (-(∑ k in Finset.univ, W i k * xVec k - θ i)) := by
      ring

  _ = - (x'Vec i - xVec i) * ((∑ k in Finset.univ, W i k * xVec k) - θ i) := rfl

  _ = - (x'Vec i - xVec i) * localField net x i := rfl

  _ = (xVec i - x'Vec i) * localField net x i := by rw [neg_mul_neg (-1) _]

  _ = (xiR - x'iR) * lf := rfl

  -- Case analysis based on update rule
  by_cases h_lf_pos : 0 < lf
  · have h_x'_i_eq_up : x' i = up := by simp [updateState, h_lf_pos]
    have h_x'_iR_eq_1 : x'iR = 1 := by rw [h_x'_i_eq_up]; simp [SpinState.toReal]
    have h_xiR_minus_x'iR : xiR - x'iR = xiR - 1 := by rw [h_x'_iR_eq_1]
    -- If lf > 0, then x'i = up (1). If x i was down (-1), energy decreases. If x i was up (1), no change, energy stays the same (lf <= 0 case).
    by_cases h_xi_eq_down : xi = down
    · have h_xiR_eq_neg_1 : xiR = -1 := by rw [h_xi_eq_down]; simp [SpinState.toReal]
      have h_xiR_minus_x'iR_neg2 : xiR - x'iR = -2 := by rw [h_xiR_eq_neg_1, h_x'_iR_eq_1]; norm_num
      have energy_diff_val : (xiR - x'iR) * lf = -2 * lf := by rw [h_xiR_minus_x'iR_neg2]
      have energy_diff_nonneg : 0 ≤ energy net x - energy net x' := by
        rw [energy_diff_val]
        exact Real.le_of_mul_nonneg_left (by norm_num) (by assumption)
      exact energy_diff_nonneg
    · have h_xi_neq_down : xi ≠ down := h_xi_eq_down
      have h_xi_eq_up : xi = up := by cases xi; assumption; assumption
      have h_xiR_eq_1 : xiR = 1 := by rw [h_xi_eq_up]; simp [SpinState.toReal]
      have h_xiR_minus_x'iR_zero : xiR - x'iR = 0 := by rw [h_xiR_eq_1, h_x'_iR_eq_1]; norm_num
      have energy_diff_zero : (xiR - x'iR) * lf = 0 := by rw [h_xiR_minus_x'iR_zero]; simp
      simp [energy_diff_zero]
  · by_cases h_lf_neg : lf < 0
    · have h_x'_i_eq_down : x' i = down := by simp [updateState, h_lf_neg]
      have h_x'_iR_eq_neg_1 : x'iR = -1 := by rw [h_x'_i_eq_down]; simp [SpinState.toReal]
      have h_xiR_minus_x'iR : xiR - x'iR = xiR - (-1) := by rw [h_x'_iR_eq_neg_1]; simp
      by_cases h_xi_eq_up : xi = up
      · have h_xiR_eq_1 : xiR = 1 := by rw [h_xi_eq_up]; simp [SpinState.toReal]
        have h_xiR_minus_x'iR_pos2 : xiR - x'iR = 2 := by rw [h_xiR_eq_1, h_x'_iR_eq_neg_1]; norm_num
        have energy_diff_val : (xiR - x'iR) * lf = 2 * lf := by rw [h_xiR_minus_x'iR_pos2]
        have energy_diff_nonneg : 0 ≤ energy net x - energy net x' := by
          rw [energy_diff_val]
          exact Real.le_of_mul_nonneg_right (by norm_num) (by linarith)
        exact energy_diff_nonneg
      · have h_xi_neq_up : xi ≠ up := h_xi_eq_up
        have h_xi_eq_down : xi = down := by cases xi; assumption; assumption
        have h_xiR_eq_neg_1 : xiR = -1 := by rw [h_xi_eq_down]; simp [SpinState.toReal]
        have h_xiR_minus_x'iR_zero : xiR - x'iR = 0 := by rw [h_xiR_eq_neg_1, h_x'_iR_eq_neg_1]; norm_num
        have energy_diff_zero : (xiR - x'iR) * lf = 0 := by rw [h_xiR_minus_x'iR_zero]; simp
        simp [energy_diff_zero]
  · have h_lf_eq_zero : lf = 0 := by linarith
    have h_x'_i_eq_xi : x' i = xi := by simp [updateState, h_lf_eq_zero]
    have h_x'_iR_eq_xiR : x'iR = xiR := by rw [h_x'_i_eq_xi]
    have h_xiR_minus_x'iR_zero : xiR - x'iR = 0 := by rw [h_x'_iR_eq_xiR]; simp
    have energy_diff_zero : (xiR - x'iR) * lf = 0 := by rw [h_xiR_minus_x'iR_zero]; simp
    simp [energy_diff_zero]
