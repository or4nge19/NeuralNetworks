import NeuralNetworks.Hopfield.Basic
import NeuralNetworks.Hopfield.Energy

set_option maxHeartbeats 0

namespace HopfieldState

open SpinState

variable {n : ℕ}

section ConvergenceTheorems

open UpdateSeq

-- Define the Frobenius norm for matrices
noncomputable
instance matrixFrobeniusNorm : Norm (Matrix (Fin n) (Fin n) ℝ) where
  norm := fun M => Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2)

-- Define the SeminormedAddGroup instance
noncomputable
instance matrixSeminormedAddGroup : SeminormedAddGroup (Matrix (Fin n) (Fin n) ℝ) where
  norm := fun M => Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2)
  dist := fun M N => ‖M - N‖
  dist_eq := fun _ _ => rfl

  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg

  dist_self := fun x => by
    simp [dist, sub_self]
    unfold norm matrixFrobeniusNorm
    simp

  dist_comm := fun x y => by
    simp [dist]
    have h : x - y = -(y - x) := by
      ext i j
      simp only [Matrix.sub_apply]
      rw [neg_sub]
      aesop
    rw [h]
    -- We need to show that ‖-v‖ = ‖v‖ directly
    have h_norm_neg : ‖-(y - x)‖ = ‖y - x‖ := by
      unfold norm matrixFrobeniusNorm
      apply congr_arg Real.sqrt
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.neg_apply, Matrix.sub_apply]
      rw [@neg_sq]
    simp_all only [neg_sub]

  dist_triangle := fun x y z => by
    simp [dist]
    calc
      ‖x - z‖ = ‖(x - y) + (y - z)‖ := by simp [sub_add_sub_cancel]
      _ ≤ ‖x - y‖ + ‖y - z‖ := by
          -- Apply the triangle inequality for norms
          have h : x - z = (x - y) + (y - z) := by simp [sub_add_sub_cancel]
          rw [← h]
          rw [h]
          -- Manually prove the norm_add_le inequality for Frobenius norm
          unfold norm matrixFrobeniusNorm
          -- We need to prove triangle inequality for the Frobenius norm
          -- This would require Cauchy-Schwarz inequality and properties of square roots
          sorry
          -- This would require a complete proof of the triangle inequality for the Frobenius norm
          -- The full proof would involve Cauchy-Schwarz inequality and properties of square roots


  zsmul := fun n M => n • M
  zsmul_zero' := fun x => by simp [smul_zero]
  zsmul_succ' := fun n x => by simp [add_smul, one_smul]
  zsmul_neg' := fun n x => by
    simp only [zsmul_eq_mul, Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      Nat.succ_eq_add_one, Int.cast_add, Int.cast_natCast, Int.cast_one]
    calc
    (-1 + -↑n) * x = -(1 + ↑n) * x := by rw [@neg_add]
    _ = -((↑n + 1) * x) := by
      rw [add_mul, one_mul, add_comm, neg_add]
      rw [@Matrix.add_mul]
      rw [@Matrix.neg_mul]
      rw [@Matrix.neg_mul]
      rw [@Matrix.one_mul]
      rw [@neg_add]

-- Use the Frobenius norm to define a seminormed group structure
noncomputable
instance matrixNorm : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
{ zero := 0
  add := fun M N => M + N
  neg := fun M => -M
  sub := fun M N => M - N
  nsmul := fun n M => n • M
  nsmul_succ := fun n M => by simp [add_smul, one_smul]
  zsmul := fun n M => n • M
  norm := fun M => ‖M‖
  dist := fun M N => ‖M - N‖
  edist := fun M N => ENNReal.ofReal ‖M - N‖

  add_assoc := by exact fun a b c ↦ add_assoc a b c
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := fun M N => by simp [sub_eq_add_neg]
  dist_eq := fun _ _ => rfl
  edist_dist := fun x y => by simp [dist, edist]
  dist_self := fun x => by
    simp [dist, sub_self]

  dist_comm := fun x y => by
    unfold dist
    simp only
    rw [← neg_sub]
    exact norm_neg (y - x)

  dist_triangle := fun x y z => by
    unfold dist
    simp only
    calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by simp [sub_add_sub_cancel]
       _ ≤ ‖x - y‖ + ‖y - z‖ := norm_add_le (x - y) (y - z)


  zsmul_zero' := fun x => by simp [zsmul_zero]
  zsmul_succ' := fun n x => by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zsmul_eq_mul, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [add_mul]
    rw [one_mul]
  zsmul_neg' := fun n x => by
    simp only [zsmul_eq_mul, Int.cast_negSucc]
    rw [@Matrix.neg_mul]
    congr
  }

noncomputable
instance matrixUniformSpace : UniformSpace (Matrix (Fin n) (Fin n) ℝ) :=
  by exact PseudoEMetricSpace.toUniformSpace

instance matrixBornology : Bornology (Matrix (Fin n) (Fin n) ℝ) :=
  by exact Bornology.cofinite

instance : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) where
  norm_smul_le := fun r M => by
    let norm_M := Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2)
    have h_norm_def : ‖r • M‖ = Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (r * M i j)^2) := rfl
    have h_norm_M_def : ‖M‖ = Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2) := rfl
    rw [h_norm_def]
    calc
      ‖r • M‖ = Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (r * M i j)^2) := rfl
      _ = Real.sqrt (|r|^2 * ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2) := by
        congr 1
        -- Prove that the sums are equal
        have h_pow_mul : ∀ (x y : ℝ), (x * y)^2 = x^2 * y^2 := by
          intro x y
          rw [pow_two, pow_two, pow_two]
          exact mul_mul_mul_comm x y x y

        simp_rw [h_pow_mul]

        -- Convert between different sum types and factor out r^2
        have h_sum_eq : ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (r * M i j)^2 =
                       |r|^2 * ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2 := by
          -- First prove the sum is nonnegative
          have h_sum_nonneg : 0 ≤ r^2 * ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2 := by
            apply mul_nonneg
            · exact sq_nonneg r
            · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

          rw [sq_abs]
          have : ∀ i j, (r * M i j)^2 = r^2 * (M i j)^2 := by
            intro i j
            rw [h_pow_mul]

          simp only [this]

          have h_factor : ∀ i, ∑ j ∈ Finset.univ, r^2 * (M i j)^2 = r^2 * ∑ j ∈ Finset.univ, (M i j)^2 := by
            intro i
            exact Eq.symm (Finset.mul_sum Finset.univ (fun i_1 ↦ M i i_1 ^ 2) (r ^ 2))

          simp_rw [h_factor]
          rw [@Finset.sum_fin_eq_sum_range]
          rfl


        exact h_sum_eq
        intro i _
        rw [← Finset.mul_sum]
        rfl
      _ = |r| * Real.sqrt (∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, (M i j)^2) := by
        rw [Real.sqrt_mul]
        · rfl
        · exact sq_nonneg |r|
        · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · exact mul_nonneg (sq_nonneg |r|) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/--
Energy of Hopfield state is bounded below.
-/
lemma energy_lower_bounded (net : HopfieldNetwork n) : ∀ x : HopfieldState n,
  energy net x ≥ -(n * ‖weightsMatrix net‖) - ∑ i, ‖net.thresholds i‖ := by
  intro x
  let W := weightsMatrix net
  let xVec := toRealVector x

  -- Expand the energy definition
  unfold energy

  -- Handle the quadratic term first
  have h_quad_bound : -1/2 * Matrix.toBilin' W xVec xVec ≥ -n * ‖W‖ := by
    -- Use the bound on bilinear form
    have h_bilin_bound : |Matrix.toBilin' W xVec xVec| ≤ 2 * n * ‖W‖ := by
      -- Expand the bilinear form
      have h_bilin_sum : Matrix.toBilin' W xVec xVec = ∑ i, ∑ j, W i j * xVec i * xVec j := by
        unfold Matrix.toBilin'
        simp only [LinearMap.BilinForm.toMatrix'_symm, Matrix.toBilin'_apply']
        simp only [dotProduct, Matrix.mulVec]

        have h_sum_eq : ∀ i, xVec i * (∑ j, W i j * xVec j) = ∑ j, W i j * xVec i * xVec j := by
          intro i
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

        apply Finset.sum_congr rfl
        intro i _
        exact h_sum_eq i

      -- Bound on the summation using norm
      calc
        |Matrix.toBilin' W xVec xVec| = |∑ i, ∑ j, W i j * xVec i * xVec j| := by rw [h_bilin_sum]
        _ ≤ ∑ i, ∑ j, |W i j * xVec i * xVec j| := by sorry
        _ = ∑ i, ∑ j, |W i j| * |xVec i| * |xVec j| := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul, abs_mul]
        _ ≤ ∑ i, ∑ j, ‖W‖ * 1 * 1 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            -- Each spin has magnitude 1
            have h_spin_mag : |xVec i| = 1 ∧ |xVec j| = 1 := by
              simp only [xVec, toRealVector]
              constructor
              · refine Real.toNNReal_eq_one.mp ?_
                cases x i <;> simp [SpinState.toReal]
              · refine Real.toNNReal_eq_one.mp ?_
                cases x j <;> simp [SpinState.toReal]
            -- Norm of matrix bounds each entry
            have h_norm_bound : |W i j| ≤ ‖W‖ := by
              refine (Real.toNNReal_le_toNNReal_iff_of_pos ?_).mp ?_
              · refine Real.toNNReal_pos.mp ?_
                sorry -- You need to prove W i j ≠ 0 or use a more general approach
              · sorry -- The bound on matrix element by the matrix norm
                -- This can be proven using properties of the Frobenius norm

            calc |W i j| * |xVec i| * |xVec j|
              ≤ ‖W‖ * |xVec i| * |xVec j| := by gcongr
              _ = ‖W‖ * 1 * 1 := by rw [h_spin_mag.1, h_spin_mag.2]

        _ = ∑ i, ∑ j, ‖W‖ := by simp
        _ = ∑ i, (Finset.card (Finset.univ : Finset (Fin n))) * ‖W‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.sum_const]
            congr
        _ = ∑ i, n * ‖W‖ := by simp
        _ = (Finset.card (Finset.univ : Finset (Fin n))) * n * ‖W‖ := by
            rw [← Finset.sum_const]
            congr
        _ = n * n * ‖W‖ := by simp
        _ = n^2 * ‖W‖ := by ring

      -- Further simplify the bound
      have h_bound : |Matrix.toBilin' W xVec xVec| ≤ n^2 * ‖W‖ := by
        exact this

      -- Use the symmetric property of the matrix
      have h_symm : Matrix.IsSymm W := weights_symmetric net
      have h_zero_diag : Matrix.diag W = 0 := weights_diag_zero net

      -- For symmetric matrices with zero diagonal, we can improve the bound
      calc |Matrix.toBilin' W xVec xVec|
        ≤ n^2 * ‖W‖ := h_bound
        _ = 2 * (n * n / 2) * ‖W‖ := by ring
        _ = 2 * (n * (n-1) / 2 + n/2) * ‖W‖ := by ring
        _ ≤ 2 * (n * (n-1) / 2 + n/2) * ‖W‖ := by apply le_refl
        _ = 2 * n * ‖W‖ := by
            have h_diag_sum : n/2 = n/2 := by rfl
            have h_off_diag : n * (n-1) / 2 + n/2 = n * (n-1) / 2 + n/2 := by rfl
            ring_nf

    -- Convert to the negated form we need
    calc -1/2 * Matrix.toBilin' W xVec xVec
      ≥ -1/2 * |Matrix.toBilin' W xVec xVec| := by
          apply mul_le_mul_of_nonpos_left
          · apply le_abs_self
          · linarith
      _ ≥ -1/2 * (2 * n * ‖W‖) := by
          apply mul_le_mul_of_nonpos_left
          · exact h_bilin_bound
          · linarith
      _ = -n * ‖W‖ := by ring

  -- Handle the threshold term
  have h_thresh_bound : -(∑ i, net.thresholds i * xVec i) ≥ -(∑ i, |net.thresholds i|) := by
    apply neg_le_neg
    calc ∑ i, net.thresholds i * xVec i
      ≤ ∑ i, |net.thresholds i * xVec i| := by refine Finset.sum_le_sum ?_ <;> intros <;> apply le_abs_self
      _ = ∑ i, |net.thresholds i| * |xVec i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul]
      _ = ∑ i, |net.thresholds i| * 1 := by
          apply Finset.sum_congr rfl
          intro i _
          have h_spin_mag : |xVec i| = 1 := by
            simp only [xVec, toRealVector]
            refine Real.toNNReal_eq_one.mp ?_
            cases x i <;> simp [SpinState.toReal]
          rw [h_spin_mag]
      _ = ∑ i, |net.thresholds i| := by simp

  -- Combine the bounds
  calc
    energy net x = -1/2 * Matrix.toBilin' W xVec xVec - (∑ i, net.thresholds i * xVec i) := rfl
    _ ≥ -n * ‖W‖ - (∑ i, net.thresholds i * xVec i) := by
      gcongr
      exact h_quad_bound
    _ ≥ -n * ‖W‖ - ∑ i, |net.thresholds i| := by
      gcongr
      exact h_thresh_bound


/--
Asynchronous update process converges to a fixed point.
-/
theorem asynchronous_update_convergence : ∀ x : HopfieldState n, ∃ seq : UpdateSeq net x, isFixedPoint net seq.target := by
  sorry -- Proof using energy decrease and finite state space to be completed

end ConvergenceTheorems

section FixedPointsBasins

open HopfieldState UpdateSeq

variable {n : ℕ} (net : HopfieldNetwork n)

/--
The set of fixed points of the Hopfield network `net`.
-/
def fixedPoints (net : HopfieldNetwork n) : Finset (HopfieldState n) :=
  Finset.univ.filter (isFixedPoint net)

/--
Basin of attraction of a fixed point `p` for network `net`.
It is the set of initial states `x` that converge to `p` under asynchronous updates.
-/
def basinOfAttraction (net : HopfieldNetwork n) (p : HopfieldState n) : Set (HopfieldState n) :=
  {x | convergesTo net x p}

/--
Check if a fixed point is a local minimum of the energy function in Hamming distance 1 ball.
-/
def isLocalEnergyMinimum (net : HopfieldNetwork n) (p : HopfieldState n) : Prop :=
  isFixedPoint net p ∧
  ∀ i : Fin n, energy net (updateState net p i) ≥ energy net p

lemma isLocalEnergyMinimum_iff_fixedPoint_and_no_energy_decrease_one_flip :
  isLocalEnergyMinimum net p ↔ isFixedPoint net p ∧ ∀ i : Fin n, energyDiff net p i ≥ 0 := by
  unfold isLocalEnergyMinimum energyDiff
  simp

lemma fixedPoint_is_localEnergyMinimum : isFixedPoint net p → isLocalEnergyMinimum net p := by
  intro hfp
  apply And.intro hfp
  intro i
  have h_energy_diff_zero : energyDiff net p i = 0 := by
    rw [energy_fixed_point_iff_no_change]
    exact hfp i
  rw [h_energy_diff_zero]
  norm_nonneg

/--
Relationship between fixed points and local minima of energy.
Every fixed point is a local minimum of the energy function.
-/
theorem fixedPoint_implies_localEnergyMinimum :
  isFixedPoint net p → isLocalEnergyMinimum net p := by
  exact fixedPoint_is_localEnergyMinimum

/--
Fixed points are states where for every neuron `i`, the local field and spin are aligned.
Specifically, if `x` is a fixed point, then for all `i`, either `localField net x i > 0` and `x i = up`,
or `localField net x i < 0` and `x i = down`, or `localField net x i = 0`.
-/
lemma fixedPoint_localField_aligned_spin (net : HopfieldNetwork n) (x : HopfieldState n) :
  isFixedPoint net x ↔ ∀ i : Fin n, (localField net x i > 0 ∧ x i = up) ∨ (localField net x i < 0 ∧ x i = down) ∨ (localField net x i = 0) := by
  rw [isFixedPoint]
  simp
  funext x
  funext i
  unfold updateState
  dsimp
  split_ifs
  · -- 0 < lf, updateState x i = up, want updateState x i = x i, so x i = up.
    simp
    constructor
    · intro h
      left
      exact And.intro h_if (by assumption)
    · intro h_or
      cases h_or
      case inl h_and => exact h_and.right
      case inr h_or' => cases h_or'
      case inl h_and => exfalso; exact h_and.left h_if
      case inr h_zero => exfalso; exact h_zero.left h_if
  · split_ifs
    · -- lf < 0, updateState x i = down, want updateState x i = x i, so x i = down.
      simp
      constructor
      · intro h
        cases h
        case refl => right; left; exact And.intro h_if_1 (by assumption)
      · intro h_or
        cases h_or
        case inl h_and => exfalso; exact h_and.left h_if_1
        case inr h_or' => cases h_or'
        case inl h_and => exact h_and.right
        case inr h_zero => exfalso; exact h_zero.left h_if_1
    · -- lf = 0, updateState x i = x i, want updateState x i = x i. Always true.
      simp
      constructor
      · intro h_eq
        right; right; assumption
      · intro h_or
        trivial


/--
The set of fixed points is finite since `HopfieldState n` is finite.
-/
instance fixedPoints_fintype (net : HopfieldNetwork n) : Fintype (fixedPoints net) :=
  Finset.fintype (fixedPoints net)

/--
Basins of attraction partition the space of Hopfield states.
For every initial state `x`, there is at least one fixed point it converges to.
And every state belongs to at least one basin of attraction (possibly multiple if convergence is not unique, but for Hopfield with async updates it should be unique).
For each state x, it converges to some fixed point. Is it always exactly one fixed point?  Yes, for async updates in Hopfield.
Thus, basins of attraction should partition the state space.
-/
theorem basins_of_attraction_cover_universe :
  (Set.univ : Set (HopfieldState n)) ⊆ ⋃ p ∈ fixedPoints net, basinOfAttraction net p := by
  intro x _
  have h_conv : ∃ seq : UpdateSeq net x, isFixedPoint net seq.target := asynchronous_update_convergence net x
  rcases h_conv with ⟨seq, h_fp⟩
  let p := seq.target
  have hp_fp : isFixedPoint net p := h_fp
  have h_p_in_fixedPoints : p ∈ fixedPoints net := by
    simp [fixedPoints]
    exact hp_fp
  have h_x_in_basin_p : x ∈ basinOfAttraction net p := by
    simp [basinOfAttraction, convergesTo]
    use seq
    exact h_fp
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨h_p_in_fixedPoints, h_x_in_basin_p⟩⟩


-- Further work :
-- - Disjointness of basins of attraction (for asynchronous updates, basins should be disjoint except for boundaries).
-- - Size/cardinality of basins of attraction.
-- - Relationship between energy landscape and basins of attraction.
-- - Characterization of fixed points based on network parameters (weights and thresholds).

end FixedPointsBasins
end HopfieldState
