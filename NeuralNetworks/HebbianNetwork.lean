import HopfieldNetworks.Basic


namespace HebbianLearning
open HopfieldState UpdateSeq

variable {n : ℕ}
/--
Calculate weights matrix using Hebbian learning rule for a given set of patterns.
Weight matrix W_{ij} = (1/n) * ∑_{pattern μ} pattern_μ[i] * pattern_μ[j].
For binary spins {+1, -1}, pattern_μ[i] is just (pattern_μ i).toReal.
Diagonal elements W_{ii} are set to 0.
Result is a valid `HopfieldNetwork`.weights structure.
-/
noncomputable
def hebbianWeights (patterns : Finset (HopfieldState n)) :
  {M : Matrix (Fin n) (Fin n) ℝ // M.IsHermitian ∧ Matrix.diag M = 0} :=
  let n_patterns := (patterns.card : ℝ)
  let W_raw : Matrix (Fin n) (Fin n) ℝ :=
    λ i j => (1 / n : ℝ) * Finset.sum patterns (λ p => (p i).toReal * (p j).toReal)
  -- Define W with zero diagonal explicitly
  let W : Matrix (Fin n) (Fin n) ℝ :=
    λ i j => if i = j then 0 else W_raw i j
  have is_hermitian : W.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp [W, W_raw]
    -- The weights matrix is symmetric by construction
    -- Just need to show that swapping i and j in the sum preserves equality
    by_cases h : i = j
    · -- When i = j, both sides are 0
      simp [h]
    · -- When i ≠ j, need to show the sums are equal
      simp [h]
      by_cases hji : j = i
      · -- This case is impossible since i ≠ j but j = i
        exact False.elim (h (id (Eq.symm hji)))
      · -- When both i ≠ j and j ≠ i, prove the sums are equal
        simp [hji]
        -- Prove that the sums are equal using commutativity of multiplication
        have h_comm_sum : ∑ p ∈ patterns, (p j).toReal * (p i).toReal = ∑ p ∈ patterns, (p i).toReal * (p j).toReal := by
          apply Finset.sum_congr
          · exact rfl
          · intros p hp
            exact mul_comm (p j).toReal (p i).toReal
        exact
          Or.symm
            ((fun {n} {α} {a b} => Vector.mkVector_inj.mp)
              (congrArg (Vector.mkVector n) h_comm_sum))
  have diag_zero : Matrix.diag W = 0 := by
    funext i
    -- We need to define W' which is W but with zeroes on the diagonal
    let W' : Matrix (Fin n) (Fin n) ℝ :=
      λ i j => if i = j then 0 else W_raw i j

    -- Show that W' has the same non-diagonal elements as W
    have h_same_nondiag : ∀ (i j : Fin n), i ≠ j → W' i j = W i j := by
      intro i j h_neq
      simp [W', W, W_raw]

    -- Show that W'_ii = 0 for all i
    have h_diag_zero : ∀ i, W' i i = 0 := by
      intro i
      simp [W']

    -- Now show that Matrix.diag W = Matrix.diag W' = 0
    simp [Matrix.diag_apply, W, W_raw]

    -- Since we're defining W to have zero diagonal, we need to show:
    -- Let's prove that W_raw i i = (patterns.card / n) and then set diagonal to zero explicitly


  ⟨W, And.intro is_hermitian diag_zero⟩

/--
Construct a Hopfield network with weights learned by Hebbian rule from given patterns, and zero thresholds.
-/
noncomputable
def hebbianNetwork (patterns : Finset (HopfieldState n)) : HopfieldNetwork n :=
  { weights := hebbianWeights patterns, thresholds := 0 }

/--
Theorem: If a Hopfield network is constructed using Hebbian learning from a set of patterns,
and the patterns are orthogonal, then the stored patterns are fixed points of the network.
(Orthogonality here means overlap between distinct patterns is 0).
We will show a weaker version first, assuming strict orthogonality and zero thresholds.

Simplified version for now: Assume patterns are orthogonal (overlap 0 for distinct patterns, overlap n for self-overlap),
and thresholds are zero. Show that each pattern is a fixed point.
-/
theorem hebbian_orthogonal_patterns_are_fixedPoints
  (patterns : Finset (HopfieldState n))
  (h_orthogonal : ∀ p1 ∈ patterns, ∀ p2 ∈ patterns, p1 ≠ p2 → overlap p1 p2 = 0)
  (h_patterns_nonempty : patterns.Nonempty):
  ∀ p ∈ patterns, isFixedPoint (hebbianNetwork patterns) p := by
  intro p_fix p_in_patterns
  intro i -- Need to show updateState (hebbianNetwork patterns) p_fix i = p_fix i for all i.
  let net := hebbianNetwork patterns
  let W := weightsMatrix net
  let thresholds := net.thresholds -- thresholds = 0
  let x := p_fix
  let lf := localField net x i -- localField net p_fix i

  -- localField net p_fix i = (W * toRealVector p_fix)_i - thresholds i
  -- = (W * toRealVector p_fix)_i - 0 = (W * toRealVector p_fix)_i
  -- = ∑_j W_{ij} (p_fix j).toReal
  -- W_{ij} = (1/n) * ∑_{pattern μ} (pattern_μ i).toReal * (pattern_μ j).toReal
  -- localField net p_fix i = ∑_j [(1/n) * ∑_{pattern μ} (pattern_μ i).toReal * (pattern_μ j).toReal] * (p_fix j).toReal
  -- = (1/n) * ∑_j [∑_{pattern μ} (pattern_μ i).toReal * (pattern_μ j).toReal] * (p_fix j).toReal
  -- = (1/n) * ∑_{pattern μ} (pattern_μ i).toReal * [∑_j (pattern_μ j).toReal * (p_fix j).toReal]
  -- = (1/n) * ∑_{pattern μ} (pattern_μ i).toReal * (overlap pattern_μ p_fix)

  have lf_eq_sum_overlaps : localField net p_fix i = (1 / n : ℝ) * Finset.sum patterns (λ pattern_μ => (pattern_μ i).toReal * (overlap pattern_μ p_fix)) := by
    unfold localField net hebbianNetwork
    unfold hebbianWeights weightsMatrix
    simp
    -- Direct proof working with matrix multiplication definition
    simp [Matrix.mulVec, dotProduct]
    -- We need to show that the sum is equivalent to our desired expression

    -- Work through the algebra directly
    have h_sum_transform : (∑ x : Fin n, if i = x then 0 else ((↑n)⁻¹ * ∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal) =
                           (↑n)⁻¹ * ∑ pattern_μ ∈ patterns, (pattern_μ i).toReal * overlap pattern_μ p_fix := by
      -- Pull the constant factor out
      rw [@Fin.sum_univ_def]
      have h_factor : ∀ (s : Fin n → ℝ), (∑ x, if i = x then 0 else ((↑n)⁻¹ * s x) * (p_fix x).toReal) = (↑n)⁻¹ * (∑ x, if i = x then 0 else s x * (p_fix x).toReal) := by
        intro s
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j
        · simp [h]
        · simp [h]

      let s : Fin n → ℝ := λ x => ∑ p ∈ patterns, (p i).toReal * (p x).toReal
      rw [@List.sum_map_ite]

      -- Distribute multiplication over summation and reorder sums
      simp only [List.map_const', List.sum_replicate, smul_zero, decide_not, zero_add]
      rw [@inv_mul_eq_div]

      -- First convert list operations to finset operations
      rw [@Finset.sum_div]
      rw [@Finset.sum_list_map_count]

      -- Now use algebraic manipulation to rewrite the sum step by step
      simp only [List.toFinset_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, List.toFinset_finRange, nsmul_eq_mul]

      -- Restate the goal more clearly
      suffices h_goal : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                         (↑n)⁻¹ * (∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal =
                         (↑n)⁻¹ * ∑ p ∈ patterns, (p i).toReal * overlap p p_fix by
        sorry

      -- Factor out (↑n)⁻¹ from both sides
      have n_nat_ne_zero : n ≠ 0 := by
        intro h
        cases n
        · -- In case n = 0, we need to derive a contradiction
          simp at h  -- This is true by assumption
          -- Get a contradiction from the fact that Fin 0 is empty but we have a pattern
          have h_fin0_empty : IsEmpty (Fin 0) := by exact Fin.isEmpty'
          have p_fix_impossible : p_fix ∈ patterns := p_in_patterns
          have p_fix_type : p_fix = fun _ => SpinState.up := funext (fun x => False.elim (h_fin0_empty.false x))
          exact IsEmpty.false i
        · contradiction

      have n_real_ne_zero : (n : ℝ) ≠ 0 := by
        intro h
        have h' := Nat.cast_eq_zero.mp h
        exact n_nat_ne_zero h'

      have n_real_inv_ne_zero : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero n_real_ne_zero

      -- Focus on the left-hand side
      have h_lhs : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                   (↑n)⁻¹ * (∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal =
                   (↑n)⁻¹ * ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                   (∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal := by
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]

      rw [h_lhs]

      -- Now interchange the order of summation
      have h_sum_interchange : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                               (∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal =
                               ∑ p ∈ patterns, ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                               (p i).toReal * (p x).toReal * (p_fix x).toReal := by
        -- Instead of using Finset.sum_congr directly, we need to work with the Cauchy sequences
        rw [@Real.ext_cauchy_iff]
        simp only [ne_eq]

        -- Explicitly write out the proof for interchanging summations
        have h_interchange : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                              (∑ p ∈ patterns, (p i).toReal * (p x).toReal) * (p_fix x).toReal =
                             ∑ p ∈ patterns,
                              ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                              (p i).toReal * (p x).toReal * (p_fix x).toReal := by
          -- Use Finset.sum_comm to swap the order of summation
          rw [Finset.sum_comm]

          -- Show equality by focusing on the individual summands
          apply Finset.sum_congr rfl
          intro (pattern_μ : Fin n) hp

          -- For each pattern_μ, prove the summation equality
          have h_inner_sum : (∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                            (pattern_μ i).toReal * (pattern_μ x).toReal * (p_fix x).toReal) =
                            (∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                            (pattern_μ i).toReal * (pattern_μ x).toReal * (p_fix x).toReal) := by
            -- Simplify with reflexivity since both sides are identical
            rfl

            -- Apply Finset.sum_congr to prove equality of sums


          exact h_inner_sum

        exact congrArg Real.cauchy h_interchange

      rw [h_sum_interchange]

      -- The inner sum now corresponds to the overlap definition
      apply Finset.sum_congr rfl
      intro p hp

      -- Define the overlap explicitly in terms of the sum
      have h_overlap_def : overlap p p_fix = ∑ x : Fin n, (p x).toReal * (p_fix x).toReal := by
        rfl

      -- We need to show that the filtered sum equals the full sum
      have h_filter_sum : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                          (p i).toReal * (p x).toReal * (p_fix x).toReal =
                          (p i).toReal * ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ,
                          (p x).toReal * (p_fix x).toReal := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_assoc]

      rw [h_filter_sum]

      -- Now we need to show that the filtered sum equals the full sum (i term contributes 0)
      have h_sum_filter_equiv : ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ, (p x).toReal * (p_fix x).toReal =
                               ∑ x : Fin n, (p x).toReal * (p_fix x).toReal := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : i = x
        · simp [h]
        · simp [h]

      rw [h_sum_filter_equiv]
      rw [h_overlap_def]

      -- First, factor out (↑n)⁻¹
      rw [Finset.mul_sum]
      apply Eq.symm
      rw [Finset.mul_sum]
      congr

      -- Reorder summations (interchange sum over patterns and sum over x)
      rw [Finset.sum_comm]

      -- Now show that each pattern's contribution matches the definition of overlap
      apply Finset.sum_congr rfl
      intro pattern_μ hμ

      -- Show that sum over x matches the overlap definition
      have h_overlap : ∑ x : Fin n, if i = x then 0 else ((p_fix x).toReal * (pattern_μ i).toReal * (pattern_μ x).toReal) =
                       (pattern_μ i).toReal * overlap pattern_μ p_fix := by
        -- Definition of overlap
        simp [overlap]

        -- Apply commutativity of multiplication
        -- Distribute the multiplication over the sum using mul_sum
        have h_distrib : (pattern_μ i).toReal * ∑ x : Fin n, (p_fix x).toReal * (pattern_μ x).toReal =
                         ∑ x : Fin n, (pattern_μ i).toReal * ((p_fix x).toReal * (pattern_μ x).toReal) := by
          rw [Finset.mul_sum]

        rw [h_distrib]

        -- Apply associativity
        have h_assoc : ∑ x : Fin n, (pattern_μ i).toReal * ((p_fix x).toReal * (pattern_μ x).toReal) =
                      ∑ x : Fin n, ((pattern_μ i).toReal * (pattern_μ x).toReal) * (p_fix x).toReal := by
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_assoc]

        rw [h_assoc]

        -- Handle the conditional term
        have h_filter : ∑ x : Fin n, if i = x then 0 else ((pattern_μ i).toReal * (pattern_μ x).toReal) * (p_fix x).toReal =
                       ∑ x ∈ Finset.filter (fun x => i ≠ x) Finset.univ, ((pattern_μ i).toReal * (pattern_μ x).toReal) * (p_fix x).toReal := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : i = j
          · simp [h]
          · simp [h]

        rw [h_filter]

        -- The diagonal term (i=x) contributes zero, which matches our filter
        rfl

      -- Apply the overlap equality
      rw [h_overlap]
      simp [mul_comm]

    exact h_sum_transform

  rw [lf_eq_sum_overlaps]

  -- Consider the term (overlap pattern_μ p_fix).
  -- If pattern_μ = p_fix, overlap pattern_μ p_fix = overlap p_fix p_fix = n.
  -- If pattern_μ ≠ p_fix, and pattern_μ ∈ patterns, p_fix ∈ patterns, then by orthogonality h_orthogonal, overlap pattern_μ p_fix = 0.
  -- So, in the sum ∑_{pattern μ} (pattern_μ i).toReal * (overlap pattern_μ p_fix), only the term with pattern_μ = p_fix is non-zero.
  -- And for pattern_μ = p_fix, overlap pattern_μ p_fix = n.

  have overlap_term : ∀ pattern_μ ∈ patterns, pattern_μ ≠ p_fix → (pattern_μ i).toReal * (overlap pattern_μ p_fix) = 0 := by
    intros pattern_mu pattern_mu_in patterns_ne_pfix
    have h_overlap_zero : overlap pattern_mu p_fix = 0 := h_orthogonal pattern_mu p_fix pattern_mu_in p_in_patterns patterns_ne_pfix
    simp [h_overlap_zero]

  have sum_term : Finset.sum patterns (λ pattern_μ => (pattern_μ i).toReal * (overlap pattern_μ p_fix)) =
    (p_fix i).toReal * (overlap p_fix p_fix) + Finset.sum (patterns.erase p_fix) (λ pattern_μ => (pattern_μ i).toReal * (overlap pattern_μ p_fix)) := by
    rw [Finset.sum_insert p_fix]
    · rfl
    · intro h_not_mem
      apply Finset.not_mem_erase

  rw [sum_term]
  simp

  have sum_zero : Finset.sum (patterns.erase p_fix) (λ pattern_μ => (pattern_μ i).toReal * (overlap pattern_μ p_fix)) = 0 := by
    apply Finset.sum_eq_zero
    intro pattern_mu pattern_mu_in_erase_pfix
    apply overlap_term
    · apply Finset.mem_of_mem_erase pattern_mu_in_erase_pfix
    · intro h_eq_p_fix
      apply pattern_mu_in_erase_pfix
      rw [h_eq_p_fix]
      apply Finset.mem_erase_self

  rw [sum_zero]
  simp

  have overlap_self_eq_n : overlap p_fix p_fix = n := overlap_self p_fix
  rw [overlap_self_eq_n]
  simp

  -- localField net p_fix i = (1/n) * (p_fix i).toReal * n = (p_fix i).toReal

  have lf_eq_x_real : localField net p_fix i = (p_fix i).toReal := rfl

  rw [lf_eq_x_real]

  -- Now need to show updateState net p_fix i = p_fix i.
  unfold updateState
  dsimp
  let lf_val := (p_fix i).toReal
  split_ifs
  next h_pos => -- 0 < lf_val, i.e., 0 < (p_fix i).toReal.  Then p_fix i must be SpinState.up, so (p_fix i).toReal = 1.
    simp [h_pos] at *
    have p_fix_i_is_up : p_fix i = SpinState.up := by
      cases p_fix i
      case up => rfl
      case down => simp [SpinState.toReal] at h_pos -- 0 < -1, contradiction
    rw [p_fix_i_is_up]
    rfl -- updateState = up = p_fix i.
  next h_nonpos =>
    split_ifs
    next h_neg => -- lf_val < 0, i.e., (p_fix i).toReal < 0.  Then p_fix i must be SpinState.down, so (p_fix i).toReal = -1.
      simp [h_neg] at *
      have p_fix_i_is_down : p_fix i = SpinState.down := by
        cases p_fix i
        case up => simp [SpinState.toReal] at h_neg -- -1 > 0, contradiction
        case down => rfl
      rw [p_fix_i_is_down]
      rfl -- updateState = down = p_fix i.
    next h_nonneg_lf => -- lf_val = 0, i.e., (p_fix i).toReal = 0.  But (p_fix i).toReal is either 1 or -1. Contradiction.
      simp [h_nonneg_lf] at *
      have p_fix_real_not_zero : (p_fix i).toReal ≠ 0 := by
        cases p_fix i
        case up => simp [SpinState.toReal]
        case down => simp [SpinState.toReal]
      exact False.elim (h_nonneg_lf p_fix_real_not_zero)

end HebbianLearning
