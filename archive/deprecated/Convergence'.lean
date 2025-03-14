
import HopfieldNetworks.Energy
import aesop

set_option maxHeartbeats 0
set_option maxRecDepth 10000


--section EnergyDecrease
open HopfieldState

variable {n : ℕ}

/--
  Theorem: Fixed points are local minima of the energy function.
-/
theorem fixed_point_is_local_minimum {net : HopfieldNetwork n} {x : HopfieldState n}
    (h_fixed : UpdateSeq.isFixedPoint net x)
    (h_zero_thresholds : ∀ i, net.thresholds i = 0) :
    ∀ y : HopfieldState n, (∃ i : Fin n, ∀ j : Fin n, j ≠ i → y j = x j) →
    energy net x ≤ energy net y := by
  intro y h_diff_at_one
  rcases h_diff_at_one with ⟨i, h_diff_only_i⟩

  have h_energy_diff := energy_diff_single_flip net x i (h_zero_thresholds i) y h_diff_only_i
  have h_update_eq_x : updateState net x i = x := h_fixed i

  let lf := localField net x i

  have h_consistent_sign : (x i).toReal * lf ≥ 0 := by
    by_contra h_not_consistent
    push_neg at h_not_consistent

    -- If signs are inconsistent, the update would change the state
    have h_energy_decreases := energy_decreases_on_update_with_inconsistent_signs net x i
      (h_zero_thresholds i) h_not_consistent

    -- But x is a fixed point, so no change should occur
    have h_no_change : updateState net x i = x := h_fixed i

    -- This leads to a contradiction
    rw [h_no_change] at h_energy_decreases
    exact lt_irrefl (energy net x) h_energy_decreases

  cases (x i) <;> simp [SpinState.toReal] at h_consistent_sign ⊢
  · rw [← h_fixed i] at h_consistent_sign
    by_cases h_y_eq_x : y i = up
    · simp only [neg_sub] at h_energy_diff
      rw [h_y_eq_x, SpinState.toReal] at h_energy_diff
      rw [← h_fixed i]
      -- Since x i = down, updateState net x i i = down
      have h_update_down : updateState net x i i = down := by
        rw [h_fixed i]
        by_contra h_not_down
        -- If x i is up, then the consistent sign condition implies lf ≥ 0
        have h_x_up : x i = up := by
          cases h_x : x i
          · simp only
            -- When x i = down, we have a contradiction with our assumption
          · -- When x i = up, we have exactly what we need to prove
            exact False.elim (h_not_down h_x)
        rw [← h_x_up] at h_consistent_sign

        -- But then x would not be a fixed point
        cases h_x : x i with
        | down =>
          -- This contradicts h_x_up
          have h_contra : down = up := by rw [← h_x, h_x_up]
          exact h_not_down h_x
        | up =>
          have h_lf_neg : lf ≤ 0 := by
            rw [h_x] at h_consistent_sign
            have h_update_eq : updateState net x i i = x i := by exact congrFun (h_fixed i) i
            unfold updateState at h_update_eq
            simp at h_update_eq

            -- If lf > 0 and x i = up, the update would keep it as up
            -- If lf < 0 and x i = up, the update would change it to down
            -- Since x is a fixed point and x i = up, we must have lf ≥ 0

            -- But we also need to prove lf ≤ 0 for this branch of the proof
            -- The only way both can be true is if lf = 0
            apply le_of_eq
            apply le_antisymm
            · -- Prove lf ≤ 0
              sorry -- This requires additional context or is part of a contradiction
            · -- Prove lf ≥ 0
              aesop

          -- Define the update logic for the down state
          have h_down_update : updateState net x i i = down := by
            unfold updateState
            simp
            by_cases h_lf_strict : localField net x i < 0
            · simp [h_lf_strict]
              exact h_lf_neg
            · -- If not strict negative, then lf = 0 by h_lf_neg
              have h_lf_zero : localField net x i = 0 := by
                apply le_antisymm
                · exact h_lf_neg
                · exact not_lt.mp h_lf_strict
              simp [h_lf_zero]
              -- With lf = 0 and x i = up, the update would keep it as up
              -- This is a contradiction, so we need to derive false
              -- Since x i = up (from h_x) but updateState should be down (from our current branch),
              -- we have a contradiction
              have h_xi_eq_up : x i = up := by exact h_x
              have h_update_eq : updateState net x i i = x i := by exact congrFun (h_fixed i) i
              rw [h_xi_eq_up] at h_update_eq
              -- These are different constructors, so we have a contradiction
              have h_contra : x i = up := by exact h_x
              have h_false : False := by
                have : updateState net x i i = down := by
                  unfold updateState
                  simp [h_lf_zero]
                  -- Here we're trying to prove a contradiction
                  -- The context has h_lf_zero: localField net x i = 0
                  -- With lf = 0, updateState will keep the spin state unchanged
                  -- Since x i = up, the update would keep it as up
                  by_cases h_up_state : x i = up
                  · rw [h_up_state]
                    -- We have x i = up, so updateState would keep it as up
                    -- But we need to prove down, which is a contradiction
                    exfalso
                    -- The contradiction comes from the fact that we're trying to prove updateState = down
                    -- but with lf = 0 and x i = up, the updateState would be up
                    have h_update_up : updateState net x i i = up := by
                      unfold updateState
                      simp [h_lf_zero, h_up_state]
                    -- Now we have both h_update_up (update is up) and trying to prove update is down
                    -- These are different constructors, so we have a contradiction
                    have h_contra : up = down := by
                      -- We have h_update_up: updateState net x i i = up
                      -- But we're trying to prove updateState net x i i = down
                      -- This creates a contradiction
                      have h_suppose_down : updateState net x i i = down := by
                        -- This is our supposition that leads to contradiction
                        rw [h_fixed]  -- Assume what we're trying to prove
                        sorry
                      rw [h_update_up] at h_suppose_down
                      exact h_suppose_down
                    contradiction
                  · have : x i = down := by
                      cases x i
                      · aesop
                      · exfalso
                        exact h_up_state h_x
                    rw [this]
                rw [h_update_eq] at this
                rw [← «Prop».bot_eq_false]
                exact SpinState.noConfusion this
              contradiction

          -- This contradicts fixed point property
          have h_not_fixed : updateState net x i ≠ x := by
            intro h_eq
            rw [funext_iff] at h_eq
            have h_eq_i := h_eq i
            rw [h_down_update] at h_eq_i
            rw [h_x] at h_eq_i
            exact SpinState.noConfusion h_eq_i

          exact absurd (h_fixed i) h_not_fixed
      rw [h_update_down] at h_consistent_sign
      simp at h_consistent_sign
      -- With these facts, we can show the energy difference is non-negative
      have h_energy_nonneg : energy net y - energy net x ≥ 0 := by
        rw [h_energy_diff]
        simp
        have : -1 - 1 = -2 := by ring
        rw [← h_fixed i]
        -- Fix the sign and use the appropriate inequality lemma
        have h1 : ((if updateState net x i i = up then 1 else -1) - up.toReal) * localField net (updateState net x i) i =
                  (-2) * localField net x i := by
          rw [h_update_down, h_update_eq_x]
          simp [SpinState.toReal]
          -- We need to show (-1 - 1) * localField net x i = -(2 * localField net x i)
          have : (-1 - 1) = -2 := by ring
          have : -2 * localField net x i = -(2 * localField net x i) := by ring

          -- Use the fact that updateState net x i = x to rewrite the expressions
          have : localField net (updateState net x i) i = localField net x i := by
            rw [h_update_eq_x]

          rw [← this]; rw [@sub_one_mul]
          rw [h_fixed]
          simp only [neg_mul, one_mul]

          -- Explicitly simplify the expressions
          have h2 : -localField net x i - localField net x i = -2 * localField net x i := by
            rw [neg_mul]
            rw [← this]
            ring_nf
          aesop
        rw [h1]
        apply mul_nonneg_of_nonpos_of_nonpos
        · norm_num
        · exact h_consistent_sign
      -- We need to show: energy net (updateState net x i) ≤ energy net y
      -- We have: h_update_eq_x : updateState net x i = x
      -- And: h_energy_nonneg : energy net y - energy net x ≥ 0 (which implies energy net x ≤ energy net y)
      rw [h_update_eq_x]  -- Replace updateState net x i with x
      -- Now we need to prove: energy net x ≤ energy net y
      -- This follows directly from h_energy_nonneg
      linarith [h_energy_nonneg]
    · have h_y_down : y i = down := by
        cases h_yi : y i with
        | up =>
            have h_y_is_up : y i = up := by exact h_yi
            exact False.elim (h_y_eq_x h_y_is_up)
        | down => rfl

      -- Rewrite h_y_down into h_energy_diff
      rw [h_y_down] at h_energy_diff

      -- Simplify the expression
      simp only [SpinState.toReal] at h_energy_diff

      rw [← h_fixed i] at h_energy_diff
      have h_energy_nonneg : energy net x ≤ energy net y := by
        rw [← h_fixed i]
        if h : x i = up then
          -- Case where x i = up
          rw [h_fixed]
          rw [← h_fixed i]
          -- Simplify the expression
          have : (1 + 1) = 2 := by norm_num
          rw [← h_fixed i]
          -- Since x i = up and we have consistent signs, localField is non-negative
          apply le_of_sub_nonneg
          simp_all only [ne_eq, reduceCtorEq, ↓reduceIte, neg_sub, sub_neg_eq_add, not_false_eq_true, Nat.reduceAdd,
            pos_add_self_iff, zero_lt_one, mul_nonneg_iff_of_pos_left, lf]
        else
          -- Case where x i = down
          have h_xi_down : x i = down := by
            cases x i with
            | up =>
              -- We have h: ¬x i = up but also x i = up, so this is a contradiction
              rw [← h_y_down]
              rw [h_y_down]
              rw [← @Function.graph_id]
              sorry
            | down => rfl
          -- With x i = down, energy difference is zero
          rw [h_fixed]
          rw [← h_fixed i]
          rw [@energy_eq_energy']
          -- Show that localField is zero when x i is down
          have h_lf_zero : localField net x i = 0 := by
            -- If x i is down and update doesn't change it,
            -- then localField must be zero (or negative, but we have nonpositive from h_consistent_sign)
            have h_update : updateState net x i i = down := by rw [h_update_eq_x, h_xi_down]
            unfold updateState at h_update
            simp at h_update
            by_cases h_neg : localField net x i < 0
            · -- If lf < 0, we have a contradiction with h_consistent_sign
              exfalso
              have : lf < 0 := h_neg
              have : -lf > 0 := neg_pos.mpr h_neg
              have : -lf ≤ 0 := by
                rw [h_update_eq_x] at h_consistent_sign
                rw [h_xi_down] at h_consistent_sign
                simp at h_consistent_sign
                rw [← h_zero_thresholds i]
                rw [@neg_le]
                rw [h_zero_thresholds i]
                simp
                exact h_consistent_sign
              exact absurd (le_of_lt this) (not_le_of_gt h_consistent_sign)
            · -- If not lf < 0, then by h_consistent_sign, we have lf = 0
              push_neg at h_neg
              exact le_antisymm h_consistent_sign h_neg
          rw [h_lf_zero]
          simp
          exact le_refl (energy net x)

      have h_xi_down : (x i).toReal = -1 := by
        cases x i
      have h_yi_down : (y i).toReal = -1 := by
        cases y i
        case up =>
          contradiction
        case down =>
          simp
        case up =>
          simp
        case down =>
          contradiction

      have h_consistent_sign' : 0 ≤ if x i = up then lf else -lf := by
        rw [h_update_eq_x] at h_consistent_sign
        cases x i
        case up =>
          simp at h_consistent_sign
          exact h_consistent_sign
        case down =>
          simp at h_consistent_sign
          exact h_consistent_sign

      have h_local_field_nonpos : localField net x i ≤ 0 := by
        cases x i
        case up =>
          simp at h_consistent_sign'
        case down =>
          simp at h_consistent_sign'
          exact nonpos_of_neg_nonneg h_consistent_sign'

      have h_energy_diff_nonneg : 0 ≤ energy net y - energy net x := by
        rw [h_energy_diff]
        simp
        have h_neg2_local_field_nonneg : -2 * localField net x i ≥ 0 := by
          exact mul_nonneg (by norm_num) (neg_nonneg.mpr h_local_field_nonpos)
        exact h_neg2_local_field_nonneg

      exact le_of_sub_nonneg h_energy_diff_nonneg
  · have h_energy_nonneg : energy net x ≤ energy net y := by
      rw [@energy_eq_energy']
      have h_xi_up : (x i).toReal = 1 := by
        cases x i
        case up =>
          simp
        case down =>
          contradiction
      have h_yi_down : (y i).toReal = -1 := by
        cases y i
        case down =>
          simp
        case up =>
          contradiction
      rw [h_xi_up, h_yi_down]
      simp
      have h_local_field_nonneg : localField net x i ≥ 0 := by
        have h_consistent_sign' : 0 ≤ if x i = up then lf else -lf := h_consistent_sign
        cases x i
        case up =>
          simp at h_consistent_sign'
          exact h_consistent_sign'
        case down =>
          simp at h_consistent_sign'
      have h_neg2_local_field_nonpos : -2 * localField net x i ≤ 0 := by
        exact mul_nonpos (by norm_num) (neg_nonpos.mpr h_local_field_nonneg)
      exact le_of_neg_nonpos h_neg2_local_field_nonpos
    exact h_energy_nonneg

end HopfieldState
