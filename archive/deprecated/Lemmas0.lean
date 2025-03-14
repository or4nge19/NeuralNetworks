import HopfieldNetworks.Basic

open SpinState HopfieldState

variable {n : ℕ}

lemma isFixedPoint_iff_localField_sign (net : HopfieldNetwork n) (x : HopfieldState n) :
  isFixedPoint net x ↔ ∀ i,
    (0 < localField net x i → x i = SpinState.up) ∧
    (localField net x i < 0 → x i = SpinState.down) ∧
    (x i = SpinState.up → 0 ≤ localField net x i) ∧
    (x i = SpinState.down → localField net x i ≤ 0) := by
  constructor
  · -- Forward direction: isFixedPoint net x → ∀ i, ...
    intro h i
    unfold isFixedPoint at h
    specialize h i
    unfold updateState at h

    constructor
    · -- First part: 0 < localField net x i → x i = up
      intro h_pos
      have h_update : Function.update x i (if 0 < localField net x i then SpinState.up
                                         else if localField net x i < 0 then SpinState.down
                                         else x i) = x := h
      simp [h_pos] at h_update
      exact Eq.symm h_update

    · constructor
      · -- Second part: localField net x i < 0 → x i = down
        intro h_neg
        have h_update : Function.update x i (if 0 < localField net x i then SpinState.up
                                           else if localField net x i < 0 then SpinState.down
                                           else x i) = x := h
        simp [h_neg] at h_update
        have : x i = SpinState.down := Eq.symm h_update
        exact this

      · constructor
        · -- Third part: x i = up → 0 ≤ localField net x i
          intro h_up
          by_cases h_pos : 0 < localField net x i
          · -- Case 1: 0 < localField net x i
            exact le_of_lt h_pos
          · -- Case 2: ¬(0 < localField net x i)
            by_cases h_neg : localField net x i < 0
            · -- Case 2a: localField net x i < 0
              have h_update : Function.update x i (if 0 < localField net x i then SpinState.up
                                                 else if localField net x i < 0 then SpinState.down
                                                 else x i) = x := h
              simp [h_pos, h_neg] at h_update
              have : x i = SpinState.down := Eq.symm (Function.update_eq_iff.1 h_update)
              contradiction
            · -- Case 2b: ¬(localField net x i < 0)
              have h_zero : localField net x i = 0 := by
                apply le_antisymm
                · apply le_of_not_gt; exact h_pos
                · apply le_of_not_lt; exact h_neg
              exact le_of_eq h_zero

        · -- Fourth part: x i = down → localField net x i ≤ 0
          intro h_down
          by_cases h_neg : localField net x i < 0
          · -- Case 1: localField net x i < 0
            exact le_of_lt h_neg
          · -- Case 2: ¬(localField net x i < 0)
            by_cases h_pos : 0 < localField net x i
            · -- Case 2a: 0 < localField net x i
              have h_update : Function.update x i (if 0 < localField net x i then SpinState.up
                                                 else if localField net x i < 0 then SpinState.down
                                                 else x i) = x := h
              simp [h_pos] at h_update
              have : x i = SpinState.up := Eq.symm (Function.update_eq_iff.1 h_update)
              contradiction
            · -- Case 2b: ¬(0 < localField net x i)
              have h_zero : localField net x i = 0 := by
                apply le_antisymm
                · apply le_of_not_gt; exact h_pos
                · apply le_of_not_lt; exact h_neg
              exact le_of_eq h_zero

  · -- Backward direction: (∀ i, ...) → isFixedPoint net x
    intro h
    unfold isFixedPoint
    intro i
    unfold updateState

    -- Case analysis on the local field
    by_cases h_pos : 0 < localField net x i
    · -- If localField > 0
      -- We know x i = SpinState.up from our hypothesis h
      have h_xi_up : x i = SpinState.up := (h i).1 h_pos
      -- After update, i gets set to up
      simp [h_pos, h_xi_up]
      -- Need to show: Function.update x i SpinState.up = x
      -- Use Function.update_samef to show that if we update x at i with the same value it already has,
      -- then we get back x
      apply Function.update_self

    by_cases h_neg : localField net x i < 0
    · -- If localField < 0
      have h_xi_down : x i = SpinState.down := (h i).2.1 h_neg
      -- After update, i gets set to down
      simp [h_neg, h_xi_down]
      -- Need to show: Function.update x i SpinState.down = x
      apply Function.update_self

    -- If not positive and not negative, then localField = 0
    have h_zero : localField net x i = 0 := by
      apply le_antisymm
      · apply le_of_not_gt; exact h_pos
      · apply le_of_not_lt; exact h_neg

    -- If localField = 0, update doesn't change the state
    simp [h_pos, h_neg, h_zero]
    -- Need to show: Function.update x i (x i) = x
