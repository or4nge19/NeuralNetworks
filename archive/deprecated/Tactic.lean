import HopfieldNetworks.Basic

macro "analyze_field_sign" (net : term) (x : term) (i : term) : tactic => `(tactic|
  by_cases h_field_sign : (localField $net $x $i = 0)
  · rw [h_field_sign] at *
  · by_cases h_field_pos : (localField $net $x $i > 0)
    · have h_field_nonzero : (localField $net $x $i ≠ 0) := by linarith
    · have h_field_neg : (localField $net $x $i < 0) := by linarith
)

/-- Create a tactic that handles specific fixed point cases for different spin states. -/
macro "check_fixed_point" : tactic => `(tactic|
  have updateState_eq_self : updateState net x i = x := by
    funext j
    by_cases h : j = i
    . rw [h]
      simp [updateState, h_field_sign]
    . simp [updateState, h]
)
