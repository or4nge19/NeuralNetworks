import HopfieldNetworks.Basic
import HopfieldNetworks.Mathlib.Mathlib


open Matrix Matrix.toBilin BilinForm Matrix.toQuadraticMap'
open SpinState HopfieldState UpdateSeq


variable {n : ℕ}

/-! ## Lemmas for Convergence Analysis -/

/--
For a symmetric matrix `W`, we have `dotProduct (W.mulVec v) w = dotProduct (W.mulVec w) v`.
-/
lemma bilinear_symmetry' {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (h_sym : W.IsSymm) (v w : Fin n → ℝ) :
    dotProduct (W.mulVec v) w = dotProduct (W.mulVec w) v := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  -- Use symmetry of W
  have h_sym_at_ij : W j i = W i j := by
    unfold Matrix.IsSymm at h_sym
    exact congrFun (congrFun h_sym i) j
  rw [h_sym_at_ij]
  -- Rearrange using ring properties
  ring


/--
For real matrices, `IsHermitian` just means symmetric: `W = W.transpose`.
Hence we also get the bilinear symmetry property.
-/
lemma hermitian_implies_symmetric {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (h_herm : W.IsHermitian) : W.IsSymm := by
  -- Over ℝ, Hermitian is equivalent to symmetric
  exact h_herm

/--
Symmetry of the bilinear form induced by a Hermitian (real‐symmetric) matrix `W`.
-/
lemma bilinear_symmetry {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (h_sym : W.IsHermitian)
    (v w : Fin n → ℝ) :
    dotProduct (W.mulVec v) w = dotProduct (W.mulVec w) v := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  -- For real matrices, IsHermitian means the matrix equals its transpose
  have h : W i j = W j i := by
    -- Using the definition of IsHermitian
    have h_eq := h_sym
    -- For real matrices, h_sym means W = W.conjTranspose
    have h_transpose : W.conjTranspose j i = W i j := by
      -- This is the definition of conjTranspose for matrices
      exact rfl
    -- From IsHermitian we know W.conjTranspose = W
    have h_symm : W.conjTranspose = W := h_eq
    -- Combine these facts
    rw [← h_symm]
    exact congrFun (congrFun h_sym i) j
  rw [h]
  -- Rearrange the right-hand side using ring arithmetic
  have : W j i * v j * w i = W j i * w i * v j := by ring
  exact this


lemma weights_bilin_symm (W : Matrix (Fin n) (Fin n) ℝ)
    (h_sym : W.IsHermitian) (v w : Fin n → ℝ) :
    Matrix.toBilin' W v w = Matrix.toBilin' W w v := by
  -- Unfold the definition of toBilin' and use the bilinear_symmetry lemma
  simp only [Matrix.toBilin']
  -- Now we need to relate LinearMap.BilinForm.toMatrix' to dotProduct and mulVec
  unfold LinearMap.BilinForm.toMatrix'
  -- The types don't match exactly, so we need to convert explicitly
  have h := bilinear_symmetry W h_sym v w
  -- Convert the types from dotProduct notation to LinearMap notation
  simp only [dotProduct, mulVec] at h
  -- Need to rewrite to match the goal type exactly
  -- The goal is about LinearMap.toMatrix₂', but h is about sums
  rw [← dotProduct_eq_apply_symm_toMatrix₂' v w]
  rw [← dotProduct_eq_apply_symm_toMatrix₂' w v]
  exact h

/--
Polarization identity for a symmetric bilinear form in one variable.

In more classical “vector/matrix” language: if `B` is symmetric and linear
in both arguments, then

B(v + w, v + w) - B(v, v) - B(w, w) = 2 * B(v, w).

-/
theorem polarization_identity {V : Type*} [AddCommGroup V]
    {B : V → V → ℝ} (h_symm : ∀ v w, B v w = B w v)
    (h_bilin : ∀ u v w, B (u + v) w = B u w + B v w) (v w : V) :
  B (v + w) (v + w) - B v v - B w w = 2 * B v w := by
  have h_bilin_right : ∀ u v w, B u (v + w) = B u v + B u w := by
    intro u v w
    rw [h_symm u (v + w), h_bilin v w u, h_symm v u, h_symm w u]
  rw [h_bilin, h_bilin_right, h_bilin_right, h_symm w v]
  ring


/--
*Rank‐1 update* lemma for quadratic forms:
Let `v' := v` except coordinate `i` shifts by `δ`. Then

\[
\sum_{p,q} W_{p,q}\,v'_p\,v'_q \;-\; \sum_{p,q} W_{p,q}\,v_p\,v_q
\;=\;
2\,\delta\,\Bigl(\sum_{j} W_{i,j}\,v_j\Bigr) \;+\;\delta^2\,W_{i,i}.
\]

This is just the standard expansion \((v + \delta e_i)^T W (v + \delta e_i)\).
-/
lemma quadratic_form_rank1_updateState
    (W : Matrix (Fin n) (Fin n) ℝ) (h_sym : W.IsSymm)
    (v : Fin n → ℝ) (i : Fin n) (δ : ℝ) :
  let v' := fun j => if j = i then v j + δ else v j
  ∑ p, ∑ q, W p q * v' p * v' q  -  ∑ p, ∑ q, W p q * v p * v q
    = 2 * δ * ∑ j, W i j * v j  +  δ^2 * W i i := by
  let x := v
  let e_i : Fin n → ℝ := fun j => if j = i then 1 else 0
  let u := fun j => δ * e_i j      -- The rank-1 “update”
  let x' := fun j => x j + u j
  let v' := fun j => if j = i then v j + δ else v j

  -- First check x' = v'
  have eq_v': x' = v' := by
    funext k
    simp [x', u, e_i, v']
    split_ifs with hk <;> ring

  -- Rewrite sums as dotProduct(W.mulVec x) x
  have eq_sum_x : ∑ p, ∑ q, W p q * x p * x q = dotProduct (W.mulVec x) x := by
    simp only [dotProduct, mulVec]
    apply Finset.sum_congr rfl
    intro p _
    -- For each p, rewrite the inner sum
    rw [Finset.sum_mul]
    congr
    funext i
    ring_nf

  have eq_sum_x' : ∑ p, ∑ q, W p q * x' p * x' q = dotProduct (W.mulVec x') x' := by
    simp only [dotProduct, mulVec]
    apply Finset.sum_congr rfl
    intro p _
    -- For each p, rewrite the inner sum
    rw [Finset.sum_mul]
    congr
    funext q
    -- Expand x' according to its definition
    simp [x', u, e_i]
    -- Case analysis on p = i and q = i
    by_cases hp : p = i; by_cases hq : q = i
    · -- Case p = i, q = i
      simp [hp, hq]
    · -- Case p = i, q ≠ i
      simp [hp, hq]
      ring
    · -- Case p ≠ i, q = i
      simp [hp]
      ring

  calc
    (∑ p, ∑ q, W p q * v' p * v' q)
      - (∑ p, ∑ q, W p q * v p * v q)
    = dotProduct (W.mulVec x') x' - dotProduct (W.mulVec x) x
      := by rw [← eq_sum_x', ← eq_sum_x, eq_v']

    -- Expand  (x+u)^T W (x+u) - x^T W x
    --   = x^T W x + x^T W u + u^T W x + u^T W u - x^T W x
    --   = 2 (x^T W u) + u^T W u     (because W is symmetric => x^T W u = u^T W x)
    -- Now  x^T W u = dotProduct x (W.mulVec u) = ∑_{j} x_j [∑_{k} W j k u_k].
    -- But u = δ e_i => only coordinate `i` is nonzero =>  x^T W (δ e_i) = δ ∑_{j} W j i x_j
    -- Then by symmetry W j i = W i j.  Similarly  e_i^T W e_i = W i i.
    _ =
      let Q (z : Fin n → ℝ) := dotProduct (W.mulVec z) z
      Q (x + u) - Q x
      := rfl
    _ = 2 * dotProduct (W.mulVec x) u + dotProduct (W.mulVec u) u
      := by
        -- standard identity for a symmetric form:
        --   Q(x+u) - Q x = 2 (x^T W u) + (u^T W u)
        -- because W is symmetric => x^T W u = u^T W x
        simp only [dotProduct, mulVec]
        ring_nf
        -- Convert sums to dot products, then expand manually
        have h1 : ∀ y z, dotProduct (W.mulVec y) z =
          ∑ x_1, (∑ x_2, W x_1 x_2 * y x_2) * z x_1 := by simp [dotProduct, mulVec]
        -- Define function addition
        have pointwise_add : ∀ (y z : Fin n → ℝ), y + z = fun i => y i + z i := by exact fun y z ↦
          rfl
        simp only [pointwise_add]

        -- Apply the lemma with specific arguments
        have h1_x_plus_u : dotProduct (W.mulVec (x + u)) (x + u) =
          ∑ x_1, (∑ x_2, W x_1 x_2 * (x x_2 + u x_2)) * (x x_1 + u x_1) := by apply h1
        have h1_x : dotProduct (W.mulVec x) x =
          ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * x x_1 := by apply h1

        -- Use these identities directly
        trans
        · exact rfl
        trans
        · exact rfl

        -- Now expand the bilinear forms manually by distributivity
        simp only [add_mul, mul_add]

        -- Expand and simplify the sums directly
        -- Expand the difference manually
        have expansion :
          ∑ x_1, (∑ x_2, W x_1 x_2 * (x x_2 + u x_2)) * (x x_1 + u x_1) -
          ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * x x_1 =
          ∑ x_1, ((∑ x_2, W x_1 x_2 * x x_2) * u x_1 +
                 (∑ x_2, W x_1 x_2 * u x_2) * x x_1 +
                 (∑ x_2, W x_1 x_2 * u x_2) * u x_1) := by
          -- Distribute addition over multiplication
          have h_distribute : ∀ (x_1 : Fin n) (_ : x_1 ∈ Finset.univ),
            (∑ x_2, W x_1 x_2 * (x x_2 + u x_2)) * (x x_1 + u x_1) -
            (∑ x_2, W x_1 x_2 * x x_2) * x x_1 =
            (∑ x_2, W x_1 x_2 * x x_2) * u x_1 +
            (∑ x_2, W x_1 x_2 * u x_2) * x x_1 +
            (∑ x_2, W x_1 x_2 * u x_2) * u x_1 := by
              intro x_1 _
              have h_add_mul : ∑ x_2, W x_1 x_2 * (x x_2 + u x_2) =
                               ∑ x_2, W x_1 x_2 * x x_2 + ∑ x_2, W x_1 x_2 * u x_2 := by
                simp [Finset.sum_add_distrib, mul_add]
              rw [h_add_mul]
              simp [add_mul, mul_add]
              ring

          -- Now apply this to each term in the sum
          have sum_eq :
              ∑ x_1, (∑ x_2, W x_1 x_2 * (x x_2 + u x_2)) * (x x_1 + u x_1) -
              ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * x x_1 =
              ∑ x_1, ((∑ x_2, W x_1 x_2 * (x x_2 + u x_2)) * (x x_1 + u x_1) -
                     (∑ x_2, W x_1 x_2 * x x_2) * x x_1) := by
              simp only [Finset.sum_sub_distrib]

          rw [sum_eq]
          apply Finset.sum_congr rfl h_distribute

        -- First distribute multiplication over addition in the target
        simp only [Finset.sum_add_distrib, add_mul, mul_add]
        -- Now simplify the left side by canceling common terms and rearranging
        have target_simplified :
          ∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * x x_2) * x x_1 +
          ∑ x_1 : Fin n, (∑ x : Fin n, W x_1 x * u x) * x x_1 +
          (∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * x x_2) * u x_1 +
            ∑ x : Fin n, (∑ x_1 : Fin n, W x x_1 * u x_1) * u x) -
          ∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * x x_2) * x x_1 =
          ∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * u x_2) * x x_1 +
          ∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * x x_2) * u x_1 +
          ∑ x_1 : Fin n, (∑ x_2 : Fin n, W x_1 x_2 * u x_2) * u x_1 := by
            -- Cancel the common terms
            ring_nf

        -- Use the fact that expansion has the same terms, just grouped differently
        rw [target_simplified]

        -- Show this equals the right-hand side we need
        -- First, simplify the second term using the definition of u and e_i
        have h_simp : ∀ (x_1 : Fin n), u x_1 = if x_1 = i then δ else 0 := by
          intro x_1
          simp [u, e_i]

        -- Transform sums into equivalent forms
        conv =>
          rhs
          congr
          · -- First part: sum with u * u
            simp [h_simp]
            ring_nf
          · -- Second part: sum with δ * e_i
            simp [h_simp]
            ring_nf

        -- Now both sides have the same form
        ring_nf
        simp [h_simp]
        ring_nf

        -- Now use symmetry of W to simplify
        have symmetry : ∑ x_1, (∑ x_2, W x_1 x_2 * u x_2) * x x_1 =
                        ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * u x_1 := by
          -- Expand outer sum
          have outer_sum : ∑ x_1, (∑ x_2, W x_1 x_2 * u x_2) * x x_1 =
                           ∑ x_1, ∑ x_2, W x_1 x_2 * u x_2 * x x_1 := by
            apply Finset.sum_congr rfl
            intro x_1 _
            simp only [Finset.sum_mul]

          -- Expand right side too
          have right_sum : ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * u x_1 =
                           ∑ x_1, ∑ x_2, W x_1 x_2 * x x_2 * u x_1 := by
            apply Finset.sum_congr rfl
            intro x_1 _
            simp only [Finset.sum_mul]

          -- Rewrite using these expanded forms
          rw [outer_sum, right_sum]

          -- Use interchange of summation and symmetry of W
          calc
            ∑ x_1, ∑ x_2, W x_1 x_2 * u x_2 * x x_1
              = ∑ x_2, ∑ x_1, W x_1 x_2 * u x_2 * x x_1 := by rw [Finset.sum_comm]
            _ = ∑ x_2, ∑ x_1, W x_2 x_1 * u x_2 * x x_1 := by
                apply Finset.sum_congr rfl
                intro x_2 _
                apply Finset.sum_congr rfl
                intro x_1 _
                have : W x_1 x_2 = W x_2 x_1 := by
                  -- Use the symmetry property of W
                  unfold Matrix.IsSymm at h_sym
                  -- This means W i j = W j i for all i, j
                  exact congrFun (congrFun h_sym x_2) x_1
                rw [this]
            _ = ∑ x_2, ∑ x_1, W x_1 x_2 * x x_1 * u x_2 := by
                apply Finset.sum_congr rfl
                intro x_2 _
                apply Finset.sum_congr rfl
                intro x_1 _
                -- Use symmetry of W matrix (W x_2 x_1 = W x_1 x_2)
                have h_symm : W x_2 x_1 = W x_1 x_2 := by
                  unfold Matrix.IsSymm at h_sym
                  exact congrFun (congrFun (id (Eq.symm h_sym)) x_2) x_1
                rw [h_symm]
                -- Rearrange multiplication (commutative)
                ring


            _ = ∑ x_1, ∑ x_2, W x_1 x_2 * x x_2 * u x_1 := by
                -- Swap the order of the sums
                rw [Finset.sum_comm]
                -- Apply symmetry to each term
                apply Finset.sum_congr rfl
                intro y _
                apply Finset.sum_congr rfl
                intro x_1 _
                -- Use symmetry of W
                have : W y x_1 = W x_1 y := by
                  -- The IsSymm property means W = Wᵀ
                  unfold Matrix.IsSymm at h_sym
                  -- This means W y x_1 = W x_1 y
                  have h := congrFun (congrFun h_sym x_1) y
                  exact h
                rw [this]
                -- Since u = δ * e_i, we need to match the terms properly
                simp [u, e_i]
                -- The goal is: W x_1 y * x y * δ * (if x_1 = i then 1 else 0) = W x_1 y * δ * x x_1 * (if y = i then 1 else 0)
                -- We need to examine all cases
                by_cases h1: x_1 = i
                · by_cases h2: y = i
                  · simp [h1, h2]
                  · -- Case where x_1 = i and y ≠ i
                    -- We have h1: x_1 = i and h2: y ≠ i
                    rw [if_pos h1]  -- Since x_1 = i
                    rw [if_neg h2]  -- Since y ≠ i
                    -- The right side is zero due to multiplication by zero
                    -- simp only [mul_zero]
                    -- Show that the left side is also zero
                    simp only [mul_eq_zero]
                    -- We need to prove W x_1 y = 0 ∨ x y = 0 ∨ δ = 0
                    -- Since right side equals 0, the left side must also equal 0
                    -- Choose any disjunct - here we'll assume that δ could be 0
                    apply Or.inr
                    --apply Or.inr
                    sorry -- We need more information to determine which factor is zero

                · by_cases h2: y = i
                  · simp [h1, h2]
                    ring_nf
                    sorry
                  · simp [h1, h2]


            -- Reorder the multiplications using ring
            _ = ∑ x_2, ∑ x_1, W x_2 x_1 * x x_1 * u x_2 := by
                apply Finset.sum_congr rfl
                intro x_2 _
                apply Finset.sum_congr rfl
                exact fun x_1 a ↦ rfl

        have sum_with_ei : ∑ x_1 : Fin n, (∑ x : Fin n, W x_1 x * δ * e_i x) * x x_1 =
                           δ * ∑ x_1 : Fin n, W x_1 i * x x_1 := by
          -- Pull δ out of both sums
          simp only [Finset.mul_sum]

          -- Extract the constant multiplier δ
          rw [Finset.sum_congr rfl]
          intro x_1 _
          rw [Finset.sum_mul]
          congr
          -- Simplify using properties of summation and δ
          have h_sum : ∑ i : Fin n, W x_1 i * δ * e_i i * x x_1 = W x_1 i * δ * x x_1 := by
            -- Only the i-th term contributes due to e_i
            rw [Finset.sum_eq_single i]
            · simp [e_i]
            · intro j _ hj
              simp [e_i, hj]
            · intro h
              simp [h]
              aesop
          rw [h_sum]
          ring

        -- Simplify the other side with e_i
        have sum_with_ei_right : (∑ x_1 : Fin n, (δ * ∑ x_2 : Fin n, W x_1 x_2 * x x_2) * e_i x_1) * 2 =
                                 2 * δ * ∑ x_2 : Fin n, W i x_2 * x x_2 := by
          -- Pull δ out of the sum
          simp only [Finset.sum_mul]
          -- For e_i x_1, only the term where x_1 = i is non-zero
          have h_e_i : ∀ x, e_i x = if x = i then 1 else 0 := by simp [e_i]
          simp only [h_e_i]
          -- Simplify the sum
          simp [Finset.sum_ite_eq']
          -- Simplify the conditional
          --simp
          -- Rearrange terms
          ring

        -- Use symmetry of W
        have W_sym : ∑ x_1 : Fin n, W x_1 i * x x_1 = ∑ x_2 : Fin n, W i x_2 * x x_2 := by
          -- Use the fact that W is symmetric
          apply Finset.sum_congr rfl
          intro j _
          have h_sym_at_ij : W j i = W i j := by
            -- Use the symmetry property
            unfold Matrix.IsSymm at h_sym
            -- Extract the specific instance we need
            exact congrFun (congrFun h_sym i) j
          rw [h_sym_at_ij]

        -- Rewrite the goal using these facts
        rw [sum_with_ei, sum_with_ei_right, W_sym]

        -- Simplify algebraic expressions
        ring
    -- Evaluate x^T W u and u^T W u when u = δ e_i
    _ = 2 * δ * ∑ j, W i j * x j + δ^2 * W i i
      := by
        -- 1) dotProduct (W.mulVec x) u = δ * dotProduct (W.mulVec x) e_i
        --    = δ * (W.mulVec x i) = δ * ∑_{j} W i j * x j
        -- 2) dotProduct (W.mulVec u) u = δ^2 * dotProduct (W.mulVec e_i) e_i
        --    = δ^2 * (W.mulVec e_i i) = δ^2 * ∑_{j} W i j * e_i j = δ^2 * W i i
        simp only [u, e_i, dotProduct, mulVec]

        -- First term: dotProduct (W.mulVec x) u
        have h_first_term : ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * δ * (if x_1 = i then (1 : ℝ) else 0) =
                           δ * ∑ j, W i j * x j := by
          -- Split sum into cases where x_1 = i and x_1 ≠ i
          rw [Finset.sum_eq_single i]
          · -- Case where x_1 = i
            simp only [eq_self_iff_true, if_true, mul_one]
            ring
          · -- Case where x_1 ≠ i
            intro x_1 _ hx1
            simp only [if_neg hx1, mul_zero]
          · -- Show i is in the universe
            intro a
            simp_all only [mul_ite, mul_one, mul_zero, ite_mul,
             Finset.mem_univ, not_true_eq_false, v', u, e_i, x', x]

        -- Second term: dotProduct (W.mulVec u) u
        have h_second_term : ∑ x, (δ * ∑ x_1, W x x_1 * δ * (if x_1 = i then (1 : ℝ) else 0)) * (if x = i then (1 : ℝ) else 0) =
                             δ^2 * W i i := by
          -- Split the outer sum based on x = i
          rw [Finset.sum_eq_single i]
          · -- Case where x = i
            have h_inner : ∑ x_1, W i x_1 * δ * (if x_1 = i then (1 : ℝ) else 0) = δ * W i i := by
              rw [Finset.sum_eq_single i]
              · simp only [eq_self_iff_true, if_true, mul_one]
                ring
              · intro x _hx hx
                simp only [if_neg hx, mul_zero]
              · intro h
                simp only [h, not_false_eq_true]
                simp_all only [mul_ite, mul_one, mul_zero, ite_mul, Finset.sum_ite_eq', ↓reduceIte, zero_eq_mul,
                  Finset.mem_univ, not_true_eq_false, v', u, x, e_i, x']
            simp only [eq_self_iff_true, if_true, mul_one]
            rw [h_inner]
            ring
          · -- Case where x ≠ i
            intro x _hx hx
            simp only [if_neg hx, mul_zero]
          · -- Show i is in the universe
            intro h
            simp only [h, not_false_eq_true]
            simp_all only [mul_ite, mul_one, mul_zero, ite_mul, Finset.sum_ite_eq', ↓reduceIte, zero_eq_mul,
              Finset.mem_univ, not_true_eq_false, v', u, x, e_i, x']

        -- First extract the common factor δ from the first sum
        have h1 : 2 * ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * (δ * if x_1 = i then 1 else 0) =
                 2 * δ * ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * (if x_1 = i then 1 else 0) := by ring_nf; simp_all only [mul_ite,
                   mul_one, mul_zero, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, v', u, x, e_i, x']

        -- Use our h_first_term after extracting δ
        have h2 : ∑ x_1, (∑ x_2, W x_1 x_2 * x x_2) * (if x_1 = i then 1 else 0) =
                 ∑ j, W i j * x j := by
          -- Simplify the sum using the property of the conditional
          rw [Finset.sum_eq_single i]
          · -- Case where x_1 = i
            simp only [eq_self_iff_true, if_true, mul_one]
          · -- Case where x_1 ≠ i
            intro x_1 _ hx1
            simp only [if_neg hx1, mul_zero]
          · -- Show i is in the universe
            intro h
            simp only [h, not_false_eq_true]
            simp_all only [Finset.mem_univ]
            simp_all only [mul_ite, mul_one, mul_zero, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
              zero_eq_mul, ite_self, Finset.sum_const_zero, pow_eq_zero_iff', ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, and_false, false_or, v', u, x, e_i, x']


        -- Simplify the second sum to match h_second_term
        have h3 : ∑ x, (∑ x_1, W x x_1 * (δ * if x_1 = i then 1 else 0)) * (δ * if x = i then 1 else 0) =
                 ∑ x, (δ * ∑ x_1, W x x_1 * δ * (if x_1 = i then 1 else 0)) * (if x = i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : x = i
          · simp [h]
            ring
          · simp [h]

        -- Now combine everything
        rw [h1]
        rw [h2]
        rw [h3]
        rw [h_second_term]


/--
A small corollary: if we change exactly one spin in `x` (coordinate `i`),
the difference in energy from `x'` to `x` is exactly the “local field times the spin change”,
unless we also wish to track the diagonal of `W`.
Here we ignore the diagonal term because `weights_diag_zero net` often zeroes it out.
-/
lemma energy_component_difference
    (net : HopfieldNetwork n) (x : HopfieldState n) (i : Fin n) (s' : SpinState) :
  let x' := fun j => if j = i then s' else x j
  energy net x' - energy net x
    = - ( localField net x i * (s'.toReal - (x i).toReal ) )
      - 0.5 * ( (s'.toReal - (x i).toReal)^2 * (weightsMatrix net) i i ) := by
  let δ := s'.toReal - (x i).toReal
  let x' := fun j => if j = i then s' else x j
  let x'_real := fun j => if j = i then s'.toReal else (x j).toReal
  --dsimp [HopfieldState.toRealVector, energy, Matrix.toBilin']
  simp only [Finset.univ_sum_single, Finset.range_one, sub_eq_add_neg]
  -- Break energy into the -0.5 * x^T W x  - ∑ b_i x_i part
  let W := weightsMatrix net
  let thr := net.thresholds
  let Q (z : Fin n → ℝ) := dotProduct (W.mulVec z) z
  calc
    energy net x' - energy net x
    = ( -0.5 * Q x'_real - ∑ j, thr j * x'_real j )
      - ( -0.5 * Q (fun j ↦ (x j).toReal) - ∑ j, thr j * (x j).toReal ) := by
      -- Unfold the energy definition
      simp only [energy]
      -- Show equivalence between the different forms
      have h1 : ((toBilin' (weightsMatrix net)) (toRealVector x')) (toRealVector x') = Q x'_real := by
        -- Expand definitions to show they're equal
        unfold toBilin'
        have h_equiv : toRealVector x' = x'_real := by
          funext j
          simp [toRealVector, x'_real]
          exact apply_ite toReal (j = i) s' (x j)
        rw [h_equiv]
        unfold Q
        -- The definitions match directly after expanding
        unfold dotProduct mulVec
        -- Need to use the simp lemma for LinearMap.BilinForm.toMatrix'.symm instead of unfold
        simp only [LinearMap.BilinForm.toMatrix'_symm, x'_real]
        -- Direct proof of equality using the definitions
        simp only [dotProduct, mulVec]

          -- We need to explicitly expand the bilinear form
        have expand_bilin : ((toBilin' W) (toRealVector x')) (toRealVector x') = ∑ x_1, ∑ x_2, W x_1 x_2 * (toRealVector x' x_1) * (toRealVector x' x_2) := by
          -- Definition of toBilin' expanded
          unfold toBilin'
          -- Define what toBilin' expands to
          have h_def : ∀ (a b : Fin n → ℝ), ((toBilin' W) a) b = ∑ x_1, ∑ x_2, W x_1 x_2 * a x_1 * b x_2 := by
            intro a b
            simp only [toBilin']
            -- Expand the definition of LinearMap.BilinForm.toMatrix'.symm
            simp only [dotProduct, mulVec]
            -- Need to unwrap the definition and show the equality explicitly
            -- This is the expansion of LinearMap.BilinForm.toMatrix'.symm
            have h_expand : ((LinearMap.BilinForm.toMatrix'.symm W) a) b =
              ∑ x_1, (∑ x_2, W x_1 x_2 * a x_2) * b x_1 := by rfl
            rw [h_expand]
            -- Rearrange the nested sums to match the target
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x_1 _
            rw [mul_comm]
            apply Finset.sum_congr rfl
            intro x_2 _
            ring

          -- Apply the definition directly
          exact h_def (toRealVector x') (toRealVector x')

        -- Expand x'_real into if-then-else form
        rw [expand_bilin]
        apply Finset.sum_congr rfl
        intro x_1 _

        -- Break into cases for x_1 = i or x_1 ≠ i
        by_cases h_x1 : x_1 = i
        · -- Case x_1 = i
          rw [if_pos h_x1]
          apply Finset.sum_congr rfl
          intro x_2 _
          -- Break into cases for x_2 = i or x_2 ≠ i
          by_cases h_x2 : x_2 = i
          · -- Case x_2 = i
            rw [if_pos h_x2]
            congr
          · -- Case x_2 ≠ i
            rw [if_neg h_x2]
            congr

        · -- Case x_1 ≠ i
          rw [if_neg h_x1]
          congr
          apply Finset.sum_congr rfl
          intro x_2 _
          by_cases h_x2 : x_2 = i
          · -- Case x_2 = i
            rw [if_pos h_x2]
            congr
          · -- Case x_2 ≠ i
            rw [if_neg h_x2]
            congr

      have h2 : ((toBilin' (weightsMatrix net)) x.toRealVector) x.toRealVector = Q (fun j ↦ (x j).toReal) := by
        simp only [Q, dotProduct, mulVec, toBilin']
        -- Expand definitions to show these are equal
        unfold Matrix.toBilin'
        simp only [dotProduct, mulVec]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        congr
        · rfl
        · rfl
      have h3 : ∀ j, x'_real j = toRealVector x' j := by
        intro j
        simp [x'_real, x', toRealVector]
      have h4 : ∀ j, (x j).toReal = x.toRealVector j := by
        intro j
        simp [toRealVector]

      rw [h1, h2]
      apply congr_arg₂ Sub.sub
      · congr
        · exact
          Eq.symm
            ((fun {α β} f₁ f₂ ↦ (Set.eqOn_univ f₁ f₂).mp) (fun j ↦ thr j * x'_real j)
              (fun i ↦ net.thresholds i * toRealVector x' i) fun ⦃x⦄ a ↦
              congrArg (HMul.hMul (thr x)) (h3 x))
      · congr
    _ = -0.5 * (Q x'_real - Q (fun j ↦ (x j).toReal))
      - ∑ j, thr j * (x'_real j - (x j).toReal) := by
      -- Use ring arithmetic to rearrange the terms
      simp only [neg_mul]
      ring_nf
      sorry
    -- Evaluate Q(...) difference via `quadratic_form_rank1_updateState`
    -- with δ, plus the threshold part
    _ = -0.5 * (
           2 * δ * ∑ j, W i j * (x j).toReal
           + δ^2 * W i i
         )
         - (thr i * δ)
      := by
        -- Define a variable for the shifted vector that matches what quadratic_form_rank1_updateState expects
        let v := fun j => (x j).toReal
        let v' := fun j => if j = i then (x j).toReal + δ else (x j).toReal

        -- Show x'_real equals v'
        have h_x'_real_eq_v' : x'_real = v' := by
          funext j
          simp only [x'_real, v']
          by_cases h : j = i
          · simp [h]
            have : s'.toReal = (x j).toReal + δ := by
              simp [h, δ]
            exact Eq.symm (add_sub_cancel (x i).toReal s'.toReal)
          · simp [h]

        apply congr_arg₂ Sub.sub
        · -- the -0.5 * [Q(x') - Q(x)] part
          have h_quadratic : Q x'_real - Q v =
                            2 * δ * ∑ j, W i j * v j + δ^2 * W i i := by
            -- Apply quadratic_form_rank1_updateState
            rw [h_x'_real_eq_v']
            rfl

          -- Apply our result
          rw [h_quadratic]

        · -- the threshold part: ∑ j, thr j * (x'_real j - (x j).toReal) = thr i * δ
          have h_threshold : ∑ j, thr j * (x'_real j - (x j).toReal) = thr i * δ := by
            -- Only the i-th term contributes to the sum
            rw [Finset.sum_eq_single i]
            · -- Main term
              simp only [x'_real]
              by_cases h : i = i
              · simp [h]
                ring_nf
                exact Or.symm (Or.inr trivial)
              · contradiction
            · -- Other terms are zero
              intro j _ hj
              aesop
            aesop
          aesop

/--
If `x'` differs from `x` in exactly one coordinate `i`, then
the difference in energy simplifies further, because in a typical Hopfield
setup we take the diagonal of `W` to be zero.  Then `δ^2 * W i i` vanishes.
-/
lemma energy_diff_single_component
    (net : HopfieldNetwork n) (x x' : HopfieldState n) (i : Fin n)
    (h_diff : ∀ j, j ≠ i → x' j = x j) :
  energy net x' - energy net x
    = - ( (localField net x i) * (x'.toRealVector i - x.toRealVector i) ) := by
  -- Let s' = x' i, so δ = x'.toRealVector i - x.toRealVector i
  let s' := x' i
  have eq_x' : x' = fun j => if j = i then s' else x j := by
    ext j
    by_cases hj : j = i
    · simp [hj]
      exact rfl
    · simp [hj, h_diff j hj]
  rw [eq_x']
  simp only [SpinState.toReal, HopfieldState.toRealVector]
  -- Then apply `energy_component_difference` plus the fact that W i i = 0 in typical Hopfield
  apply [weights_diag_zero]
  let δ := s'.toReal - (x i).toReal
  calc
    energy net (fun j => if j = i then s' else x j) - energy net x
      = - ( localField net x i * δ )
        - 0.5 * (δ^2 * (weightsMatrix net) i i )
      := energy_component_difference net x i s'
    _ = - ( localField net x i * δ )    -- since W i i = 0
      := by simp [weights_diag_zero]; exact?




#print energy_diff_single_component
#print energy_component_difference
#print quadratic_form_rank1_updateState
#print polarization_identity
#print weights_diag_zero

--end HopfieldNetwork
