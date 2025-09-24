import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped InnerProductSpace RealInnerProductSpace

-- We work over a general Nontrivially Normed Field 𝕜.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The continuous linear map that composes a continuous linear map with a given continuous linear
map `f` on the right. This is the "right-composition" operator.
`compRightL 𝕜 E F` is the map `g ↦ g.comp f` where `f : E →L[𝕜] F` and `g : F →L[𝕜] G`. -/
noncomputable def compRightL (f : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] (E →L[𝕜] G) :=
  (ContinuousLinearMap.compL 𝕜 E F G).flip f

@[simp]
theorem compRightL_apply (f : E →L[𝕜] F) (g : F →L[𝕜] G) :
    compRightL f g = g.comp f :=
  rfl

/-- The dual map of a continuous linear map `f`, is the continuous linear map from the dual of the
codomain to the dual of the domain, given by pre-composition with `f`. -/
noncomputable def dualMap (f : E →L[𝕜] F) :
    StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E :=
  compRightL f

@[simp]
theorem dualMap_apply {f : E →L[𝕜] F} {g : StrongDual 𝕜 F} :
    dualMap f g = g.comp f := rfl

@[simp]
theorem dualMap_apply_apply {f : E →L[𝕜] F} {g : StrongDual 𝕜 F} {x : E} :
    (dualMap f g) x = g (f x) := rfl

@[simp]
theorem dualMap_comp {f : E →L[𝕜] F} {g : F →L[𝕜] G} :
    dualMap (g.comp f) = (dualMap f).comp (dualMap g) := by
  ext h
  simp only [comp_apply, dualMap_apply, ContinuousLinearMap.comp_assoc]

end ContinuousLinearMap

/-!
# L1 Generalized: Differentiable Pullbacks (Banach Spaces)
-/

-- E, F, G are Normed Spaces over 𝕜 (Banach if CompleteSpace is assumed).
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/--
The fundamental abstraction for differentiable computation in Banach spaces.
Represents a function and its backpropagator operating on the dual spaces (the pullback).
-/
structure DifferentiablePullback (E F : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  view : E → F
  h_diff : Differentiable 𝕜 view
  /-- The pullback: E → (F* →L[𝕜] E*). Returns the dual map of Df(x). -/
  pullback : E → (StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)
  /-- Correctness: The pullback map must be the dual map of the Fréchet derivative. -/
  h_pullback : ∀ (x : E),
    pullback x = ContinuousLinearMap.dualMap (fderiv 𝕜 view x)

namespace DifferentiablePullback

def compose {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (L1 : @DifferentiablePullback 𝕜 _ F G _ _ _ _) (L2 : @DifferentiablePullback 𝕜 _ E F _ _ _ _) :
    @DifferentiablePullback 𝕜 _ E G _ _ _ _ where
  view := L1.view ∘ L2.view
  h_diff := L1.h_diff.comp L2.h_diff
  pullback := fun x =>
    -- (g ∘ f)* = f* ∘ g*
    (L2.pullback x).comp (L1.pullback (L2.view x))
  h_pullback := by
    intro x
    simp only [L2.h_pullback x, L1.h_pullback (L2.view x)]
    -- Now we have: goal is to show
    -- (L2.pullback x).comp (L1.pullback (L2.view x)) =
    -- dualMap (fderiv 𝕜 (L1.view ∘ L2.view) x)
    rw [← ContinuousLinearMap.dualMap_comp]
    -- Now we need to show:
    -- dualMap ((fderiv 𝕜 L1.view (L2.view x)).comp (fderiv 𝕜 L2.view x)) =
    -- dualMap (fderiv 𝕜 (L1.view ∘ L2.view) x)
    congr 1
    rw [← fderiv_comp x (L1.h_diff (L2.view x)) (L2.h_diff x)]

end DifferentiablePullback

/-!
# L1 Specialization: Differentiable Lenses (Hilbert Spaces)
-/

-- H1, H2, H3 are Hilbert spaces. We require 𝕜' to be RCLike (ℝ or ℂ) for the standard Hilbert adjoint.
variable {𝕜' : Type*} [RCLike 𝕜']
variable {H1 H2 H3 : Type*}
  [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
  [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2]
  [NormedAddCommGroup H3] [InnerProductSpace 𝕜' H3] [CompleteSpace H3]

/--
A Differentiable Lens in Hilbert spaces. Uses the Hilbert adjoint for gradient flow.
-/
structure DifferentiableLens (𝕜' : Type*) (H1 H2 : Type*)
  [RCLike 𝕜']
  [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
  [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2] where
  view : H1 → H2
  h_diff : Differentiable 𝕜' view
  /-- The backward map (Adjoint): H1 → (H2 →L[𝕜'] H1). -/
  update : H1 → (H2 →L[𝕜'] H1)
  /-- Correctness: The update map must be the Hilbert adjoint of the Fréchet derivative. -/
  h_update : ∀ (x : H1),
    update x = ContinuousLinearMap.adjoint (fderiv 𝕜' view x)

namespace DifferentiableLens

/-- Composition of Lenses (The Chain Rule in Hilbert Spaces). -/
def compose {𝕜' : Type*} [RCLike 𝕜'] {H1 H2 H3 : Type*}
    [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
    [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2]
    [NormedAddCommGroup H3] [InnerProductSpace 𝕜' H3] [CompleteSpace H3]
    (L1 : DifferentiableLens 𝕜' H1 H2) (L2 : DifferentiableLens 𝕜' H2 H3) :
    DifferentiableLens 𝕜' H1 H3 where
  view := L2.view ∘ L1.view
  h_diff := L2.h_diff.comp L1.h_diff
  update := fun x =>
    let y := L1.view x
    -- (g ∘ f)† = f† ∘ g†
    (L1.update x).comp (L2.update y)
  h_update := by
    intro x
    simp_rw [L1.h_update, L2.h_update (L1.view x)]
    -- Apply the chain rule: fderiv (g ∘ f) x = (fderiv g (f x)) ∘ (fderiv f x)
    rw [fderiv_comp x (L2.h_diff (L1.view x)) (L1.h_diff x)]
    rw [ContinuousLinearMap.adjoint_comp]

end DifferentiableLens

/-!
# L1 Refinement: Higher-Order Calculus
-/

section HigherOrderCalculus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
The second derivative (Hessian) of a function f: E → F at x.
It is the Fréchet derivative of the Fréchet derivative map.
H(x) : E →L[𝕜] (E →L[𝕜] F).
-/
noncomputable def Hessian (f : E → F) (x : E) : E →L[𝕜] (E →L[𝕜] F) :=
  fderiv (𝕜 := 𝕜) (fderiv (𝕜 := 𝕜) f) x

/--
Hessian-Vector Products (Hv-products). Computes (H(x)v₁v₂).
This is the second derivative evaluated in the directions v₁ and v₂.
-/
noncomputable def HessianVectorProduct (f : E → F) (x v₁ v₂ : E) : F :=
  ((Hessian (𝕜 := 𝕜) (E := E) (F := F) f x) v₁) v₂

-- Note: Higher-order derivatives are accessed directly via `iteratedFDeriv 𝕜 n f x`.

-- H is a Hilbert space over ℝ for optimization contexts (required for `gradient`).
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Hessian-Vector Products (Hv-products) for scalar-valued functions. Computes H(x)v.
This utilizes the definition that the Hessian applied to v is the directional derivative
of the gradient along v (Forward-over-Reverse AD).
The result is a vector in H.
-/
noncomputable def HessianVectorProduct' (f : H → ℝ) (x v : H) : H :=
  let g := gradient f
  (fderiv ℝ g x) v

end HigherOrderCalculus

/-!
# L1 Refinement: The Riesz Bridge
We formalize the connection between the Banach dual map and the Hilbert adjoint.
-/

section RieszBridge

-- H1, H2 are Hilbert spaces over 𝕜' (ℝ or ℂ).
variable {𝕜' : Type*} [RCLike 𝕜']
variable {H1 H2 : Type*}
  [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
  [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2]

/--
The Riesz Representation Map H ≃L[𝕜'] H*.
It is a conjugate-linear isometric isomorphism targeting the `StrongDual`.
In mathlib: `InnerProductSpace.toDual`.
-/
noncomputable abbrev RieszMap (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜' H] [CompleteSpace H] :
  H ≃ₗᵢ⋆[𝕜'] StrongDual 𝕜' H :=
  InnerProductSpace.toDual 𝕜' H

/--
Theorem: The Riesz Bridge.
The Hilbert adjoint L† is related to the Banach dual map L* by the Riesz isomorphisms R_H:
L† = R₁⁻¹ ∘ L* ∘ R₂.
This shows that the optimization geometry (Hilbert adjoint) is derived from
the differentiation mechanism (Banach dual map).
-/
theorem riesz_bridge_adjoint
    (L : H1 →L[𝕜'] H2) :
    L.adjoint =
      ((RieszMap H1).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        ((ContinuousLinearMap.dualMap L).comp
        ((RieszMap H2).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  simp; exact rfl

end RieszBridge

/-!
# L2: Parameterized Lenses for Neural Networks
-/

section ParameterizedLens

variable {𝕜' : Type*} [RCLike 𝕜']
variable {P H_in H_out : Type*}
  [NormedAddCommGroup P] [InnerProductSpace 𝕜' P] [CompleteSpace P]
  [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in]
  [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out]

-- Provide an inner product space instance for the Unit type.
noncomputable instance : InnerProductSpace 𝕜' Unit where
  inner _ _ := 0
  norm_sq_eq_re_inner _ := by simp
  conj_inner_symm _ _ := by simp
  add_left _ _ _ := by simp
  smul_left _ _ _ := by simp

/-
/--
A DifferentiableLens that is parameterized by a set of weights `P`.
The `view` function now takes parameters `p` and an input `x`.
The `update` function computes the adjoint, which can be used to derive gradients
with respect to both the parameters and the input.
-/
structure ParameterizedLens (𝕜' : Type*) (P H_in H_out : Type*)
  [RCLike 𝕜']
  [NormedAddCommGroup P] [InnerProductSpace 𝕜' P] [CompleteSpace P]
  [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in]
  [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out] where
  view : P → H_in → H_out
  h_diff : Differentiable 𝕜' (fun (ph : P × H_in) => view ph.1 ph.2)
  /-- The backward map (Adjoint): P × H_in → (H_out →L[𝕜'] P × H_in). -/
  update : P → H_in → (H_out →L[𝕜'] P × H_in)
  /-- Correctness: The update map must be the Hilbert adjoint of the Fréchet derivative. -/
  h_update : ∀ (p : P) (x : H_in),
    update p x = ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : P × H_in) => view ph.1 ph.2) (p, x))

namespace ParameterizedLens

/--
An affine layer `x ↦ Ax + b`.
Parameters `P` are `(H_in →L[𝕜'] H_out) × H_out`, representing the matrix `A` and bias `b`.
We require `H_in` to be finite-dimensional to have an inner product on the space of linear maps.
-/
def affineLayer (H_in H_out : Type*) [NormedAddCommGroup H_in] [InnerProductSpace 𝕜' H_in] [CompleteSpace H_in] [FiniteDimensional 𝕜' H_in]
    [NormedAddCommGroup H_out] [InnerProductSpace 𝕜' H_out] [CompleteSpace H_out] :
    ParameterizedLens 𝕜' ((H_in →L[𝕜'] H_out) × H_out) H_in H_out where
  view p x := p.1 x + p.2
  h_diff := by
    let f1 : ((H_in →L[𝕜'] H_out) × H_out) × H_in → (H_in →L[𝕜'] H_out) × H_in := fun p_x => (p_x.1.1, p_x.2)
    let f2 : (H_in →L[𝕜'] H_out) × H_in → H_out := fun p_x => p_x.1 p_x.2
    let f3 : ((H_in →L[𝕜'] H_out) × H_out) × H_in → H_out := fun p_x => p_x.1.2
    have h_f1 : Differentiable 𝕜' f1 := by simp; exact differentiable_fst.prod differentiable_snd
    have h_f2 : Differentiable 𝕜' f2 := isBoundedBilinearMap_apply.differentiable
    have h_f3 : Differentiable 𝕜' f3 := by simp; exact differentiable_snd.comp differentiable_fst
    exact (h_f2.comp h_f1).add h_f3
  update p x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun ph => view ph.1 ph.2) (p, x))
  h_update p x := rfl

/--
An element-wise activation layer, e.g., ReLU or sigmoid.
It has no parameters (`P = Unit`), so it's a special case of a `ParameterizedLens`.
-/
def elementwise (f : H_in → H_out) (h_f : Differentiable 𝕜' f) :
    ParameterizedLens 𝕜' Unit H_in H_out where
  view _ x := f x
  h_diff := Differentiable.comp h_f differentiable_snd
  update _ x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : Unit × H_in) => f ph.2) ((), x))
  h_update _ _ := rfl

/--
Mean Squared Error loss function: `L(y_pred, y_true) = ‖y_pred - y_true‖²`.
This is a `ParameterizedLens` with `H_in = H_out × H_out` (predicted and true values)
and output `H_out = ℝ`. It has no parameters (`P = Unit`).
-/
def mseLoss (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜' H] [CompleteSpace H] :
    ParameterizedLens 𝕜' Unit (H × H) ℝ where
  view _ y_yh := ‖y_yh.1 - y_yh.2‖ ^ 2
  h_diff := by
    have h_norm_sq : Differentiable 𝕜' (fun (v : H) => ‖v‖ ^ 2) := by
      simp_rw [← inner_self_eq_norm_sq_to_K]
      have := isBoundedBilinearMap_inner 𝕜' H
      exact this.differentiable.comp (differentiable_id.prod_mk differentiable_id)
    exact Differentiable.comp h_norm_sq (differentiable_fst.sub differentiable_snd)
  update _ y_yh := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun (ph : Unit × (H × H)) => ‖ph.2.1 - ph.2.2‖ ^ 2) ((), y_yh))
  h_update _ _ := rfl

variable {P1 H1 H2 P2 H3 : Type*}
  [NormedAddCommGroup P1] [InnerProductSpace 𝕜' P1] [CompleteSpace P1]
  [NormedAddCommGroup H1] [InnerProductSpace 𝕜' H1] [CompleteSpace H1]
  [NormedAddCommGroup H2] [InnerProductSpace 𝕜' H2] [CompleteSpace H2]
  [NormedAddCommGroup P2] [InnerProductSpace 𝕜' P2] [CompleteSpace P2]
  [NormedAddCommGroup H3] [InnerProductSpace 𝕜' H3] [CompleteSpace H3]

/-- Composition of ParameterizedLenses. -/
def compose (L2 : ParameterizedLens 𝕜' P2 H2 H3) (L1 : ParameterizedLens 𝕜' P1 H1 H2) :
    ParameterizedLens 𝕜' (P1 × P2) H1 H3 where
  view p x := L2.view p.2 (L1.view p.1 x)
  h_diff := by
    let f_combined : (P1 × P2) × H1 → (P2 × H2) :=
      fun p_x => (p_x.1.2, L1.view p_x.1.1 p_x.2)
    have h_f_combined : Differentiable 𝕜' f_combined :=
      (differentiable_snd.comp differentiable_fst).prod (L1.h_diff.comp ((differentiable_fst.comp differentiable_fst).prod differentiable_snd))
    exact L2.h_diff.comp h_f_combined
  update p x := ContinuousLinearMap.adjoint (fderiv 𝕜' (fun ph => view ph.1 ph.2) (p, x))
  h_update p x := rfl

/--
A single step of gradient descent for a parameterized lens.
Computes the gradient of the loss with respect to the parameters and updates them.
-/
def gradientDescentStep
    (L : ParameterizedLens 𝕜' P H_in H_out)
    (loss : ParameterizedLens 𝕜' Unit (H_out × H_out) ℝ)
    (p : P) (x : H_in) (y_true : H_out) (η : ℝ) : P :=
  let y_pred := L.view p x
  let _loss_val := loss.view () (y_pred, y_true)
  -- The adjoint of the composed forward map gives the gradients.
  -- The derivative of the loss w.r.t. its input is needed.
  -- For MSE `‖y - y'‖²`, the gradient w.r.t. `y` is `2(y - y')`.
  -- The `update` function for the loss gives the adjoint of the derivative.
  -- We apply it to `1` (the gradient of the identity function `z ↦ z` at `loss_val`).
  let dL_dy_pred_adj : Unit × (H_out × H_out) := (loss.update () (y_pred, y_true)) (1 : ℝ)
  -- The adjoint returns a pair of gradients: (w.r.t. y_pred, w.r.t. y_true). We need the first.
  let dL_dy_pred := dL_dy_pred_adj.2.1
  -- Propagate this gradient back through the lens L.
  let grads := (L.update p x) dL_dy_pred
  -- The result is a pair of gradients: (w.r.t. parameters, w.r.t. input). We need the first.
  let dL_dp := grads.1
  -- Update parameters
  p - (η : 𝕜') • dL_dp

end ParameterizedLens
-/

/-!
# Differentiable computational blocks and VJPs (general Banach + Hilbert specializations)

A CompBlock is a smooth, parameterized operation fwd : P × X → Y over a base field 𝕜.
We expose its Jacobian (via fderiv), a Banach-space VJP (via the dual map), and a
Hilbert-space VJP (via the adjoint). We also provide a bridge back into your
DifferentiablePullback abstraction for reuse of composition theorems.
-/

section CompBlock

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A differentiable, parameterized block: fwd : P × X → Y with a differentiability certificate. -/
structure CompBlock (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (P X Y : Type*)
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  fwd   : P × X → Y
  diff  : Differentiable 𝕜 fwd

namespace CompBlock

/-- The Fréchet derivative (Jacobian) of a block at (p, x). -/
noncomputable def jacobian
    (B : CompBlock 𝕜 P X Y) (p : P) (x : X) : (P × X) →L[𝕜] Y :=
  fderiv 𝕜 B.fwd (p, x)

/-- Banach VJP: the pullback on duals (StrongDual) induced by the Jacobian. -/
noncomputable def vjpBanach
    (B : CompBlock 𝕜 P X Y) (p : P) (x : X) :
    (StrongDual 𝕜 Y) →L[𝕜] (StrongDual 𝕜 (P × X)) :=
  ContinuousLinearMap.dualMap (B.jacobian p x)

/-- Package the block as a DifferentiablePullback from P × X to Y. -/
noncomputable def toDifferentiablePullback
    (B : CompBlock 𝕜 P X Y) :
    @DifferentiablePullback 𝕜 _ (P × X) Y _ _ _ _ where
  view := B.fwd
  h_diff := B.diff
  pullback := fun z => ContinuousLinearMap.dualMap (fderiv 𝕜 B.fwd z)
  h_pullback := by intro z; rfl

/- Hilbert-space VJP via the adjoint (requires inner products over an RCLike field). -/
variable {𝕜' : Type*} [RCLike 𝕜']
variable {P' X' Y' : Type*}
  [NormedAddCommGroup P'] [InnerProductSpace 𝕜' P'] [CompleteSpace P']
  [NormedAddCommGroup X'] [InnerProductSpace 𝕜' X'] [CompleteSpace X']
  [NormedAddCommGroup Y'] [InnerProductSpace 𝕜' Y'] [CompleteSpace Y']

open scoped InnerProductSpace RealInnerProductSpace PiLp EuclideanSpace

/-
noncomputable def vjpHilbert
    (B : CompBlock 𝕜' P' X' Y') (p : P') (x : X') :
    Y' →L[𝕜'] (P' × X') :=
  have := Prod.innerProductSpace
  ContinuousLinearMap.adjoint (fderiv 𝕜' B.fwd (p, x))
  -/

end CompBlock
end CompBlock
