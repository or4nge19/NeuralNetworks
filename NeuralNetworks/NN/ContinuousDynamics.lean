import Mathlib
open ProbabilityTheory MeasureTheory
open scoped ENNReal

-- Time is generalized to an Ordered Additive Commutative Monoid (covers ℕ, ℝ, hybrid time)
variable {T : Type*} [AddCommMonoid T] [PartialOrder T] [IsOrderedAddMonoid T] [TopologicalSpace T]

/-- Generalized Dynamical System (Action of Time Monoid on State Space) -/
class DynamicalSystem (S : Type*) [TopologicalSpace S] where
  evolve : S → T → S
  h_identity : ∀ s, evolve s 0 = s
  h_flow : ∀ s t1 t2, evolve (evolve s t1) t2 = evolve s (t1 + t2)

/-- Rigorous Continuous Dynamics (ODEs). S must be a Banach space. (T=ℝ) -/
class RigorousContinuousDynamics (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    extends DynamicalSystem S (T := ℝ) where
  vectorField : S → S -- Autonomous ODE for simplicity
  /-- Crucial Requirement: Locally Lipschitz continuous for unique solutions (Picard-Lindelöf). -/
  h_lipschitz : LocallyLipschitz vectorField
  --/-- The evolution is definitionally the flow of the vector field. -/
  --evolve_def : ∀ s t, evolve s t = (Analysis.ODE.flow vectorField t) s
  /-- Proof obligation: The flow satisfies the ODE (dx/dt = V(x)). -/
  h_is_solution : ∀ s t, HasDerivAt (fun t' => evolve s t') (vectorField (evolve s t)) t

/-- Stochastic Dynamics using Markov Kernels (e.g., MCMC, Gibbs Sampling). (T=ℕ) -/
class MarkovDynamics (S : Type*) [MeasurableSpace S] [TopologicalSpace S] extends DynamicalSystem S (T := ℕ) where
  /-- The Markov Kernel: Time → State → Distribution over next states -/
  kernel : ℕ → Kernel S S
  /-- The evolution of a probability distribution over time. -/
  evolve_dist : Measure S → ℕ → Measure S
  -- (Axiom connecting evolve_dist to the repeated application of the kernel)
