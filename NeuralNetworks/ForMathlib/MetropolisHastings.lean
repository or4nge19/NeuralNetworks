import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib

--set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Measure Set ENNReal


/-- The Metropolis-Hastings algorithm is a Markov Chain Monte Carlo method for obtaining a sequence
of random samples from a probability distribution where direct sampling is difficult.

This file defines:
1. The acceptance probability function used in the algorithm
2. The Metropolis-Hastings kernel that defines one step of the algorithm
3. Various probability distributions used in MCMC sampling (uniform, normal)
4. Supporting infrastructure for working with PDFs and kernels

The file also includes theorems about measurability properties of the algorithm components,
as well as the equivalence between different formulations of the Metropolis-Hastings kernel.
-/


lemma ofReal_inv' (a : ℝ) (ha : 0 < a) :
  ENNReal.ofReal (a⁻¹) = ENNReal.ofReal 1 / ENNReal.ofReal a :=
by rw [← one_div]; exact ofReal_div_of_pos ha

namespace ProbabilityTheory

instance : MeasurableMul₂ ℝ := inferInstance
instance : MeasurableNeg ℝ := inferInstance
instance : MeasurableDiv₂ ℝ := inferInstance
instance : MeasurableSub₂ ℝ := inferInstance

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

instance kernelMeasurableSpace : MeasurableSpace (Kernel α β) := ⊤

class CastRealField (α : Type*) [LT α] where
  cast : α → ℝ
  map_lt : ∀ {a b : α}, a < b → cast a < cast b

instance realCastRealField : CastRealField ℝ where
  cast := id
  map_lt := fun {_ _} h => h

instance : OrderedRing ℝ := inferInstance

def RandomVariable (Ω : Type*) [MeasurableSpace Ω] (X : Type*) [MeasurableSpace X] :=
  Ω → X

class DiscreteDistribution (X : Type*) [MeasurableSpace X] [MeasurableSingletonClass X] where
  pmf : X → ℝ≥0∞
  isProbabilityMassFunction : (∑' x, pmf x) = 1

class ContinuousDistribution (X : Type*) [MeasurableSpace X] [MeasureSpace X] where
  pdf : X → ℝ≥0∞
  isProbabilityDensityFunction : (∫⁻ x, pdf x) = 1

class MarkovChain (X : Type*) [MeasurableSpace X] where
  transitionKernel : Kernel X X
  isMarkovKernel : IsMarkovKernel transitionKernel
  -- Add properties about the kernel's measurability and normalization here

/-- A measure `μ` is a stationary distribution for a kernel `κ` if, for all measurable
sets `s`, the integral of `κ a s` with respect to `a : α` distributed according to `μ`
is equal to `μ s`.  This is the standard definition of stationarity. -/
def isStationaryDistribution (κ : Kernel α α) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → ∫⁻ a, κ a s ∂μ = μ s

end ProbabilityTheory

open MeasureTheory ProbabilityTheory ENNReal Finset

namespace PMF

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]


-- Bernoulli Distribution (already largely defined in Constructions.lean)
-- We just need to show how to create a `Measure` from it.
-- The existing `PMF.bernoulli` is good. We'll add a convenience lemma.

/-- The measure associated with a Bernoulli PMF. -/
noncomputable def bernoulliMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : ℝ≥0∞) (h : p ≤ 1) (f : Bool → α) : Measure α :=
  (bernoulli p h).toMeasure.map f

-- Uniform Discrete Distribution (on a Finset)
section UniformDiscrete

variable (s : Finset α)

/-- Uniform distribution over a finite set `s`.  Assigns equal probability to each element
    of `s`. -/
noncomputable def uniformDiscrete [DecidableEq α] [h : Nonempty ↑s] : PMF α :=
  ofFinset (fun a => if a ∈ s then ((Finset.card s : ℝ≥0∞))⁻¹ else 0) s
    (by
      simp [Finset.sum_ite_mem]
      let ⟨x, hx⟩ := h
      have hs : s.Nonempty := ⟨x, hx⟩
      have hp := Finset.card_pos.2 hs
      field_simp [hp]
      have := ENNReal.div_self (show (Finset.card s : ENNReal) ≠ 0 from ne_of_gt (by exact_mod_cast hp))
      simp [hp] at this
      exact this)
    (by simp)

@[simp]
theorem uniformDiscrete_apply [DecidableEq α] [Nonempty ↑s] (a : α) :
    uniformDiscrete s a = if a ∈ s then (card s : ℝ≥0∞)⁻¹ else 0 := by
  simp [uniformDiscrete]

@[simp]
theorem support_uniformDiscrete [DecidableEq α] [Nonempty ↑s] :
    (uniformDiscrete s).support = (s : Set α) := by
  ext a
  simp [mem_support_iff]

instance isProbabilityMeasure_uniformDiscrete [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [TopologicalSpace α] [OpensMeasurableSpace α] [Nonempty (s : Set α)] [Nonempty s] :
    IsProbabilityMeasure (uniformDiscrete s).toMeasure :=
  inferInstance

/-- The measure associated with a uniform discrete PMF. -/
noncomputable def uniformDiscreteMeasure [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Finset α) [Nonempty (s : Set α)] [Nonempty s] : Measure α :=
  (uniformDiscrete s).toMeasure

end UniformDiscrete

end PMF

open MeasureTheory ProbabilityTheory ENNReal

instance measure_measurable_space (α : Type*) [MeasurableSpace α] : MeasurableSpace (Measure α) := ⊤

namespace ProbabilityTheory

section UniformContinuous

variable {α : Type*}
[MeasurableSpace α]  [LinearOrderedField α] [Zero α]
-- [TopologicalSpace α] [LinearOrder α]
 -- [OrderTopology α] [OrderClosedTopology α] [OpensMeasurableSpace α]

variable [CastRealField α]

/-- A continuous uniform distribution on the interval `[a, b]`. -/
noncomputable def uniformContinuousPdf {a b : α} [Zero α] (_ : a < b) : α → ℝ≥0∞ :=
  Set.indicator (Icc a b) (fun _ => ENNReal.ofReal (1/(CastRealField.cast b - CastRealField.cast a)))

lemma measurable_uniformContinuousPdf {a b : α} (h : a < b)
    [TopologicalSpace α]
    [OrderClosedTopology α] [OpensMeasurableSpace α] :
    Measurable (uniformContinuousPdf h) := by
  -- uniformContinuousPdf is an indicator function multiplied by a constant
  have h_indic : Measurable (Set.indicator (Icc a b) (fun _ => ENNReal.ofReal (1/(CastRealField.cast b - CastRealField.cast a)))) := by
    apply Measurable.indicator
    · exact measurable_const  -- The constant function is measurable
    · exact measurableSet_Icc   -- Intervals are measurable sets
  -- Since uniformContinuousPdf h is exactly this indicator function
  convert h_indic

/-- Given absolute continuity of μ with respect to ν, this definition provides the Lebesgue decomposition of μ. -/
def haveLebesgueDecomposition_of_absolutelyContinuous {α : Type*} [MeasurableSpace α]
  (μ ν : Measure α) (h : μ ≪ ν) : μ.HaveLebesgueDecomposition ν :=
  ⟨ (0, rnDeriv μ ν), (@measurable_rnDeriv α _ μ ν), MutuallySingular.zero_left, by
  simp_all only [zero_add]
  sorry⟩

/-- The uniform distribution on the interval [a, b]. -/
noncomputable def uniformContinuous (a b : α) (h : Fact (a < b)) [MeasureSpace α] (vol : Measure α) : Measure α :=
  vol.withDensity (uniformContinuousPdf h.out)

@[simp] lemma uniformContinuous_eq_withDensity (a b : α) (h : Fact (a < b)) [MeasureSpace α] (vol : Measure α)  :
  uniformContinuous a b h vol = vol.withDensity (uniformContinuousPdf h.out) := rfl

/-- A measure is restricted scalable on a set if it can be scaled by a constant factor on that set. -/
class RestrictedScalable (μ : Measure α) (s : Set α) : Prop where
  scale : ∀ (c : ℝ≥0∞), ∃ (ν : Measure α), ∀ (t : Set α), MeasurableSet t → ν (t ∩ s) = c • μ (t ∩ s)

instance isProbabilityMeasure_uniformContinuous (a b : α) (vol : Measure α)
    (h : Fact (a < b)) [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α] [MeasureSpace α] [BorelSpace α]
    [IsFiniteMeasure vol] [RestrictedScalable vol (Icc a b)]  :
    IsProbabilityMeasure (vol.withDensity (uniformContinuousPdf h.out)) := by
  constructor
  have hm : Measurable (uniformContinuousPdf h.out) :=
    measurable_uniformContinuousPdf h.out
  simp only [uniformContinuousPdf, Set.indicator_univ, MeasureTheory.Measure.restrict_univ]
  let delta := (CastRealField.cast b - CastRealField.cast a : ℝ)
  -- Explicitly compute the difference as a real number
  have : (∫⁻ (x : α), ENNReal.ofReal (delta)⁻¹ ∂vol) =
    (∫⁻ x in Icc a b, ENNReal.ofReal (delta)⁻¹ ∂vol) + ∫⁻ x in (Icc a b)ᶜ, ENNReal.ofReal (delta)⁻¹ ∂vol := by
    rw [lintegral_add_compl]
    exact measurableSet_Icc
  simp [uniformContinuousPdf]
  have : ENNReal.ofReal ((CastRealField.cast b - CastRealField.cast a)⁻¹) * vol (Icc a b) = 1 := by
    have h_scale := @RestrictedScalable.scale _ _ vol (Icc a b) _ 1
    obtain ⟨ν, hν⟩ := h_scale
    have h_icc := hν (Icc a b) measurableSet_Icc
    rw [Set.inter_self] at h_icc
    simp [← ENNReal.ofReal_one] at h_icc ⊢
    have h_eq : ENNReal.ofReal ((CastRealField.cast b - CastRealField.cast a)⁻¹) = (ENNReal.ofReal 1) / (vol (Icc a b)) := by
      have h_pos : 0 < (CastRealField.cast b - CastRealField.cast a : ℝ) := by
        have h_coe : (CastRealField.cast a) < (CastRealField.cast b) := CastRealField.map_lt h.out
        exact sub_pos.mpr h_coe

      have h_vol : vol (Set.Icc a b) = ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a) :=
        by
          obtain ⟨ν, hν⟩ := @RestrictedScalable.scale _ _ vol (Set.Icc a b) _ (1 : ℝ≥0∞)
          specialize hν (Set.Icc a b) measurableSet_Icc
          rw [Set.inter_self] at hν
          have h_one_smul : (1 : ℝ≥0∞) • vol (Set.Icc a b) = vol (Set.Icc a b) := one_smul _ _
          rw [h_one_smul] at hν
          have h_vol_eq := hν
          convert h_vol_eq.symm
          have h_vol_pos : 0 < CastRealField.cast b - CastRealField.cast a := by
            exact sub_pos.mpr (CastRealField.map_lt h.out)

          have h_ne_top : ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a) ≠ ⊤ := by exact ofReal_ne_top
          have h_vol_eq_sub : vol (Set.Icc a b) = ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a) := by
            have h_vol_real : vol (Set.Icc a b) = ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a) := by
                -- Use the RestrictedScalable instance to prove this
                have h_scale := @RestrictedScalable.scale _ _ vol (Set.Icc a b) _ (ENNReal.ofReal 1)
                obtain ⟨ν', hν'⟩ := h_scale
                have h_scale_set := hν' (Set.Icc a b) measurableSet_Icc
                rw [Set.inter_self] at h_scale_set

                -- Since vol(Icc a b) = Integral of 1 over Icc a b = b - a
                -- We need to relate this to our measure
                have h_one_smul_eq : (1 : ℝ≥0∞) • vol (Set.Icc a b) = vol (Set.Icc a b) := one_smul _ _
                rw [← h_one_smul_eq] at h_scale_set

                -- In a measure space where we have vol(Icc a b) = b - a
                -- This is a standard property of Lebesgue measure on interval
                have h_interval_measure : vol (Set.Icc a b) = ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a) := by
                  -- For the BorelSpace measure on an ordered field, the measure of an interval is its length
                  sorry -- This requires a detailed proof about the measure of intervals
                  -- The key insight is that vol(Icc a b) = b - a in appropriate spaces
                simp_all only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul,
                  one_mul, ofReal_one, sub_pos, ne_eq, ofReal_ne_top, not_false_eq_true, delta]
            exact h_vol_real
          simp_all only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul,
            one_mul, ofReal_one, sub_pos, ne_eq, ofReal_ne_top, not_false_eq_true, delta]
      have : ENNReal.ofReal (CastRealField.cast b - CastRealField.cast a)⁻¹ = (vol (Set.Icc a b))⁻¹ :=
        by
          rw [h_vol]
          exact ofReal_inv_of_pos h_pos

      have h_vol_pos : 0 < vol (Icc a b) := by
        rw [h_vol]
        exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (CastRealField.map_lt h.out))
      aesop
    rw [h_eq]
    have : ENNReal.ofReal 1 / vol (Icc a b) * vol (Icc a b) = ENNReal.ofReal 1 := by
      rw [ENNReal.div_mul_cancel]
      ·
        simp_all only [ofReal_one, one_div, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
          smul_eq_mul, one_mul, ne_eq, delta]
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        simp_all only [ENNReal.inv_zero, mul_zero, zero_add, ofReal_ne_top, delta]
      · exact measure_ne_top vol (Set.Icc a b)
    simp_all only [ofReal_one, one_div, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      smul_eq_mul, one_mul, delta]
  have hIcc : (∫⁻ x in Icc a b, ENNReal.ofReal delta⁻¹ ∂vol) = 1 := by
    rw [lintegral_const]
    simp_all only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, delta]
  have hIoc : (∫⁻ x in (Icc a b)ᶜ, ENNReal.ofReal (delta⁻¹) ∂vol) = 0 := by
    have h_meas_compl : MeasurableSet (Icc a b)ᶜ := MeasurableSet.compl measurableSet_Icc
    have h_indicator : ∀ x ∈ (Icc a b)ᶜ, uniformContinuousPdf h.out x = 0 := by
      intros x hx
      simp only [uniformContinuousPdf, Set.indicator_apply]
      by_cases h' : x ∈ Icc a b
      { exfalso; exact hx h' }
      { rw [if_neg h']
         }
    have h_indic_ae : ∀ᵐ x ∂(vol.restrict (Icc a b)ᶜ), uniformContinuousPdf h.out x = 0 := by
      apply ae_of_all
      intro x
      simp only [uniformContinuousPdf, Set.indicator_apply]
      by_cases hx : x ∈ Icc a b
      · rw [@ite_eq_iff']
        sorry
      · rw [if_neg hx]
    sorry
  simp_all only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, mul_eq_zero,
    ofReal_eq_zero, inv_nonpos, tsub_le_iff_right, zero_add, delta]

variable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → α) (P : Measure Ω)
  (a b : α) [Fact (a < b)] [MeasureSpace α] [MeasureSpace Ω]


-- Add necessary conditions for HasPDF
variable [UniformSpace α] [CompleteSpace α] [MetricSpace α]

noncomputable
instance decidableRelativelySingular (μ : Measure α) (ν : Measure α) : Decidable (μ ⟂ₘ ν) := Classical.propDecidable (μ ⟂ₘ ν)

class HasPDF {E : Type*} [MeasurableSpace E] (X : Ω → E) (P : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  aemeasurable' : AEMeasurable X P
  haveLebesgueDecomposition' : (map X P).HaveLebesgueDecomposition μ
  absolutelyContinuous' : map X P ≪ μ

theorem hasPDF_of_uniformContinuousPdf
    [MeasurableSpace α] [TopologicalSpace α] [MeasureSpace α]
    [OpensMeasurableSpace α] [MeasureSpace Ω] [OrderClosedTopology α]
    [Zero α]
    (volume : Measure α) (hX : AEMeasurable X P)
    (hac : Measure.map X P ≪ volume)
    (h : pdf X P volume =ᵐ[volume] uniformContinuousPdf (‹Fact (a < b)›).out) :
    HasPDF X P volume := by

  have hmeas : Measurable (uniformContinuousPdf (‹Fact (a < b)›).out) :=
    measurable_uniformContinuousPdf (‹Fact (a < b)›).out
  have haemeas : AEMeasurable (uniformContinuousPdf (‹Fact (a < b)›).out) volume := hmeas.aemeasurable

  -- The key insight is that we need to establish the Lebesgue decomposition
  -- of Measure.map X P with respect to volume

  exact { aemeasurable' := hX,
          haveLebesgueDecomposition' := by
            refine ⟨(⟨0, uniformContinuousPdf (‹Fact (a < b)›).out⟩ : Measure α × (α → ℝ≥0∞)), ?_⟩
            constructor
            · -- Prove the density is measurable
              exact hmeas
            · -- Show the absolutely continuous part
              constructor
              · -- Since map X P ≪ volume (by hac), the discrete part must be zero
                -- The first component of our Lebesgue decomposition is the discrete part
                -- Since the measure is absolutely continuous, this part must be the zero measure
                -- The zero measure and volume are mutually singular
                exact MutuallySingular.zero_left

              · -- The measure equals the density integrated against volume
                -- We need to show that Measure.map X P = (Measure.map X P, uniformContinuousPdf ⋯).1 + volume.withDensity (Measure.map X P, uniformContinuousPdf ⋯).2
                -- Since the first component (discrete part) is 0, we need to show:
                -- Measure.map X P = volume.withDensity (uniformContinuousPdf (‹Fact (a < b)›).out)

                -- First, by Radon-Nikodym, we know:
                haveI : (Measure.map X P).HaveLebesgueDecomposition volume :=
                  haveLebesgueDecomposition_of_absolutelyContinuous (Measure.map X P) volume hac
                have h_rn : Measure.map X P = volume.withDensity (rnDeriv (Measure.map X P) volume) :=
                        by exact Eq.symm (Measure.withDensity_rnDeriv_eq (Measure.map X P) volume hac)

                -- Since pdf X P volume =ᵐ[volume] uniformContinuousPdf (‹Fact (a < b)›).out by hypothesis h
                -- We can use withDensity_congr_ae to show they generate the same measure
                have h_pd_eq : volume.withDensity (pdf X P volume) = volume.withDensity (uniformContinuousPdf (‹Fact (a < b)›).out) :=
                  withDensity_congr_ae h

                -- We need to establish that the measure has a Lebesgue decomposition
                haveI : (Measure.map X P).HaveLebesgueDecomposition volume :=
                  haveLebesgueDecomposition_of_absolutelyContinuous (Measure.map X P) volume hac

                -- Combining these results:
                rw [h_rn]

                -- Since the first component is 0, we have:
                rw [h_rn]
                simp only [zero_add]
                rw [← h_rn]
                exact withDensity_congr_ae h
          absolutelyContinuous' := hac }

end UniformContinuous

end ProbabilityTheory

open MeasureTheory ProbabilityTheory ENNReal Real

namespace ProbabilityTheory


/-- Probability density function of the normal distribution -/
noncomputable def normalPdf (μ σ : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((σ * Real.sqrt (2 * π))⁻¹ * Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2)))

lemma measurable_normalPdf (μ σ : ℝ) [TopologicalSpace ℝ] [BorelSpace ℝ] [Fact (0 < σ)] : Measurable (normalPdf μ σ) :=
by
  unfold normalPdf
  -- Prove that the inner function is nonnegative.
  have h_nonneg : ∀ x, (σ * Real.sqrt (2 * π))⁻¹ * Real.exp (-(x - μ)^2 / (2 * σ^2)) ≥ 0 :=
    λ x => by
      apply mul_nonneg
      · have h1 : 0 < σ := ‹Fact (0 < σ)›.out
        have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (mul_pos two_pos pi_pos)
        exact inv_nonneg.2 (mul_nonneg (le_of_lt h1) (le_of_lt h2))
      · exact le_of_lt (Real.exp_pos _)

  -- The function is the composition of ENNReal.ofReal with a real-valued function
  apply Measurable.comp (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)

  -- Show that the real-valued part is measurable
  apply Measurable.mul
  · -- Constant part is measurable
    exact measurable_const
  · -- Exponential part is measurable
    refine Measurable.exp ?_
    -- We need to rewrite as -(something) / constant
    apply Measurable.div
    · -- Negative of numerator (x - μ)²
      apply Measurable.neg
      apply Measurable.pow
      · apply Measurable.sub
        · exact measurable_id
        · exact measurable_const
      · exact measurable_const
    · exact measurable_const

/-- The standard normal measure -/
noncomputable def normalMeasure (μ σ : ℝ) : Measure ℝ :=
  volume.withDensity (normalPdf μ σ)

instance normal_isProbabilityMeasure (μ σ : ℝ) [Fact (0 < σ)]  :
    IsProbabilityMeasure (normalMeasure μ σ) := by
  constructor
  let C := (σ * Real.sqrt (2 * π))⁻¹
  have hC_pos : 0 < C := by
    have h1 : 0 < σ := ‹Fact (0 < σ)›.out
    have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (mul_pos two_pos pi_pos)
    have h3 : 0 < σ * Real.sqrt (2 * π) := mul_pos h1 h2
    have h4 := ENNReal.ofReal_pos.2 h3
    have h4_ne_top : ENNReal.ofReal (σ * Real.sqrt (2 * π)) ≠ ⊤ := ENNReal.ofReal_ne_top
    exact inv_pos_of_pos h3
  have i : ∫⁻ x, normalPdf μ σ x = ∫⁻ x, ENNReal.ofReal (C * Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))) := by rfl
  have h_int : ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))) = ENNReal.ofReal (Real.sqrt (2 * π) * σ) := by
    -- This is a standard result about the normal distribution: ∫ e^(-(x-μ)²/(2σ²)) dx = σ√(2π)
    -- We use the known result that ∫ e^(-x²/2) dx = √(2π)
    -- With the substitution u = (x-μ)/(σ√2), we get dx = σ√2 du
    -- The integral becomes σ√2 ∫ e^(-u²) du = σ√2 · √π = σ√(2π)
    have h_change_var : ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ)^2 / (2 * σ^2))) =
                        ENNReal.ofReal σ * ∫⁻ u, ENNReal.ofReal (Real.exp (-u^2)) := by
      -- By change of variables theorem with u = (x-μ)/(σ√2)
      -- The Jacobian determinant is σ
      have h_meas : Measurable (fun x => Real.exp (-(x - μ)^2 / (2 * σ^2))) := by
        apply Measurable.exp
        apply Measurable.div
        · apply Measurable.neg
          apply Measurable.pow
          · apply Measurable.sub
            · exact measurable_id
            · exact measurable_const
          · exact measurable_const
        · exact measurable_const

      have h_subst : ∀ x, Real.exp (-(x - μ)^2 / (2 * σ^2)) =
                          Real.exp (-((x - μ)/(σ * Real.sqrt 2))^2) := by
        intro x
        -- Instead of using exp_neg which isn't working as expected,
        -- we can directly show the equality of the exponents
        have h_exp_eq : -(x - μ)^2 / (2 * σ^2) = -(((x - μ)/(σ * Real.sqrt 2))^2) := by
          field_simp [‹Fact (0 < σ)›.out]
          ring_nf
          have h_sqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
          -- Directly simplify the algebraic expression
          simp only [pow_two]
          field_simp [‹Fact (0 < σ)›.out, h_sqrt]
          ring
        rw [h_exp_eq]
        -- Show that (x - μ)^2 / (2 * σ^2) = ((x - μ)/(σ * √2))^2

      have h_eq : ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ)^2 / (2 * σ^2))) =
                  ENNReal.ofReal σ * ∫⁻ u, ENNReal.ofReal (Real.exp (-u^2)) := by
        -- For change of variables, we need to use lintegral_map with the substitution u = (x-μ)/(σ√2)
        -- This is equivalent to x = μ + u·σ√2, with dx = σ√2 du
        let f := fun u => u * σ * Real.sqrt 2
        have h_deriv : ∀ u, HasDerivAt f (σ * Real.sqrt 2) u := fun u =>
          by
            simp [f]
            have h_linear : HasDerivAt (fun u => (u * σ) * Real.sqrt 2) (σ * Real.sqrt 2) u :=
              by
                have h_mul_σ : HasDerivAt (fun y => y * σ) σ u := by exact hasDerivAt_mul_const σ
                exact HasDerivAt.mul_const h_mul_σ √2
            exact h_linear

        have h_meas : Measurable f := by
          apply Measurable.mul
          · exact MeasurableSMul.measurable_smul_const σ  -- for u
          · exact measurable_const  -- for (σ * √2)

        -- This change of variables transforms the integral
        sorry  -- Complete proof would use lintegral_map with appropriate Jacobian factor
      aesop
    have h_gaussian_integral : ∫⁻ u, ENNReal.ofReal (Real.exp (-u^2)) = ENNReal.ofReal (Real.sqrt π) := by
      -- This is the standard Gaussian integral result: ∫ e^(-u²) du = √π
      dsimp only
      sorry
    rw [h_change_var, h_gaussian_integral]
    rw [← ENNReal.ofReal_mul]
    · simp [Real.sqrt_mul]
      rw [mul_comm σ]; rw [@NonUnitalRing.mul_assoc]
      sorry
    · sorry
  have h_eq : ∫⁻ x, ENNReal.ofReal (C * Real.exp (-(x - μ)^2 / (2 * σ^2))) =
              ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ)^2 / (2 * σ^2))) := by
    have h_nonneg : 0 ≤ C := le_of_lt hC_pos
    have h_exp_pos : ∀ x, 0 ≤ Real.exp (-(x - μ)^2 / (2 * σ^2)) := fun x => le_of_lt (Real.exp_pos _)
    rw [lintegral_congr_ae]
    refine lintegral_const_mul (ENNReal.ofReal C)
      (by { apply Measurable.comp
            { exact measurable_coe_nnreal_ennreal }
            { refine Measurable.real_toNNReal ?_
              refine Measurable.exp ?_
              · refine Measurable.div ?_ ?_
                · refine Measurable.neg ?_
                  refine Measurable.pow ?_ ?_
                  · exact Measurable.add_const (fun ⦃t⦄ a ↦ a) (-μ)
                  · exact measurable_const
                · exact measurable_const } })
    sorry

  suffices h : normalMeasure μ σ Set.univ = ∫⁻ x, normalPdf μ σ x ∂volume from by
    rw [h]
    rw [i]
    have : ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ)^2 / (2 * σ^2))) = 1 := by
      rw [h_int]
      rw [← ENNReal.ofReal_mul]
      · simp [C]
        have h_pos : 0 < σ * Real.sqrt (2 * π) := mul_pos ‹Fact (0 < σ)›.out (Real.sqrt_pos.2 (mul_pos two_pos pi_pos))
        field_simp [h_pos]
        have h1 : √2 * √π * σ / (√π * √2 * σ) = 1 := by
          ring_nf
          rw [mul_assoc, mul_assoc]
          have h_rewrite : √2 * √π * σ * (√2)⁻¹ * (√π)⁻¹ * σ⁻¹ = (√2 * (√2)⁻¹) * (√π * (√π)⁻¹) * (σ * σ⁻¹) := by ring
          have h_assoc : √2 * √π * σ * ((√2)⁻¹ * ((√π)⁻¹ * σ⁻¹)) = √2 * √π * σ * (√2)⁻¹ * (√π)⁻¹ * σ⁻¹ := by ring
          rw [h_assoc]
          rw [h_rewrite]
          have h_ne_zero₁ : √2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 two_pos)
          have h_ne_zero₂ : √π ≠ 0 := ne_of_gt (Real.sqrt_pos.2 pi_pos)
          have h_ne_zero₃ : σ ≠ 0 := ne_of_gt ‹Fact (0 < σ)›.out
          have h1 : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 := by
            apply div_self
            exact h_ne_zero₁
          have h2 : √π * (√π)⁻¹ = 1 := by apply div_self; exact h_ne_zero₂
          have h3 : σ * σ⁻¹ = 1 := by apply div_self; exact h_ne_zero₃
          rw [h1, h2, h3]
          repeat rw [mul_one]
        exact h1
      · have h_exp_nonneg : 0 ≤ Real.exp (-(0 : ℝ)^2 / (2 * σ^2)) := by
          exact le_of_lt (Real.exp_pos _)
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (2 * π) := le_of_lt (Real.sqrt_pos.2 (mul_pos two_pos pi_pos))
        have h_mul_nonneg : 0 ≤ Real.sqrt (2 * π) * σ := mul_nonneg h_sqrt_nonneg (le_of_lt ‹Fact (0 < σ)›.out)
        exact le_of_lt hC_pos
    rw [h_eq]
    exact this
  rw [lintegral_congr_ae (ae_eq_refl _)]
  rw [normalMeasure, withDensity]
  --simp only [measure_univ]
  have h_int : ∫⁻ x, ENNReal.ofReal (Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))) = ENNReal.ofReal (Real.sqrt (2 * π) * σ) := by
    sorry -- this is a well-known fact about the normal distribution that needs to be proved separately
  simp only [i]
  have h_eq : ∫⁻ (x : ℝ), ENNReal.ofReal (C * Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))) =
              ENNReal.ofReal C * ∫⁻ (x : ℝ), ENNReal.ofReal (Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2))) := by
    have h_nonneg : ∀ x, 0 ≤ Real.exp (-(x - μ) ^ 2 / (2 * σ ^ 2)) := fun x => le_of_lt (Real.exp_pos _)
    have h_C_nonneg : 0 ≤ C := le_of_lt hC_pos
    rw [h_eq]
  rw [h_eq]
  rw [h_int]
  rw [mul_comm]
  have : C * (Real.sqrt (2 * π) * σ) = 1 := by
    field_simp [C]
    have h1 : 0 < σ := ‹Fact (0 < σ)›.out
    have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (mul_pos two_pos pi_pos)
    have h3 : 0 < σ * Real.sqrt (2 * π) := mul_pos h1 h2
    rw [@mul_div_mul_comm]
    sorry
  have : ENNReal.ofReal (√(2 * π) * σ) * ENNReal.ofReal C = 1 := by
    rw [← ENNReal.ofReal_mul]
    · have h_comm : √(2 * π) * σ * C = C * (√(2 * π) * σ) := by ring
      rw [h_comm, this, ENNReal.ofReal_one]
    · have h1 : 0 ≤ √(2 * π) * σ := mul_nonneg
        (Real.sqrt_nonneg _)
        (le_of_lt ‹Fact (0 < σ)›.out)
      exact h1
  simp [this]
  sorry

variable (α β : Type*)

/-- A random variable `X` has a normal distribution with parameters `μ` and `σ`
if its probability density function is `normalPdf μ σ`. -/
theorem hasPDF_normal {Ω : Type*} [TopologicalSpace α]  [MeasurableSpace Ω] {X : Ω → ℝ} {P : Measure Ω} {μ σ : ℝ}
    (hX : AEMeasurable X P) (hσ : Fact (0 < σ)) :
    HasPDF X P (by volume_tac) := by
  let volume := StieltjesFunction.id.measure
  have hmeas : Measurable (normalPdf μ σ) := measurable_normalPdf μ σ
  have h_pdf : pdf X P =ᵐ[volume] normalPdf μ σ := sorry  -- Need to prove this
  have h_measure_eq : Measure.map X P = withDensity volume (normalPdf μ σ) := by
    have h_wd := withDensity_congr_ae h_pdf
    have h_map : Measure.map X P = withDensity volume (pdf X P) := by sorry -- Use measure_map_eq_withDensity
    rw [h_map]
    exact h_wd
  exact { aemeasurable' := hX,
          haveLebesgueDecomposition' := by
            refine ⟨(⟨0, normalPdf μ σ⟩ : Measure ℝ × (ℝ → ℝ≥0∞)), ?_⟩
            constructor
            · exact hmeas
            · constructor
              · exact MutuallySingular.zero_left
              · simp [h_measure_eq]; sorry
          absolutelyContinuous' := by
            rw [h_measure_eq]
            sorry }

end ProbabilityTheory



open MeasureTheory ProbabilityTheory Measure Set ENNReal

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasureSpace α]

open MeasureTheory ProbabilityTheory Measure Set ENNReal


instance : MeasurableSpace (Kernel α β) := ⊤


lemma isStationaryDistribution_of_compProd_left {γ : Type*} [MeasurableSpace γ]
    (κ : Kernel α α) (η : Kernel (α × α) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (μ : Measure α)
    (h : (κ ⊗ₖ η) ∘ₘ μ = (Kernel.id ⊗ₖ η) ∘ₘ μ) :
    isStationaryDistribution κ μ := by
  intro s hs
  -- Using the definition of kernel composition, we have that
  -- ∫⁻ a, (κ a) s ∂μ = μ s.
  have h' : ∫⁻ a, (κ a) s ∂μ = μ s :=
  by
    sorry
  exact h'

end ProbabilityTheory



open MeasureTheory ProbabilityTheory ENNReal

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- The acceptance probability for the Metropolis-Hastings algorithm.

   - `π` is the target distribution (represented as a measure).  We assume it has a
     density with respect to some base measure (typically Lebesgue or counting measure).
   - `q` is the proposal kernel. `q x` is a kernel representing the distribution of
     proposed moves *given* that the current state is `x`.
   - `x` is the current state.
   - `y` is the proposed next state.

   Returns the acceptance probability as an `ℝ≥0∞` value.
-/
noncomputable
def metropolisHastingsAcceptance
    (pdf : α → ℝ≥0∞) [MeasurableSingletonClass α]
    (q : Kernel α α) (x y : α) : ℝ≥0∞ :=
  min 1 (pdf y * (q y) (Set.singleton y) / (pdf x * (q x) (Set.singleton x)))

instance : MeasurableSpace ℝ := inferInstanceAs (MeasurableSpace ℝ)


noncomputable
def Kernel.prodMk (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasureSpace α] [MeasureSpace β] (ν : Measure β) : Kernel α (α × β) :=
{ toFun := fun a => MeasureTheory.Measure.prod (MeasureTheory.Measure.dirac a) (ν),
  measurable' := sorry }

/-- The Metropolis-Hastings kernel.

   - `π` is the target distribution, which must have a PDF with respect to itself.
   - `q` is the proposal kernel.

   Returns a `Kernel α α` representing one step of the Metropolis-Hastings algorithm.
-/

lemma measurable_metropolisHastingsAcceptance
    (pdf : α → ℝ≥0∞) [MeasurableSingletonClass α]
    (q : Kernel α α) (x : α) (hpdf : Measurable pdf) (hq : Measurable q) :
    Measurable (fun y => metropolisHastingsAcceptance pdf q x y) := by
  -- First, we decompose the acceptance function
  have h_ratio : Measurable (fun y => pdf y * (q y) (Set.singleton y) / (pdf x * (q x) (Set.singleton x))) := by
    -- The denominator is constant with respect to y

    have h_denom : Measurable (fun (_ : α) => pdf x * (q x) (Set.singleton x)) := measurable_const
    -- For the numerator, we need measurability of each term
    have h_pdf_y : Measurable (fun y => pdf y) := hpdf

    -- This part is tricky: we need measurability of y ↦ q y (singleton y)
    have h_q_y : Measurable (fun y => (q y) (Set.singleton y)) := by
      -- The function y ↦ q y (singleton y) is measurable because q is a measurable kernel
      sorry  -- This requires additional theorems about kernel measurability

    -- Combine the numerator terms
    have h_num : Measurable (fun y => pdf y * (q y) (Set.singleton y)) :=
      Measurable.mul h_pdf_y h_q_y

    -- Division by a non-zero constant preserves measurability
    exact Measurable.div h_num h_denom

  -- Finally, min is measurable when its arguments are
  have h_one : Measurable (fun (x : α) => (1 : ℝ≥0∞)) := measurable_const

  exact Measurable.min h_one h_ratio

noncomputable
def metropolisHastingsKernel' (pi : Measure α) [hπ : HasPDF (id : α → α) pi pi] [StandardBorelSpace α]
    [Nonempty α] [MeasurableSingletonClass α] (q : Kernel α α)
    [IsSFiniteKernel q] : Kernel α α :=
  { toFun := fun x =>
      let pdf := pdf (id : α → α) pi pi
      let acceptRate : α → ℝ≥0∞ := fun y =>
        min 1 (metropolisHastingsAcceptance pdf q x y)
      Measure.withDensity (q x) acceptRate,
    measurable' := by
      apply measurable_of_measurable_coe
      intro s hs
      -- We need to show that x ↦ (metropolisHastingsKernel pi q) x s is measurable
      -- This involves proving that x ↦ Measure.withDensity (q x) acceptRate s is measurable

      -- First, establish measurability of the pdf
      have h_pdf_meas : Measurable (pdf (id : α → α) pi pi) := by
        -- This follows from the HasPDF assumption
        exact measurable_pdf id pi pi

      -- For each fixed s, we need to prove that x ↦ (q x) s is measurable
      have h_q_meas : Measurable (fun x => q x s) := by
        -- This comes from the measurability of the kernel q
        -- A kernel is measurable means exactly that for any measurable set s,
        -- the function x ↦ q x s is measurable
        exact Kernel.measurable_coe q hs

      -- Next, we need measurability of the acceptance rate function
      have h_accept_meas : Measurable (fun x => fun y =>
        min 1 (metropolisHastingsAcceptance (pdf (id : α → α) pi pi) q x y)) := by
        sorry -- Use measurable_metropolisHastingsAcceptance

      -- Finally, combine these to show measurability of the withDensity measure applied to s
      sorry -- This requires careful application of measurability of parametrized integrals
  }


variable {α : Type*} [MeasurableSpace α]
  [Nonempty α] [MeasurableSingletonClass α]

/-- The usual Metropolis--Hastings acceptance probability. -/
noncomputable
def metropolisHastingsAcceptance' (pdf : α → ℝ≥0∞) (q : Kernel α α)
  (x y : α) : ℝ≥0∞ :=
  let num := pdf y * (q y) (singleton y)
  let den := pdf x * (q x) (singleton x)
  min 1 (num / den)

/-- Measurability of the acceptance function as a function of `y`. -/
lemma measurable_metropolisHastingsAcceptance'
  {pdf : α → ℝ≥0∞} (hpdf : Measurable pdf)
  {q : Kernel α α} (hq : ∀ (x : α), Measurable (λ y => (q y) (singleton y)))
  (x : α) :
  Measurable (λ y => metropolisHastingsAcceptance pdf q x y) :=
by
  -- We show that `y ↦ pdf y * (q y) {y}` is measurable, etc.
  let denom := pdf x * (q x) (singleton x)  -- constant in y
  have h_const : Measurable (λ _ : α => denom) := measurable_const
  have h_num : Measurable (λ y => pdf y * (q y) (singleton y))
  { refine Measurable.mul hpdf (hq x)
    -- Using hq x which gives us measurability for the function at point x
  }
  have h_ratio : Measurable (λ y=> (pdf y * (q y) (singleton y)) / denom) :=
    Measurable.div h_num h_const
  -- then `min 1 (...)` is also measurable:
  exact Measurable.min measurable_const h_ratio


/-- One-step Metropolis--Hastings kernel. -/
noncomputable
def metropolisHastingsKernel
  (pi : Measure α) [HasPDF (id : α → α) pi pi]
  (q : Kernel α α)
  : Kernel α α :=
{ toFun := λ x =>
    let f : α → ℝ≥0∞ := λ y => metropolisHastingsAcceptance (pdf id pi pi) q x y
    -- withDensity from the measure (q x)
    (q x).withDensity f,
  measurable' :=
  by
    -- Outline: show x ↦ (q x).withDensity f is measurable in x
    -- requires standard “kernel is measurable in x, withDensity measurable, etc.”
    sorry
   }



theorem metropolisHastingsKernel_apply [StandardBorelSpace α] [MeasurableSingletonClass α] [Nonempty α]
    {pi : Measure α} [HasPDF (id : α → α) pi pi]
    {q : Kernel α α} [IsSFiniteKernel q] {x : α} {s : Set α}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    (metropolisHastingsKernel pi q) x s =
      ∫⁻ y in s, metropolisHastingsAcceptance (pdf (id : α → α) pi pi) q x y ∂(q x) := by
    sorry -- TODO: Should follow from a careful rewriting of all the pieces

end ProbabilityTheory

#min_imports
