import NeuralNetworks.Hopfield.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

open Finset BigOperators

infixl:70 " \\ " => Finset.sdiff

/-- Sum over universal set equals sum over all finite indices.
    Essential for Hopfield network energy calculations where we sum over all neurons. -/
@[simp]
lemma Finset.sum_univ {α : Type*} {β : Type*} [AddCommMonoid β] [Fintype α]
  (f : α → β) :
  ∑ x ∈ univ, f x = ∑ x, f x := by
  apply Finset.sum_congr
  · exact Finset.eq_univ_iff_forall.2 (fun x => Finset.mem_univ x)
  · intro x _
    rfl

  /-- Sum over universe with predicate equals single value.
    Essential for Hopfield energy calculations with single neuron terms:
    ∑_{x ∈ univ} (if x = i then f(i) else 0) = f(i) -/
@[simp]
lemma Finset.sum_univ_single {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} [AddCommMonoid β]
  (i : α) (f : α → β) :
  ∑ x ∈ univ, (if x = i then f i else 0) = f i := by
  rw [Finset.sum_univ]
  aesop

/-- For finite type sum, if only one element gives non-zero value,
    sum equals that single value. Essential for Hopfield network energy terms.

    If ∀ j ≠ i, f(j) = 0, then ∑ x, f(x) = f(i) -/
@[simp]
lemma Fintype.sum_eq_single_of_ne_zero {α : Type*} [Fintype α] {β : Type*}
  [AddCommMonoid β] (i : α) (f : α → β) (h : ∀ j, j ≠ i → f j = 0) :
  ∑ x, f x = f i := by
  apply Finset.sum_eq_single i
  · intro j _ hj
    exact h j hj
  · aesop

/-- Split sum into filtered and remaining parts:
    ∑_{x ∈ s} f(x) = ∑_{x ∈ s, p(x)} f(x) + ∑_{x ∈ s, ¬p(x)} f(x)
    Essential for Hopfield network energy decomposition. -/
@[simp]
lemma Finset.sum_eq_add_sum_filter {α : Type*} {β : Type*} [AddCommMonoid β] [DecidableEq α]
  {s : Finset α} (f : α → β) (p : α → Prop) [DecidablePred p] :
  ∑ x ∈ s, f x = ∑ x ∈ (s.filter p), f x + ∑ x ∈ (s.filter (fun x => ¬ p x)), f x := by
  apply Eq.symm
  rw [← Finset.sum_union]
  { congr
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto }
  { simp only [Finset.disjoint_filter]
    intro x _ h₁ h₂
    aesop
}

/-- Insert element into finite set, handling both cases:
    - If element exists, set unchanged
    - If new element, adds to set
    Essential for Hopfield network node operations. -/
@[simp]
lemma Finset.insert_eq' {α : Type*} [DecidableEq α] (a : α) (s : Finset α) :
  insert a s = if a ∈ s then s else {a} ∪ s := by
  by_cases h : a ∈ s
  · rw [if_pos h]
    exact Finset.insert_eq_of_mem h
  · rw [if_neg h]
    aesop

/- Insert an element into a finite set.
    Essential for Hopfield network set operations.
    Returns a new set containing the element and all original elements. -/
--def Finset.insert {α : Type*} [DecidableEq α] (a : α) (s : Finset α) : Finset α :=
--  if a ∈ s then s else {a} ∪ s

/-- Properties of insert:
    1. a ∈ insert a s
    2. x ∈ s → x ∈ insert a s
    3. x ∈ insert a s → x = a ∨ x ∈ s -/
@[simp]
theorem Finset.mem_insert' {α : Type*} [DecidableEq α] {a x : α} {s : Finset α} :
  x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  simp
  aesop

/-- Insert followed by difference with singleton:
    (insert a s) \ {a} = s \ {a}
    Essential for Hopfield network set manipulations. -/
@[simp]
lemma Finset.insert_diff_singleton {α : Type*} [DecidableEq α]
  (a : α) (s : Finset α) :
  (insert a s) \ {a} = s \ {a} := by
  ext x
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · intro h
    cases' h with _ h₂
    aesop
  · intro h
    cases' h with h₁ h₂
    exact ⟨Or.inr h₁, h₂⟩

/-- Set difference with empty set equals the original set:-/
@[simp]
lemma Finset.diff_empty {α : Type*} [DecidableEq α] (s : Finset α) :
  s \ ∅ = s := by
  ext x
  aesop

/-- Split sum into parts using set difference:
    ∑_{x ∈ s} f(x) = ∑_{x ∈ t} f(x) + ∑_{x ∈ s\t} f(x)
    Essential for Hopfield network energy calculations. -/
@[simp]
lemma Finset.sum_add_sum_diff {α : Type*} [DecidableEq α] [Fintype α] {β : Type*} [AddCommMonoid β]
  {s t : Finset α} (f : α → β) :
  ∑ x ∈ s, f x = ∑ x ∈ (t ∩ s), f x + ∑ x ∈ (s \ t), f x := by
  rw [← Finset.sum_union]
  · congr
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  · rw [Finset.disjoint_iff_ne]
    intro y hy z hz
    intro eq
    rw [← eq] at hz
    simp at hy
    aesop

/- Create singleton finite set {a}.
    Essential for single neuron operations in Hopfield networks. -/
--def Finset.singleton {α : Type*} (a : α) : Finset α := {a}

/-- Membership in singleton set:
    x ∈ {a} ↔ x = a -/
@[simp]
theorem Finset.mem_singleton' {α : Type*} [DecidableEq α] {a x : α} :
  x ∈ (singleton a : Finset α) ↔ x = a := by
  simp

/-- Sum distributes over subtraction:
    ∑ x, (f(x) - g(x)) = (∑ x, f(x)) - (∑ x, g(x))
    Essential for Hopfield energy difference calculations. -/
@[simp]
lemma Fintype.sum_sub_distrib {α : Type*} {β : Type*} [Fintype α] [AddCommGroup β]
  (f g : α → β) :
  ∑ x, (f x - g x) = (∑ x, f x) - (∑ x, g x) := by
  simp only [sub_eq_add_neg]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_neg_distrib]

/-- Create singleton finite set {a}.
    Essential for single neuron operations in Hopfield networks. -/
def Finset.singleton {α : Type*} (a : α) : Finset α := {a}

/-- Membership in singleton set: x ∈ {a} ↔ x = a -/
@[simp]
theorem Finset.mem_singleton'' {α : Type*} {a x : α} :
  x ∈ singleton a ↔ x = a := by
  unfold singleton
  simp only [mem_singleton]

/-- Card of singleton is 1 -/
@[simp]
theorem Finset.card_singleton' {α : Type*} (a : α) :
  (singleton a).card = 1 := by
  unfold singleton
  simp only [card_singleton]

/-- Split sum into intersection and difference parts:
    ∑_{x ∈ s} f(x) = ∑_{x ∈ s∩t} f(x) + ∑_{x ∈ s\t} f(x)
    Essential for Hopfield network energy decomposition. -/
@[simp]
lemma Finset.sum_eq_add_sum_diff {α : Type*} [DecidableEq α] {β : Type*} [AddCommMonoid β]
  {s t : Finset α} (f : α → β) :
  ∑ x ∈ s, f x = ∑ x ∈ (s ∩ t), f x + ∑ x ∈ (s\t), f x := by
  rw [← Finset.sum_union]
  · congr
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    apply Iff.intro
    · intro h
      by_cases ht : x ∈ t
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ⟨h, ht⟩
    · intro h
      cases h with
      | inl h => exact h.1
      | inr h => exact h.1
  · apply Disjoint.symm
    exact disjoint_sdiff_inter s t

/-- Sets are equal if one is subset of other and they have same cardinality:
    If s ⊆ t and |s| = |t| then s = t
    Essential for Hopfield network state space equivalence. -/
@[simp]
lemma Finset.eq_of_subset_of_card {α : Type*} {s t : Finset α}
  (h_sub : s ⊆ t) (h_card : s.card = t.card) : s = t := by
  apply Finset.ext
  intro x
  constructor
  · exact fun h => h_sub h
  · intro h
    by_contra h'
    have : s.card < t.card := Finset.card_lt_card ⟨h_sub, fun h_sub' => h' (h_sub' h)⟩
    linarith

/-- Cardinality inequality via subset:
    If s ⊆ t then |s| ≤ |t|
    Essential for Hopfield network state space analysis. -/
@[simp]
lemma Finset.card_le_of_subset {α : Type*} [DecidableEq α] {s t : Finset α}
  (h : s ⊆ t) : s.card ≤ t.card := by
  induction s using Finset.induction with
  | empty =>
    simp only [card_empty]
    exact Nat.zero_le _
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_not_mem ha]
    by_cases h' : a ∈ t
    · have : s ⊆ t := fun x hx => h (Finset.mem_insert_of_mem hx)
      have h_le := ih this
      rw [Nat.succ_le_iff]
      have : s.card < t.card := by
        apply Nat.lt_of_le_of_ne h_le
        intro h_eq
        have st : s ⊆ t := fun x hx => h (Finset.mem_insert_of_mem hx)
        have : s = t := Finset.eq_of_subset_of_card st h_eq
        exact ha (this ▸ h')
      exact this
    · exfalso
      exact h' (h (Finset.mem_insert_self a s))

/-- Cardinality of image equals source set cardinality under injection:
    If f is injective on s, then |f[s]| = |s|
    Essential for Hopfield network state space mappings. -/
@[simp]
lemma Finset.card_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
  {s : Finset α} (f : α → β)
  (h_inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) :
  (Finset.image f s).card = s.card := by
  induction s using Finset.induction with
  | empty => simp only [image_empty, card_empty]
  | @insert a s h_not_mem h_ih =>
    rw [image_insert, card_insert_of_not_mem]
    · have h_inj_s : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ := fun x₁ h₁ x₂ h₂ =>
        h_inj x₁ (Finset.mem_insert_of_mem h₁) x₂ (Finset.mem_insert_of_mem h₂)
      rw [h_ih h_inj_s]
      rw [card_insert_of_not_mem h_not_mem]
    · intro h
      simp only [mem_image] at h
      obtain ⟨x, hx, hf⟩ := h
      have : a ∈ s := by
        have : x = a := h_inj x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s) hf
        rw [this] at hx
        exact hx
      exact h_not_mem this

/-- Cardinality inequality via mapping:
    If f maps s into t, then |s| ≤ |t|
    Essential for Hopfield network state space analysis. -/
@[simp]
lemma Finset.card_le_card_of_maps_to {α β : Type*} [DecidableEq α] [DecidableEq β]
  {s : Finset α} {t : Finset β} (f : α → β)
  (h_inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂)
  (h : ∀ x ∈ s, (f x) ∈ t) :
  s.card ≤ t.card := by
  let image := Finset.image f s
  have h_subset : image ⊆ t := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h x hx
  have h_card : s.card = image.card := (Finset.card_image_of_inj f h_inj).symm
  rw [h_card]
  exact Finset.card_le_of_subset h_subset

/-- Cardinality inequality via injection:
    If f: s → t is injective on s, then |s| ≤ |t|
    Essential for Hopfield network state space comparisons. -/
@[simp]
lemma Finset.card_le_of_inj_on {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Nonempty α]
  {s : Finset α} {t : Finset β} (f : α → β)
  (h_inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂)
  (h_map : ∀ x ∈ s, f x ∈ t) :
  s.card ≤ t.card := by
  exact card_le_card_of_maps_to f h_inj h_map

/-- Two finite sets have equal cardinality if there exists a bijection between them.
    Essential for Hopfield network state space analysis. -/
@[simp]
lemma Finset.card_eq_of_bij {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
  {s : Finset α} {t : Finset β} (f : α → β) (g : β → α)
  (h_bij : ∀ x ∈ s, f x ∈ t ∧ g (f x) = x)
  (h_surj : ∀ y ∈ t, ∃ x ∈ s, f x = y) :
  s.card = t.card := by
  apply Nat.le_antisymm
  · -- Prove s.card ≤ t.card
    have inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ := by
      intros x₁ h₁ x₂ h₂ h_eq
      have := (h_bij x₁ h₁).2
      rw [h_eq] at this
      aesop
    have map_to : ∀ x ∈ s, f x ∈ t := fun x hx => (h_bij x hx).1
    exact card_le_card_of_maps_to f inj map_to
  · -- Prove t.card ≤ s.card
    have inj : ∀ y₁ ∈ t, ∀ y₂ ∈ t, g y₁ = g y₂ → y₁ = y₂ := by
      intros y₁ h₁ y₂ h₂ h_eq
      obtain ⟨x₁, hx₁, rfl⟩ := h_surj y₁ h₁
      obtain ⟨x₂, hx₂, rfl⟩ := h_surj y₂ h₂
      have h1 := (h_bij x₁ hx₁).2
      have h2 := (h_bij x₂ hx₂).2
      rw [h1] at h_eq
      rw [h2] at h_eq
      aesop
    have h_map : ∀ y ∈ t, g y ∈ s := by
      intros y hy
      obtain ⟨x, hx, hfx⟩ := h_surj y hy
      rw [← hfx]
      rw [← (h_bij x hx).2]
      aesop
    exact Finset.card_le_card_of_maps_to g inj h_map

/-- A finite set has cardinality 0 iff it is empty:
    |s| = 0 ↔ s = ∅
    Essential for Hopfield network empty state set analysis. -/
@[simp]
lemma Finset.card_eq_zero_iff {α : Type*} {s : Finset α} :
  s.card = 0 ↔ s = ∅ := by
  constructor
  · intro h
    by_contra h'
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h'
    have : 0 < s.card := Finset.card_pos.2 ⟨x, hx⟩
    linarith
  · intro h
    rw [h]
    rfl

/-- Sets have equal cardinality if there is a bijective correspondence:
    If f maps s to t bijectively, then |s| = |t|
    Essential for Hopfield network state space equivalence. -/
@[simp]
lemma Finset.card_congr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nonempty α]
  {s : Finset α} {t : Finset β} {f : α → β}
  (h_maps : ∀ x ∈ s, f x ∈ t)
  (h_inj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂)
  (h_surj : ∀ y ∈ t, ∃ x ∈ s, f x = y) :
  s.card = t.card := by
  apply Nat.le_antisymm
  · exact Finset.card_le_card_of_maps_to f h_inj h_maps
  · let g' : β → α := fun _ => Classical.arbitrary α
    let g := fun y => if h : y ∈ t then Classical.choose (h_surj y h) else g' y
    exact Finset.card_le_card_of_maps_to g
      (fun y₁ hy₁ y₂ hy₂ h => by
        have h₁ := Classical.choose_spec (h_surj y₁ hy₁)
        have h₂ := Classical.choose_spec (h_surj y₂ hy₂)
        have : f (g y₁) = y₁ := by
          simp [g]
          rw [dif_pos hy₁]
          exact h₁.2
        have h1 : f (g y₁) = y₁ := by
          simp [g]
          rw [dif_pos hy₁]
          exact h₁.2
        have h2 : f (g y₂) = y₂ := by
          simp [g]
          rw [dif_pos hy₂]
          exact h₂.2
        calc y₁ = f (g y₁) := h1.symm
          _ = f (g y₂) := by rw [h]
          _ = y₂ := h2)
      (fun y hy => by
        simp [g]
        rw [dif_pos hy]
        exact (Classical.choose_spec (h_surj y hy)).1)

/-- Sets have equal cardinality if they have same vertices:
    If s and t contain same elements, then |s| = |t|
    Essential for Hopfield network state comparison. -/
lemma Finset.card_eq_of_veq {α : Type*} [DecidableEq α]
  {s t : Finset α} (h : ∀ x, x ∈ s ↔ x ∈ t) :
  s.card = t.card := by
  apply Nat.le_antisymm
  · apply Finset.card_le_of_subset
    intro x hx
    exact (h x).mp hx
  · apply Finset.card_le_of_subset
    intro x hx
    exact (h x).mpr hx


open Matrix Matrix.toBilin BilinForm Matrix.toQuadraticMap'
open SpinState HopfieldState UpdateSeq

variable {n : ℕ}

lemma LinearMap.toMatrix₂'_symm_apply {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    dotProduct (W.mulVec v) w = (((LinearMap.toMatrix₂' ℝ).symm W) v) w := by
  simp only [dotProduct, mulVec, LinearMap.toMatrix₂']

  -- Our goal is to show
  -- ∑ i, (∑ j, W i j * v j) * w i = (((LinearMap.toMatrix₂' ℝ).symm W) v) w

  -- First, expand the left-hand side
  have expand_lhs : ∑ i, (∑ j, W i j * v j) * w i = ∑ i, ∑ j, W i j * v j * w i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_mul Finset.univ (fun j ↦ W i j * v j) (w i)

  -- Rewrite the LHS using our expansion
  calc
    ∑ i, (∑ j, W i j * v j) * w i = ∑ i, ∑ j, W i j * v j * w i := expand_lhs
    _ = ∑ j, ∑ i, W i j * v j * w i := by rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, W i j * w i * v j := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
  sorry


lemma dotProduct_eq_apply_symm_toMatrix₂' (v w : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
  dotProduct (W.mulVec v) w = (((LinearMap.toMatrix₂' ℝ).symm W) v) w := by
  -- Use the previous lemma
  exact LinearMap.toMatrix₂'_symm_apply W v w
