import NeuralNetworks.LLM.GPT2.Model'
import NeuralNetworks.LLM.GPT2.Tensorview.ComputeBounds

namespace LLM.GPT2

-- Section 5: Tensor Layout and Initialization

/--
Ensures that a `Nat` value is aligned to a specific boundary.
Returns the smallest N >= value such that N % alignment = 0.
-/
@[inline]
def alignTo (value : Nat) (alignment : Nat) : Nat :=
  if alignment == 0 then value
  else (value + alignment - 1) / alignment * alignment

/-- Lemma: The result of alignTo is always greater than or equal to the original value. -/
lemma alignTo_ge (value : Nat) (alignment : Nat) : value ≤ alignTo value alignment := by
  unfold alignTo
  by_cases h_align_zero : alignment = 0
  · simp [h_align_zero]
  · have h_align_pos : 0 < alignment := Nat.pos_of_ne_zero h_align_zero
    have h_mod_lt :
        (value + alignment - 1) % alignment < alignment :=
      Nat.mod_lt _ h_align_pos
    have h_mod_le :
        (value + alignment - 1) % alignment ≤ alignment - 1 :=
      Nat.le_pred_of_lt h_mod_lt
    have h_sum :
        alignTo value alignment + (value + alignment - 1) % alignment
            = value + alignment - 1 := by
      have h := Nat.mod_add_div (value + alignment - 1) alignment
      calc
        alignTo value alignment + (value + alignment - 1) % alignment
            = ((value + alignment - 1) / alignment * alignment)
                + (value + alignment - 1) % alignment := by
                  simp [alignTo, if_neg h_align_zero]
        _ = (value + alignment - 1) % alignment
                + ((value + alignment - 1) / alignment * alignment) := by
                  simp [Nat.add_comm]
        _ = (value + alignment - 1) % alignment
                + alignment * ((value + alignment - 1) / alignment) := by
                  simp [Nat.mul_comm]
        _ = value + alignment - 1 := by
                  simpa using h
    have h_le :
        value + alignment - 1 ≤ alignTo value alignment + (alignment - 1) := by
      have h := Nat.add_le_add_left h_mod_le (alignTo value alignment)
      simpa [h_sum] using h
    have h_add_sub :
        value + alignment - 1 = value + (alignment - 1) := by
      have h_alignment : alignment = (alignment - 1).succ :=
        Eq.symm (Nat.sub_one_add_one_eq_of_pos h_align_pos)
      calc
        value + alignment - 1
            = value + ((alignment - 1).succ) - 1 := by dsimp; grind
        _ = (value + (alignment - 1)).succ - 1 := by
              simp [Nat.add_comm, Nat.add_left_comm]
        _ = value + (alignment - 1) := by simp
    have h_le' :
        value + (alignment - 1) ≤ alignTo value alignment + (alignment - 1) := by
      simpa [h_add_sub] using h_le
    exact Nat.add_le_add_iff_right.mp h_le'

/-- Lemma: The result of alignTo is always a multiple of the alignment. -/
lemma alignTo_dvd (value : Nat) (alignment : Nat) (h_align_pos : alignment > 0) :
    alignment ∣ alignTo value alignment := by
  unfold alignTo
  simp [if_neg (Nat.ne_of_gt h_align_pos)]

/--
Represents the specification of a tensor before allocation.
It includes the proofs required for eventual TensorView creation.
-/
structure TensorSpec where
  name : String
  shape : Array Nat
  rank : Nat
  h_rank_eq_size : rank = shape.size
  h_dims_positive : ∀ (i : Fin rank), shape[i.val]'(by { rw [← h_rank_eq_size]; exact i.isLt }) > 0
  deriving Repr

/-- Calculates the number of elements in a TensorSpec. -/
@[inline] def TensorSpec.elementCount (ts : TensorSpec) : Nat :=
  ts.shape.foldl (· * ·) 1

/-- Calculates the size in bytes of a TensorSpec. Guaranteed divisible by bytesPerFloat. -/
@[inline] def TensorSpec.sizeBytes (ts : TensorSpec) : Nat :=
  ts.elementCount * bytesPerFloat

/--
Helper function to create a TensorSpec from a name and shape array, validating the shape
and constructing the necessary proofs (`h_dims_positive`) by bridging operational checks with formal proofs.
-/
def createTensorSpec (name : String) (shape : Array Nat) : Except TensorError TensorSpec :=
  if shape.isEmpty then
    -- Disallow scalar/empty tensors for parameter layouts, as they violate the positivity requirement.
    Except.error (TensorError.negativeDimension shape)
  else
    let rank := shape.size
    -- Operationally check if any dimension is zero using Array.find?.
    match hFind : shape.find? (fun dim => decide (dim = 0)) with
    | some _ => Except.error (TensorError.negativeDimension shape)
    | none =>
      have h_dims_positive :
          ∀ (i : Fin rank),
            shape[i.val]'(by { have : i.val < rank := i.isLt; simp[rank]}) > 0 := by
        intro i
        have hi : i.val < shape.size := by simp [rank]
        have h_all :
            ∀ x ∈ shape, decide (x = 0) = false := by
          simpa using (Array.find?_eq_none.mp hFind)
        have hx : decide (shape[i.val]'hi = 0) = false :=
          h_all (shape[i.val]'hi) (Array.getElem_mem hi)
        have hne : shape[i.val]'hi ≠ 0 := by
          intro h0
          simp [h0] at hx
        exact Nat.pos_of_ne_zero hne

      Except.ok {
        name := name,
        shape := shape,
        rank := rank,
        h_rank_eq_size := rfl,
        h_dims_positive := h_dims_positive
      }

/--
A builder for calculating the memory layout of a set of tensors.
It maintains critical invariants to guarantee the correctness and safety of the layout.
This is a purely functional structure, separating layout calculation from memory allocation.
-/
structure LayoutBuilder where
  specs : Array TensorSpec
  offsets : Array Nat
  /-- Total size required for the layout (the offset for the next potential tensor). -/
  currentOffset : Nat
  /-- Invariant: The number of specs matches the number of calculated offsets. -/
  h_offsets_size : specs.size = offsets.size
  /-- Invariant: All recorded offsets are aligned to bytesPerFloat. -/
  h_offsets_aligned : ∀ (i : Fin offsets.size), offsets[i] % bytesPerFloat = 0
  /-- Structural integrity invariant: each tensor fits in the used prefix.
      For every recorded entry i, its starting offset plus its size is ≤ currentOffset. -/
  h_offsets_bounded :
    ∀ (i : Fin offsets.size),
      let i' : Fin specs.size := ⟨i.val, by simp [h_offsets_size]⟩
      offsets[i] + (specs[i']).sizeBytes ≤ currentOffset
  -- Note: A SOTA formalization would also include an invariant proving structural integrity:
  -- ∀ i, offsets[i] + specs[i].sizeBytes <= currentOffset. This requires induction during 'add'.

/-- Initial empty LayoutBuilder. -/
def LayoutBuilder.empty : LayoutBuilder :=
  { specs := #[], offsets := #[], currentOffset := 0, h_offsets_size := rfl,
    h_offsets_aligned := fun i => by exfalso; exact Fin.elim0 i,
    h_offsets_bounded := fun i => by exfalso; exact Fin.elim0 i }

/--
Adds a tensor specification to the layout builder.
It calculates the size, aligns the current offset, updates the state,
and crucially, proves that the alignment invariant is maintained.
-/
def LayoutBuilder.add (lb : LayoutBuilder) (spec : TensorSpec) : LayoutBuilder :=
  let size := spec.sizeBytes
  let alignedOffset := alignTo lb.currentOffset bytesPerFloat
  let newOffset := alignedOffset + size
  -- Proof 1: Maintain size consistency.
  have h_new_offsets_size : (lb.specs.push spec).size = (lb.offsets.push alignedOffset).size := by
    simp [lb.h_offsets_size]
  -- Proof 2: Maintain alignment invariant.
  have h_new_offsets_aligned :
      ∀ (i : Fin (lb.offsets.push alignedOffset).size),
        (lb.offsets.push alignedOffset)[i] % bytesPerFloat = 0 := by
    intro i
    let newOffsets := lb.offsets.push alignedOffset
    by_cases h_i_eq_last : i.val = lb.offsets.size
    · -- i points to the newly added alignedOffset
      have h_get_eq_last :
          (lb.offsets.push alignedOffset)[i] = alignedOffset := by
        have hi :
            i = ⟨lb.offsets.size, by
              simp
            ⟩ := by
          apply Fin.ext
          simp [h_i_eq_last]
        simp [hi]
      have h_bpf_pos : 0 < bytesPerFloat := by simp [bytesPerFloat]
      simpa [h_get_eq_last] using
        Nat.mod_eq_zero_of_dvd (alignTo_dvd lb.currentOffset bytesPerFloat h_bpf_pos)
    · -- i points to an old element; reuse the invariant from lb
      have h_le_old : i.val ≤ lb.offsets.size := by
        have : i.val < lb.offsets.size + 1 := by simpa using i.isLt
        exact Nat.le_of_lt_succ this
      have h_i_lt_old_size : i.val < lb.offsets.size :=
        lt_of_le_of_ne h_le_old h_i_eq_last
      have h_get_eq_old :
          (lb.offsets.push alignedOffset)[i]
            = lb.offsets[i.val]'h_i_lt_old_size := by
        simp only [Fin.getElem_fin]
        exact Array.getElem_push_lt h_i_lt_old_size
      simpa [h_get_eq_old] using lb.h_offsets_aligned ⟨i.val, h_i_lt_old_size⟩
  -- Proof 3: Maintain the structural integrity invariant.
  have h_new_offsets_bounded :
      ∀ (i : Fin (lb.offsets.push alignedOffset).size),
        let i' : Fin (lb.specs.push spec).size := ⟨i.val, by simpa [lb.h_offsets_size] using i.isLt⟩
        (lb.offsets.push alignedOffset)[i]
          + ((lb.specs.push spec)[i']).sizeBytes
          ≤ newOffset := by
    intro i
    by_cases h_i_eq_last : i.val = lb.offsets.size
    · -- Last (new) element: equality is immediate.
      have h_get_off_last :
          (lb.offsets.push alignedOffset)[i] = alignedOffset := by
        have hi :
            i = ⟨lb.offsets.size, by simp⟩ := by
          apply Fin.ext
          simp [h_i_eq_last]
        simp [hi]
      have h_i_lt_spec_succ : i.val < lb.specs.size + 1 := by
        simpa [lb.h_offsets_size] using i.isLt
      let i' : Fin (lb.specs.size + 1) := ⟨i.val, h_i_lt_spec_succ⟩
      have h_i_spec_last : i'.val = lb.specs.size := by
        simpa [i', lb.h_offsets_size] using h_i_eq_last
      have h_get_spec_last :
          (lb.specs.push spec)[i'] = spec := by
        have hi' : i' = ⟨lb.specs.size, by simp⟩ := by
          apply Fin.ext
          simp [h_i_spec_last]
        simp [Fin.getElem_fin, hi']
      have : alignedOffset + spec.sizeBytes ≤ alignedOffset + spec.sizeBytes :=
        Nat.le_refl (alignedOffset + spec.sizeBytes)
      intro i'_1
      simp_all only [Array.size_push, Nat.add_right_cancel_iff, Fin.getElem_fin,
        le_refl, alignedOffset, i'_1, newOffset, size]
    · -- Old element: reuse previous bound and lift through currentOffset ≤ newOffset.
      have h_le_old : i.val ≤ lb.offsets.size := by
        have : i.val < lb.offsets.size + 1 := by simpa using i.isLt
        exact Nat.le_of_lt_succ this
      have h_i_lt_old_size : i.val < lb.offsets.size := lt_of_le_of_ne h_le_old h_i_eq_last
      have h_i_lt_spec_old_size : i.val < lb.specs.size := by simpa [lb.h_offsets_size] using h_i_lt_old_size
      have h_get_off_old :
          (lb.offsets.push alignedOffset)[i] = lb.offsets[i.val]'h_i_lt_old_size := by
        simp only [Fin.getElem_fin]
        exact Array.getElem_push_lt h_i_lt_old_size
      have h_i_lt_spec_succ : i.val < lb.specs.size + 1 := by
        simpa [lb.h_offsets_size] using i.isLt
      let i' : Fin (lb.specs.size + 1) := ⟨i.val, h_i_lt_spec_succ⟩
      have h_get_spec_old :
          (lb.specs.push spec)[i'] = lb.specs[i.val]'h_i_lt_spec_old_size := by
        have : i'.val < lb.specs.size := by simpa [i'] using h_i_lt_spec_old_size
        have : (lb.specs.push spec)[i'] = lb.specs[i'.val]'(by simpa [i'] using h_i_lt_spec_old_size) := by
          simp only [Fin.getElem_fin]
          exact Array.getElem_push_lt (by simpa [i'] using h_i_lt_spec_old_size)
        simpa [i'] using this
      have h_old_bound :
          lb.offsets[i.val]'h_i_lt_old_size
            + (lb.specs[i.val]'h_i_lt_spec_old_size).sizeBytes
            ≤ lb.currentOffset :=
        lb.h_offsets_bounded ⟨i.val, h_i_lt_old_size⟩
      have h_curr_le_aligned : lb.currentOffset ≤ alignedOffset :=
        alignTo_ge lb.currentOffset bytesPerFloat
      have h_aligned_le_new : alignedOffset ≤ newOffset := Nat.le_add_right _ _
      have h_curr_le_new : lb.currentOffset ≤ newOffset :=
        le_trans h_curr_le_aligned h_aligned_le_new
      exact
        le_trans
          (by aesop)
          h_curr_le_new
  {
    specs := lb.specs.push spec,
    offsets := lb.offsets.push alignedOffset,
    currentOffset := newOffset,
    h_offsets_size := h_new_offsets_size,
    h_offsets_aligned := h_new_offsets_aligned,
    h_offsets_bounded := h_new_offsets_bounded
  }

/--
Defines the memory layout for the GPT-2 parameters based on the configuration.
This rigorously calculates the required memory map while maintaining alignment proofs.
-/
def Config.buildParameterLayout (c : Config) : Except TensorError LayoutBuilder := do
  let mut lb := LayoutBuilder.empty
  -- Helper lambda to add specs within the Except monad
  let addSpec (name : String) (shape : Array Nat) (builder : LayoutBuilder) : Except TensorError LayoutBuilder := do
    let spec ← createTensorSpec name shape
    return builder.add spec
  -- Embeddings
  lb ← addSpec "wte" #[c.vocabSize, c.channels] lb
  lb ← addSpec "wpe" #[c.maxSeqLen, c.channels] lb
  -- Transformer Layers
  for i in [:c.numLayers] do
    let layerPrefix := s!"layer{i}_"
    lb ← addSpec (layerPrefix ++ "ln1w") #[c.channels] lb
    lb ← addSpec (layerPrefix ++ "ln1b") #[c.channels] lb
    -- QKV weights merged: input channels -> 3 * output channels
    lb ← addSpec (layerPrefix ++ "qkvw") #[c.channels, 3 * c.channels] lb
    lb ← addSpec (layerPrefix ++ "qkvb") #[3 * c.channels] lb
    lb ← addSpec (layerPrefix ++ "attprojw") #[c.channels, c.channels] lb
    lb ← addSpec (layerPrefix ++ "attprojb") #[c.channels] lb
    lb ← addSpec (layerPrefix ++ "ln2w") #[c.channels] lb
    lb ← addSpec (layerPrefix ++ "ln2b") #[c.channels] lb
    -- Feed Forward Network (FFN) intermediate size is typically 4 * channels
    let ffnIntermediate := 4 * c.channels
    lb ← addSpec (layerPrefix ++ "fcw") #[c.channels, ffnIntermediate] lb
    lb ← addSpec (layerPrefix ++ "fcb") #[ffnIntermediate] lb
    lb ← addSpec (layerPrefix ++ "fcprojw") #[ffnIntermediate, c.channels] lb
    lb ← addSpec (layerPrefix ++ "fcprojb") #[c.channels] lb
  -- Final Layer Norm
  lb ← addSpec "lnfw" #[c.channels] lb
  lb ← addSpec "lnfb" #[c.channels] lb
  return lb

/--
A structure representing a fully initialized memory block,
derived from a LayoutBuilder and an allocated storage reference.
-/
structure VerifiedMemoryBlock (s : Type) where
  layout : LayoutBuilder
  storageRef : ST.Ref s ByteArray
  /-- The total size of the storage as determined by the layout. -/
  totalSize : Nat
  h_totalSize_eq : totalSize = layout.currentOffset

/--
Initializes the memory block by allocating the required storage based on the layout.
-/
def VerifiedMemoryBlock.init (s : Type) (layout : LayoutBuilder) : ST s (VerifiedMemoryBlock s) := do
  let totalSize := layout.currentOffset
  -- Allocate the ByteArray with the required size. In a real scenario, this would load weights.
  let storage := ByteArray.mk (Array.replicate totalSize (0 : UInt8))
  let storageRef ← ST.mkRef storage
  return {
    layout := layout,
    storageRef := storageRef,
    totalSize := totalSize,
    h_totalSize_eq := rfl
  }

/--
Extracts a specific `TensorView` from a `VerifiedMemoryBlock`.
This function utilizes the proven invariants from the LayoutBuilder to safely construct the TensorView.
-/
def VerifiedMemoryBlock.getTensorView {s} (vmb : VerifiedMemoryBlock s) (idx : Nat)
    (h_idx_lt : idx < vmb.layout.specs.size) : TensorView s :=
  let layout := vmb.layout
  let spec := layout.specs[idx]'h_idx_lt
  have h_idx_lt_offsets : idx < layout.offsets.size := by rw [← layout.h_offsets_size]; exact h_idx_lt
  let offset := layout.offsets[idx]'h_idx_lt_offsets
  -- Proof of alignment derived directly from the LayoutBuilder invariant.
  have h_offset_aligned : offset % bytesPerFloat = 0 :=
    layout.h_offsets_aligned ⟨idx, h_idx_lt_offsets⟩
  -- Construct the TensorView using the pre-verified components.
  TensorView.mkUnsafe s
    spec.shape
    spec.rank
    vmb.storageRef
    offset
    h_offset_aligned
    spec.h_rank_eq_size
    spec.h_dims_positive

/--
Extracts a TensorView together with the structural bound offset + sizeBytes ≤ totalSize.
This is the bridge needed to assemble a `TensorView.ValidView` downstream.
-/
def VerifiedMemoryBlock.getTensorViewWithBound {s}
    (vmb : VerifiedMemoryBlock s) (idx : Nat)
    (h_idx_lt : idx < vmb.layout.specs.size) :
    { _tv : TensorView s //
      vmb.layout.offsets[idx]'(by
        simpa [← vmb.layout.h_offsets_size] using h_idx_lt) + (vmb.layout.specs[idx]'h_idx_lt).sizeBytes ≤ vmb.totalSize } :=
  let layout := vmb.layout
  let spec := layout.specs[idx]'h_idx_lt
  have h_idx_lt_offsets : idx < layout.offsets.size := by rw [← layout.h_offsets_size]; exact h_idx_lt
  let offset := layout.offsets[idx]'h_idx_lt_offsets
  let tv :=
    TensorView.mkUnsafe s
      spec.shape
      spec.rank
      vmb.storageRef
      offset
      (layout.h_offsets_aligned ⟨idx, h_idx_lt_offsets⟩)
      spec.h_rank_eq_size
      spec.h_dims_positive
  -- Bound from layout structural invariant
  have h_bound_layout :
      offset + spec.sizeBytes ≤ layout.currentOffset :=
    by
      have h := layout.h_offsets_bounded ⟨idx, h_idx_lt_offsets⟩
      -- Unfold the abbreviation i' used in the invariant and align with our names
      -- The invariant's i' is definally equal to idx on both arrays after rewriting sizes.
      simpa using h
  -- Translate layout.currentOffset to vmb.totalSize
  have h_bound_total : offset + spec.sizeBytes ≤ vmb.totalSize := by
    simpa [vmb.h_totalSize_eq] using h_bound_layout
  ⟨tv, h_bound_total⟩

-- Section 6: Verified Memory Initialization and Access

/--
A `ProvenTensorView` combines a `TensorView` with the proof that it is valid
(i.e., fits within) its underlying storage.
This eliminates the need to pass validity proofs during access operations.
-/
structure ProvenTensorView (s : Type) where
  tv : TensorView s
  storageSize : Nat
  /-- The proof that the view is safely contained within the storage.
      Wraps the proof (tv.offsetBytes + tv.sizeBytes ≤ storageSize). -/
  h_valid : TensorView.ValidView tv storageSize

/--
Extracts a `ProvenTensorView` from a `VerifiedMemoryBlock`.
This function leverages the layout invariants to construct the `h_valid` proof for the ProvenTensorView.
-/
def VerifiedMemoryBlock.getProvenTensorView {s} (vmb : VerifiedMemoryBlock s) (idx : Nat)
    (h_idx_lt : idx < vmb.layout.specs.size) : ProvenTensorView s :=
  let layout := vmb.layout
  let spec := layout.specs[idx]'h_idx_lt
  have h_idx_lt_offsets : idx < layout.offsets.size := by
    rw [← layout.h_offsets_size]; exact h_idx_lt
  let offset := layout.offsets[idx]'h_idx_lt_offsets
  -- Proof of alignment.
  have h_offset_aligned : offset % bytesPerFloat = 0 :=
    layout.h_offsets_aligned ⟨idx, h_idx_lt_offsets⟩
  -- Construct the base TensorView.
  let tv := TensorView.mkUnsafe s
    spec.shape
    spec.rank
    vmb.storageRef
    offset
    h_offset_aligned
    spec.h_rank_eq_size
    spec.h_dims_positive
  -- Proof of validity (Bounds). This is the critical connection.
  have h_layout_bound :
      offset + spec.sizeBytes ≤ layout.currentOffset := by
    -- Use the existing structural bound invariant of the layout.
    simpa using layout.h_offsets_bounded ⟨idx, h_idx_lt_offsets⟩
  -- Translate to total size of the memory block.
  have h_total_bound : offset + spec.sizeBytes ≤ vmb.totalSize := by
    simpa [vmb.h_totalSize_eq] using h_layout_bound
  have h_valid_proof : tv.offsetBytes + tv.sizeBytes ≤ vmb.totalSize := by
    have h_offset_eq : tv.offsetBytes = offset := rfl
    have h_size_eq : tv.sizeBytes = spec.sizeBytes := by
      unfold TensorView.sizeBytes TensorSpec.sizeBytes TensorView.elementCount TensorSpec.elementCount
      simp; exact mul_eq_mul_left_iff.mp rfl
    simpa [h_offset_eq, h_size_eq] using h_total_bound

  { tv := tv, storageSize := vmb.totalSize, h_valid := ⟨h_valid_proof⟩ }


-- Section 7: Streamlined Verified Accessors

/--
Safely retrieves a `Float` value from a `ProvenTensorView` at the specified indices.
This API is ergonomic and statically safe, as the bounds proof (`h_valid`) is intrinsic to the structure.
-/
def ProvenTensorView.get? {s : Type} (ptv : ProvenTensorView s) (indices : Array Nat)
    : ST s (Except TensorError Float) :=
  -- We delegate to the underlying TensorView.get?, providing the stored proof.
  -- This avoids duplicating the index calculation and bounds checking logic.
  ptv.tv.get? indices ptv.storageSize ptv.h_valid.h_valid

/--
Sets a `Float` value at the specified `indices` within the `ProvenTensorView`.
-/
def ProvenTensorView.set! {s : Type} (ptv : ProvenTensorView s) (indices : Array Nat) (value : Float)
    : ST s (Except TensorError Unit) :=
  -- We delegate to the underlying TensorView.set!, providing the stored proof.
  ptv.tv.set! indices value ptv.storageSize ptv.h_valid.h_valid

/-
TODO
1. Formal definition of Abstract Tensors (mathematical representation).
2. Formal specification of tensor operations (e.g., MatMul, Element-wise operations).
-/

-- Section 8: Functional Correctness of Indexing

/-
This section proves that `computeFlatIndex` correctly implements the standard row-major linearization formula.
We use an iterative definition equivalent to Horner's method as the mathematical specification.
This definition processes dimensions from right to left (LSD to MSD), mirroring `computeHelper`.
-/

/--
The update function used in the iterative calculation of the row-major index (LSD first).
(acc, stride) -> (index_i, shape_i) -> (acc + index_i * stride, stride * shape_i)
-/
@[inline]
def rowMajorUpdate (state : Nat × Nat) (input : Nat × Nat) : Nat × Nat :=
  (state.fst + input.fst * state.snd, state.snd * input.snd)

/--
Mathematical specification of the row-major index calculation, defined iteratively.
-/
def rowMajorIter (shape : List Nat) (indices : List Nat) : Nat :=
  -- We reverse the lists so that foldl processes them from right to left.
  let combined := List.zip indices.reverse shape.reverse
  -- The foldl applies the update function starting from (0, 1).
  (combined.foldl rowMajorUpdate (0, 1)).fst

-- Lemma 8.1: Generalized Associativity/Distributivity of the Row-Major Update Fold.
/--
If applying the fold over a list Z starting from (0, 1) yields (A_final, S_final),
then starting from (A_start, S_start) yields (A_start + S_start * A_final, S_start * S_final).
This property is crucial for relating partial index computations performed in different stages of the recursion.
-/
lemma foldl_rowMajorUpdate_general (Z : List (Nat × Nat)) (A_start S_start : Nat) :
  let result_base := Z.foldl rowMajorUpdate (0, 1)
  let A_final := result_base.fst
  let S_final := result_base.snd
  Z.foldl rowMajorUpdate (A_start, S_start) = (A_start + S_start * A_final, S_start * S_final) := by
  induction Z generalizing A_start S_start with
  | nil =>
    simp [List.foldl]
  | cons head tail ih =>
    let (i, s) := head
    let result_tail_base := tail.foldl rowMajorUpdate (0, 1)
    let A_tail := result_tail_base.fst
    let S_tail := result_tail_base.snd
    simp [List.foldl, rowMajorUpdate]
    let A_new := A_start + i * S_start
    let S_new := S_start * s
    have ih1 := ih A_new S_new
    have h_final : tail.foldl rowMajorUpdate (i, s) = (i + s * A_tail, s * S_tail) := ih i s
    simpa [A_new, S_new, h_final, rowMajorUpdate,
      result_tail_base, A_tail, S_tail,
      Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih1

-- Lemma 8.2: Relationship between successive Row-Major computations (Horner's method equivalence).
/--
Proves the recursive relationship:
RM(S_prefix ++ [s_k], I_prefix ++ [i_k]) = i_k + s_k * RM(S_prefix, I_prefix).
-/
lemma rowMajorIter_append_single (S_prefix I_prefix : List Nat) (s_k i_k : Nat) :
  rowMajorIter (S_prefix ++ [s_k]) (I_prefix ++ [i_k]) =
  i_k + s_k * (rowMajorIter S_prefix I_prefix) := by
  unfold rowMajorIter
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
  simp only [List.zip_cons_cons, List.foldl_cons, rowMajorUpdate, zero_add, mul_one, one_mul]
  let Z := List.zip I_prefix.reverse S_prefix.reverse
  let result_base := Z.foldl rowMajorUpdate (0, 1)
  have h_general := foldl_rowMajorUpdate_general Z i_k s_k
  rw [h_general]

-- Lemma 8.3: Array prefix extraction and List conversion relationship.
/--
Proves that extracting a prefix of length k+1 and converting to a list is equivalent to
extracting a prefix of length k, converting to a list, and appending the element at index k.
Requires k < arr.size.
-/
lemma Array.extract_prefix_k_plus_1_toList {α : Type} [Inhabited α]
    (arr : Array α) (k : Nat) (h_k_lt_size : k < arr.size) :
  (arr.extract 0 (k + 1)).toList = (arr.extract 0 k).toList ++ [arr[k]!] := by
  have h_kp1_le_size : k + 1 ≤ arr.size := Nat.succ_le_of_lt h_k_lt_size
  have h_k_le_size : k ≤ arr.size := Nat.le_of_lt h_k_lt_size
  rw [Array.extract_prefix_toList_eq_take_toList arr (k + 1) h_kp1_le_size]
  rw [Array.extract_prefix_toList_eq_take_toList arr k h_k_le_size]
  have h_k_lt_list_len : k < arr.toList.length := by
    simpa [Array.length_toList] using h_k_lt_size
  have h_some : (arr.toList)[k]? = some (arr.toList.get ⟨k, h_k_lt_list_len⟩) := by
    simp
  have h1 : arr.toList.get (⟨k, h_k_lt_list_len⟩ : Fin arr.toList.length) = arr[k]'h_k_lt_size := by
    simp
  have h2 : arr[k]'h_k_lt_size = arr[k]! := by
    exact Eq.symm (getElem_eq_get! h_k_lt_size)
  have h_get_eq : arr.toList.get ⟨k, h_k_lt_list_len⟩ = arr[k]! := by
    simp [h2]
  have h_get?_toList : ((arr.toList)[k]?).toList = [arr[k]!] := by
    simp [h_some, Option.toList]; assumption
  rw [List.take_succ]
  rw [h_get?_toList]


-- Theorem 8.4: Functional Correctness of computeHelper.
/--
Proves that `computeHelper` (via `ComputeHelperRel`) correctly implements the `rowMajorIter` specification.
The theorem establishes an invariant connecting the final result (res) to the current state (fir, sa)
and the mathematical index of the remaining prefix (the more significant dimensions).

Invariant: res = fir + sa * RM(Shape[0..R-i_rev], Indices[0..R-i_rev])
-/
theorem computeHelper_functional_correctness
    {shape indices : Array Nat} {rank : Nat}
    (h_shape_size : shape.size = rank) (h_indices_size : indices.size = rank)
    {i_rev fir sa res : Nat}
    (h_rel : ComputeHelperRel shape rank indices i_rev fir sa res) :
    res = fir + sa * rowMajorIter
      (shape.extract 0 (rank - i_rev)).toList
      (indices.extract 0 (rank - i_rev)).toList := by
  -- The proof is by induction on the structure of the relation h_rel.
  induction h_rel with
  | tc i_rev fir sa h_term =>
    -- Base Case (Termination): i_rev >= rank.
    have h_len_zero : rank - i_rev = 0 := Nat.sub_eq_zero_of_le h_term
    rw [h_len_zero]
    -- Shape.extract 0 0 = [].
    simp only [Array.extract_eq_nil_of_start_eq_end, Array.toList_empty]
    -- rowMajorIter [] [] = 0.
    unfold rowMajorIter
    simp only [List.reverse_nil, List.zip_nil_left, List.foldl_nil]
    -- res = fir + sa * 0.
    simp
  | rs i_rev fir sa newFir newSa res h_not_term k h_k_def h_k_lt_idx_size h_k_lt_shape_size
     idx_val h_idx_eq dim_val h_dim_eq h_bound h_newFir_def h_newSa_def h_recursive_call ih =>
    let len_next := rank - (i_rev + 1)
    let len_curr := rank - i_rev
    rw [h_newFir_def, h_newSa_def] at ih
    have h_len_curr_eq_kp1 : len_curr = k + 1 := by
      rw [h_k_def]; simp [len_curr]; omega
    have h_len_next_eq_k : len_next = k := by
      rw [h_k_def]; simp [len_next]; omega
    have h_k_lt_rank : k < rank := by
      rw [h_k_def]; exact Nat.sub_one_sub_lt_of_lt h_not_term
    have h_k_lt_shape_size_derived : k < shape.size := by rw [h_shape_size]; exact h_k_lt_rank
    have h_k_lt_indices_size_derived : k < indices.size := by rw [h_indices_size]; exact h_k_lt_rank
    have h_shape_prefix_rel : (shape.extract 0 len_curr).toList = (shape.extract 0 len_next).toList ++ [shape[k]!] := by
      rw [h_len_curr_eq_kp1, h_len_next_eq_k]
      exact Array.extract_prefix_k_plus_1_toList shape k h_k_lt_shape_size_derived
    have h_indices_prefix_rel : (indices.extract 0 len_curr).toList = (indices.extract 0 len_next).toList ++ [indices[k]!] := by
      rw [h_len_curr_eq_kp1, h_len_next_eq_k]
      exact Array.extract_prefix_k_plus_1_toList indices k h_k_lt_indices_size_derived
    have h_dim_val_eq_get_bang : dim_val = shape[k]! := by
      rw [h_dim_eq]; exact Eq.symm (Array.getElem_eq_get! h_k_lt_shape_size)
    have h_idx_val_eq_get_bang : idx_val = indices[k]! := by
      rw [h_idx_eq]; exact Eq.symm (Array.getElem_eq_get! h_k_lt_idx_size)
    have h_RM_relation := rowMajorIter_append_single
      (shape.extract 0 len_next).toList
      (indices.extract 0 len_next).toList
      (shape[k]!)
      (indices[k]!)
    rw [← h_shape_prefix_rel, ← h_indices_prefix_rel] at h_RM_relation
    rw [ih]
    rw [h_dim_val_eq_get_bang, h_idx_val_eq_get_bang]
    rw [h_RM_relation]
    ring

open scoped Array

-- Corollary 8.5: Functional Correctness of computeFlatIndex.
/--
Proves that if computeFlatIndex returns successfully, the result is equal to the
mathematical row-major specification applied to the tensor's shape and the input indices.
-/
theorem computeFlatIndex_functional_correctness
    (shape indices : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank), shape[i.val]'(by { rw [← h_rank_eq_size]; exact i.isLt }) > 0)
    (res : Nat)
    (h_compute : computeFlatIndex shape rank h_rank_eq_size h_dims_pos indices = Except.ok res) :
    res = rowMajorIter shape.toList indices.toList := by

  -- Unfold and case split on the actual rank check to obtain a propositional equality.
  unfold computeFlatIndex at h_compute
  by_cases h_indices_size : indices.size = rank
  · -- Case 1: indices.size = rank.
    simp [h_indices_size] at h_compute
    have h_rel :=
      (computeHelper_eq_ok_iff_rel (Eq.symm h_rank_eq_size) h_indices_size).mp h_compute
    have h_correctness :=
      computeHelper_functional_correctness (Eq.symm h_rank_eq_size) h_indices_size h_rel
    simp only [Nat.sub_zero, zero_add, one_mul] at h_correctness
    have h_extract_shape_eq_self : shape.extract 0 rank = shape := by
      rw [h_rank_eq_size]; exact extract_eq_self_of_rank_eq_size shape
    have h_extract_indices_eq_self : indices.extract 0 rank = indices := by
      rw [← h_indices_size]; exact extract_eq_self_of_rank_eq_size indices
    simpa [h_extract_shape_eq_self, h_extract_indices_eq_self] using h_correctness
  · -- Case 2: indices.size ≠ rank. Contradicts the successful result.
    -- When the sizes mismatch, computeFlatIndex must return an error.
    simp [h_indices_size] at h_compute

/-
Status:
We have rigorously proven:
1. Memory Safety: Bounds checking, alignment, and positive dimensions (via `computeFlatIndex_bounds` and `LayoutBuilder` invariants).
2. Structural Integrity: Initialization safety (via `ProvenTensorView`).
3. Functional Correctness: The indexing implementation correctly adheres to the mathematical row-major specification (via `computeFlatIndex_functional_correctness`).

The next phase of the project involves formalizing the actual GPT-2 operations (MatMul, LayerNorm, Attention, etc.) using this verified infrastructure.
-/

end LLM.GPT2
