import NeuralNetworks.LLM.GPT2.TensorView.Lemmas
import Init.Data.List.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.Array.Lemmas


open LLM.GPT2 -- For Core types like TensorError, bytesPerFloat
open Batteries

namespace LLM.GPT2

-- SECTION 4: Flat Index Bounds


/-- Handle rank=1 specialized case in the base case. -/
lemma computeHelper_bounds_base_rank_one
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_rank_one : rank = 1)
    (h_dims_pos : ∀ (i : Fin rank), shape[i]'(by
      have h1 : i.val < rank := i.isLt
      have h2 : rank = shape.size := h_rank_eq_size
      exact Nat.lt_of_lt_of_eq h1 h2
    ) > 0)
    (indices : Array Nat) (h_indices_size : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (result : Nat)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result) :
    result < shape.foldl (· * ·) 1 := by
  -- For the initial call with i_rev=0, flatIndexRel must be 0
  have h_flatIndexRel_is_zero : flatIndexRel = 0 := by
    unfold computeHelper at h_helper
    split_ifs at h_helper with h_if_cond
    · subst h_indices_size h_stride
      simp_all only [Except.ok.injEq, Fin.getElem_fin, gt_iff_lt, ge_iff_le, nonpos_iff_eq_zero, one_ne_zero]  -- i_rev=0 implies 0 < rank=1, so this branch isn't taken
    -- We need to simplify the let expressions in h_helper
    have h_indices_0_lt_shape_0 : indices[0]! < shape[0]! := by
      -- Extract from h_helper that this comparison must have succeeded
      by_cases h_idx_ge_dim : indices[rank - 1]! >= shape[rank - 1]!
      · -- If the index is out of bounds, we'd get an error, not an ok result
        rw [h_rank_one] at h_helper
        simp [computeHelper] at h_helper
        simp at h_idx_ge_dim
        have h_simp : (let i := 0;
                        let index := indices[i]!;
                        let dimSize := shape[i]!;
                        if index ≥ dimSize then Except.error (TensorError.indexOutOfBounds indices shape)
                        else
                          let newFlatIndex := flatIndexRel + index * stride;
                          let newStride := stride * dimSize;
                          computeHelper shape 1 indices 1 newFlatIndex newStride) = Except.ok result := by simp
        -- Since we get Except.ok, the index must be valid
        simp [h_idx_ge_dim] at h_simp
        -- This leads to a contradiction since we can't get Except.ok from Except.error
        aesop
      · -- Index is in bounds case
        rw [h_rank_one] at h_idx_ge_dim
        exact Nat.lt_of_not_ge h_idx_ge_dim
      -- For our initial call to computeHelper, flatIndexRel is set to 0
      rw [h_rank_one] at h_helper
      injection h_helper with h_recursive_call
      -- Compare the recursive call to establish that flatIndexRel = 0
      have h_if_expanded : (let i := 0;
                           let index := indices[i]!;
                           let dimSize := shape[i]!;
                           if index ≥ dimSize then Except.error (TensorError.indexOutOfBounds indices shape)
                           else
                             let newFlatIndex := flatIndexRel + index * stride;
                             let newStride := stride * dimSize;
                             computeHelper shape 1 indices 1 newFlatIndex newStride) = Except.ok result := by
        simp [computeHelper]  -- This unfolds the let bindings to match h_helper's form
        exact h_helper

      have h_match_recursive_calls : computeHelper shape 1 indices 1 (flatIndexRel + indices[0]! * stride) (stride * shape[0]!) =
                                    computeHelper shape 1 indices 1 (0 + indices[0]! * stride) (stride * shape[0]!) := by
        rw [← h_if_expanded] at h_recursive_call
        exact recursive_call_rank_one shape indices indices[0]! stride flatIndexRel (flatIndexRel + indices[0]! * stride)
      -- By injectivity, the arguments must be equal
      exact Nat.eq_zero_of_add_eq_zero_right (Except.ok.inj h_match_recursive_calls)
  let k_idx := rank - 1
  let index_val := indices[k_idx]!
  let dim_size := shape[k_idx]!

  -- Extract recursive call components
  have h_components := extract_recursive_call_components
    shape rank indices flatIndexRel stride result (h_rank_one ▸ Nat.one_pos) h_helper

  have h_index_lt_dim : index_val < dim_size := h_components.1
  have h_recursive_call := h_components.2

  -- Extract the computed result
  have h_result_eq : result = flatIndexRel + index_val * stride := by
    -- Apply rank=1 recursive call simplification lemma
    let new_flat_idx := flatIndexRel + index_val * stride

    -- Simplify using h_rank_one
    have h_k_idx_zero : k_idx = 0 := by simp [k_idx, h_rank_one]
    have h_index_val_eq : index_val = indices[0]! := by
      simp [index_val, h_k_idx_zero]

    -- Make explicit that indices[rank-1] = indices[0] when rank=1
    have h_indices_eq : indices[rank - 1]! = indices[0]! := by
      rw [h_rank_one]

    -- Extract result equality from recursive call
    have h_flat_idx_term : flatIndexRel + indices[rank - 1]! * stride = flatIndexRel + index_val * stride := by
      rw [h_indices_eq, h_index_val_eq]

    -- Get the result from h_recursive_call by first getting proper equality
    have h_equal_results : (Except.ok (flatIndexRel + indices[rank - 1]! * stride) : Except TensorError Nat) = (Except.ok result : Except TensorError Nat) := by
      -- First establish what the computation returns for rank=1
      have h_comp_result : computeHelper shape rank indices 1 (flatIndexRel + indices[rank - 1]! * stride) (stride * shape[rank - 1]!) = Except.ok (flatIndexRel + indices[rank - 1]! * stride) := by
        -- Fix: First rewrite rank to 1 using h_rank_one to make types match
        rw [h_rank_one]
        -- Then apply the lemma with the correct indices
        exact recursive_call_rank_one shape indices indices[0]! stride flatIndexRel (flatIndexRel + indices[0]! * stride)
      -- Then connect with our actual computation result
      rw [← h_recursive_call, h_comp_result]

    have h_result_from_rec := Except.ok.inj h_equal_results

    -- Connect everything
    rw [h_flat_idx_term] at h_result_from_rec
    exact Eq.symm h_result_from_rec

  rw [h_result_eq]

  -- For rank=1: k_idx=0, extract is empty, stride=1
  have h_k_idx_zero : k_idx = 0 := by
    simp [k_idx, h_rank_one]

  have h_dim_size_is_shape_0 : dim_size = shape[0]! := by
    simp [dim_size, h_k_idx_zero]

  have h_extract_empty : (shape.extract 0 (rank - 1)).foldl (· * ·) 1 = 1 := by
    rw [h_rank_one]
    apply extract_empty_product

  have h_stride_is_one : stride = 1 := by
    rw [h_stride, h_rank_one]
    apply extract_empty_product

  -- For a singleton array, the product is just that element
  have h_shape_product : shape.foldl (· * ·) 1 = shape[0]! := by
    -- Proof for an array with size 1
    have h_shape_size_one : shape.size = 1 := by
      rw [←h_rank_eq_size, h_rank_one]

    -- Reduce to list operation
    rw [← Array.foldl_toList]
    rw [← List.prod_eq_foldl]

    -- Since shape has size 1, its toList has length 1
    have h_shape_toList_length : shape.toList.length = 1 := by
      rw [Array.length_toList, h_shape_size_one]

    -- A list with length 1 consists of exactly one element
    have h_shape_toList_eq : shape.toList = [shape[0]!] := by
      apply List.eq_singleton_of_length_eq_one
      · exact h_shape_toList_length
      · rw [List.head?]
        simp only [h_shape_toList_length, List.length_pos, if_true]
        rw [List.getElem_eq_get?, Array.getElem_toList]
        simp only [h_shape_size_one, gt_iff_lt, zero_lt_one, if_true]
        rfl

    -- The product of a singleton list is its element
    rw [h_shape_toList_eq]
    simp only [List.prod_singleton]

  -- Apply the bounds
  rw [h_stride_is_one, Nat.mul_one, h_flatIndexRel_is_zero, Nat.zero_add]
  rw [h_shape_product]
  -- Fix: Use transitivity instead of rewrite
  exact Nat.lt_of_lt_of_eq h_index_lt_dim h_dim_size_is_shape_0

/-- Base case of computeHelper_bounds theorem when i_rev = 0. -/
lemma computeHelper_bounds_base
    (shape : Array Nat) (rank : Nat)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank), shape[i]'(by
      have h1 : i.val < rank := i.isLt
      have h2 : rank = shape.size := h_rank_eq_size
      exact Nat.lt_of_lt_of_eq h1 h2
    ) > 0)
    (indices : Array Nat) (h_indices_size : indices.size = rank)
    (flatIndexRel : Nat) (stride : Nat)
    (h_stride : stride = (shape.extract rank rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 rank).foldl (· * ·) 1)
    (h_helper : computeHelper shape rank indices 0 flatIndexRel stride = Except.ok result) :
    result < shape.foldl (· * ·) 1 := by
  unfold computeHelper at h_helper
  split_ifs at h_helper with h_if_cond
  · -- Case: 0 >= rank (which implies rank = 0 for Nat)
    injection h_helper with h_eq_result
    subst result

    -- Prove rank = 0 from 0 >= rank
    have h_rank_zero : rank = 0 :=
      Nat.eq_zero_of_le_zero h_if_cond

    -- Apply the specialized helper lemma for rank = 0
    rw [h_rank_zero] at *
    apply computeHelper_bounds_rank_zero shape h_rank_eq_size indices h_indices_size
      flatIndexRel stride h_stride h_flatIndexRel

  · -- Case: ¬(0 >= rank) (i.e., 0 < rank)
    -- h_not_if_cond is 0 < rank
    have h_not_if_cond : 0 < rank :=
      Nat.gt_of_not_le h_if_cond

    -- Extract the key recursive call details using our new lemma
    let k_idx := rank - 1
    let index_val := indices[k_idx]!
    let dim_size := shape[k_idx]!

    have h_helper_components := extract_computeHelper_i_rev_zero_components
      shape rank indices h_not_if_cond h_helper

    have h_index_val_lt_dim_size := h_helper_components.1
    have h_helper_rec := h_helper_components.2

    -- Apply main theorem for the recursive call with i_rev = 1
    apply computeHelper_bounds shape rank h_rank_eq_size h_dims_pos indices h_indices_size 1
      (flatIndexRel + index_val * stride) (stride * dim_size)
    · -- Prove 1 ≤ rank
      exact Nat.succ_le_of_lt h_not_if_cond
    · -- Prove stride property for recursive call using our new lemma
      apply stride_for_i_rev_zero_recursive_call shape rank h_not_if_cond h_rank_eq_size
    · -- Prove flatIndexRel bound for recursive call using our new lemma
      apply flatIndexRel_bound_for_i_rev_zero_recursive_call
        shape rank h_not_if_cond h_rank_eq_size indices
        flatIndexRel stride h_stride h_flatIndexRel
        index_val dim_size h_index_val_lt_dim_size
    · -- Pass the recursive helper
      exact h_helper_rec

/-- Helper theorem: computeHelper maintains the bound invariant through recursion. -/
theorem computeHelper_bounds
    (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank), shape[i]'(by
      have h1 : i.val < rank := i.isLt
      have h2 : rank = shape.size := h_rank_eq_size
      exact Nat.lt_of_lt_of_eq h1 h2
    ) > 0)
    (indices : Array Nat) (h_indices_size : indices.size = rank)
    (i_rev : Nat) (flatIndexRel : Nat) (stride : Nat)
    (h_i_rev : i_rev ≤ rank)
    (h_stride : stride = (shape.extract (rank - i_rev) rank).foldl (· * ·) 1)
    (h_flatIndexRel : flatIndexRel < stride * (shape.extract 0 (rank - i_rev)).foldl (· * ·) 1)
    (result : Nat)
    (h_helper : computeHelper shape rank indices i_rev flatIndexRel stride = Except.ok result)
    : result < shape.foldl (· * ·) 1 := by
  -- Case analysis on i_rev value
  cases h_eq : i_rev
  case zero =>
    -- Base case uses the specialized lemma
    apply computeHelper_bounds_base shape rank h_rank_eq_size h_dims_pos indices h_indices_size
      flatIndexRel stride h_stride h_flatIndexRel
    rw [h_eq] at h_helper
    exact h_helper

  case succ i_prev =>
    -- Induction on i_rev
    unfold computeHelper at h_helper
    split at h_helper
    case inl h_ge =>
      -- When i_rev ≥ rank, return flatIndexRel
      injection h_helper with h_result
      rw [h_result]

      -- If i_rev = rank (since i_rev ≤ rank from h_i_rev)
      have h_i_rev_eq_rank : i_rev = rank := by
        apply Nat.le_antisymm
        · exact h_ge
        · exact h_i_rev

      -- At i_rev = rank, stride = 1 and flatIndexRel < shape.foldl (· * ·) 1
      rw [h_i_rev_eq_rank] at h_stride h_flatIndexRel
      rw [h_stride]
      rw [extract_empty_product]
      rw [Nat.mul_one] at h_flatIndexRel

      -- Normalize the expression of the array extract
      have h_extract_form : (shape.extract 0 rank) = (shape.extract 0 rank) 0 (rank ⊓ shape.size) := by
        rw [h_rank_eq_size]
        rw [min_self]
        rfl

      rw [←h_extract_form] at h_flatIndexRel
      exact h_flatIndexRel

    case inr h_lt =>
      -- When i_rev < rank, process one more index and recur
      let i := rank - 1 - i_rev
      let index := indices[i]!
      let dimSize := shape[i]!

      split at h_helper
      case inl h_index_ge =>
        -- This contradicts successful computation
        contradiction

      case inr h_index_lt =>
        -- Process current index and recur
        let newFlatIndex := flatIndexRel + index * stride
        let newStride := stride * dimSize

        -- Use the inductive step lemma
        apply computeHelper_bounds_inductive shape rank h_rank_eq_size h_dims_pos indices
          h_indices_size i_prev newFlatIndex newStride h_lt _ _

        -- Prove stride matches extract pattern after update
        · sorry -- Use stride_update_matches_extract

        -- Prove flatIndex bound is maintained
        · sorry -- Use flatIndex_bound_maintained
        -- Pass the recursive call result
        · exact h_helper

/-- Proof: If computeFlatIndex succeeds, the result is within the element count bounds. -/
theorem computeFlatIndex_bounds
    (shape : Array Nat) (rank : Nat) (h_rank_eq_size : rank = shape.size)
    (h_dims_pos : ∀ (i : Fin rank), shape[i.val]'(by { have h1 : i.val < rank := i.isLt; have h2 : rank = shape.size := h_rank_eq_size; exact Nat.lt_of_lt_of_eq h1 h2 }) > 0)
    (indices : Array Nat)
    (h_compute : computeFlatIndex shape rank h_rank_eq_size h_dims_pos indices = Except.ok flatIndexRel)
    : flatIndexRel < shape.foldl (· * ·) 1 := by
  -- Extract key facts from h_compute
  unfold computeFlatIndex at h_compute

  -- Establish that indices.size == rank from successful computation
  have h_indices_size : indices.size = rank := by
    cases h_size_check : indices.size == rank
    case true =>
      exact Eq.of_beq_eq_true h_size_check
    case false =>
  -- Apply the helper theorem with initial values
  apply computeHelper_bounds shape rank h_rank_eq_size h_dims_pos indices h_indices_size 0 0 1
  · -- Show 0 ≤ rank
    exact Nat.zero_le rank
  · -- Initial stride = 1 matches empty product
    simp [Array.extract]
  · -- Initial flatIndexRel = 0 is within bounds
    simp
  · -- Pass the computation result
    -- Convert from computeFlatIndex to computeHelper result
    unfold computeFlatIndex at h_compute
    simp [h_indices_size] at h_compute
    exact h_compute
  · -- Initial stride = 1 matches empty product
    simp [Array.extract]
  · -- Initial flatIndexRel = 0 is within bounds
    simp
  · -- Pass the computation result
    exact h_compute

def TensorView.get? (tv : TensorView s) (indices : Array Nat)
    -- We need a snapshot of storage size for the proof, could pass ValidView proof instead
    (storageSize : Nat) (h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize)
    : ST s (Except TensorError Float) := do

  -- Compute flat index, getting potential errors
  match computeFlatIndex tv.shape tv.rank tv.h_dims_positive indices with
  | Except.error e => return Except.error e
  | Except.ok flatIndexRel =>
      -- Prove that the resulting flat index is within bounds
      have h_flat_bounds : flatIndexRel < tv.elementCount :=
        computeFlatIndex_bounds tv.shape tv.rank tv.h_dims_positive indices (by assumption)

      -- Calculate absolute byte index
      let byteIndexAbs := tv.offsetBytes + flatIndexRel * bytesPerFloat

      -- Prove that the read is within the view's allocated slice
      have h_read_in_view : byteIndexAbs + bytesPerFloat <= tv.offsetBytes + tv.sizeBytes := by
        -- Proof sketch: uses h_flat_bounds, definition of sizeBytes
        sorry

      -- Prove that the read is within the underlying storage bounds
      have h_read_in_storage : byteIndexAbs + bytesPerFloat <= storageSize := by
        -- Proof sketch: uses h_read_in_view and h_valid
        sorry

      -- Perform the read
      let storage ← ST.Ref.get tv.storageRef
      match Hybrid.ByteArray.readFloatLE? storage byteIndexAbs with
      | Some val => return Except.ok val
      | None =>
          -- This case *should* be impossible if h_read_in_storage holds and readFloatLE? is correct.
          -- Indicates an internal inconsistency or bug in readFloatLE?.
          panic! "Internal error: readFloatLE? failed despite bounds proof"

/--
  -- Compute flat index
  match computeFlatIndex tv.shape tv.rank tv.h_rank_eq_size tv.h_dims_positive indices with
-/
def TensorView.set! (tv : TensorView s) (indices : Array Nat) (value : Float)
    (storageSize : Nat) (h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize)
    : ST s (Except TensorError Unit) := do

  -- Compute flat index
  match computeFlatIndex tv.shape tv.rank tv.h_dims_positive indices with
  | Except.error e => return Except.error e
  | Except.ok flatIndexRel =>
      have h_flat_bounds : flatIndexRel < tv.elementCount :=
        computeFlatIndex_bounds tv.shape tv.rank tv.h_dims_positive indices (by assumption)

      -- Calculate absolute byte index
      let byteIndexAbs := tv.offsetBytes + flatIndexRel * bytesPerFloat

      -- Prove that the write is within the view's allocated slice
      have h_write_in_view : byteIndexAbs + bytesPerFloat <= tv.offsetBytes + tv.sizeBytes := by
        -- Proof sketch: similar to h_read_in_view
        sorry

      -- Prove that the write is within the underlying storage bounds
      have h_write_in_storage : byteIndexAbs + bytesPerFloat <= storageSize := by
         -- Proof sketch: similar to h_read_in_storage
        sorry

      -- Perform the write (writeFloatLE! panics if bounds fail, but h_write_in_storage proves it won't)
      ST.Ref.modify tv.storageRef (fun storage =>
        Hybrid.ByteArray.writeFloatLE! storage byteIndexAbs value
      )
      return Except.ok ()

-- == Section 4: GPT-2 Structures (Minimal Changes, Focus on Init) ==

-- Config, ParameterTensors, ActivationTensors structures remain similar
-- BUT: Activation Tensors need review for memory usage

structure Config where -- Unchanged for now
  maxSeqLen : Nat       := 1024
  vocabSize : Nat       := 50257
  paddedVocabSize : Nat := 50304
  numLayers : Nat       := 12
  numHeads : Nat        := 12
  channels : Nat        := 768
  deriving Repr, Inhabited

structure ParameterTensors (s : Type) where -- Unchanged structure
  wte : TensorView s; wpe : TensorView s; ln1w : TensorView s; ln1b : TensorView s
  qkvw : TensorView s; qkvb : TensorView s; attprojw : TensorView s; attprojb : TensorView s
  ln2w : TensorView s; ln2b : TensorView s; fcw : TensorView s; fcb : TensorView s
  fcprojw : TensorView s; fcprojb : TensorView s; lnfw : TensorView s; lnfb : TensorView s
  deriving Repr -- Assuming TensorView Repr exists

/--
Activation Tensors for GPT-2.
*WARNING:* Storing full `attWeights` (`[L, B, NH, T, T]`) is extremely memory intensive
           and impractical for large `T`. Real implementations use streaming/blocking.
           `preatt` has been removed due to memory redundancy.
-/
structure ActivationTensors (s : Type) where
  encoded : TensorView s
  ln1 : TensorView s; ln1Mean : TensorView s; ln1Rstd : TensorView s
  qkv : TensorView s
  -- preatt removed
  attWeights : TensorView s -- Renamed from `att` to clarify it holds probabilities/weights
  attproj : TensorView s
  residual2 : TensorView s
  ln2 : TensorView s; ln2Mean : TensorView s; ln2Rstd : TensorView s
  fch : TensorView s; fchGelu : TensorView s; fcproj : TensorView s
  residual3 : TensorView s
  lnf : TensorView s; lnfMean : TensorView s; lnfRstd : TensorView s
  logits : TensorView s; probs : TensorView s; losses : TensorView s -- Losses might be scalar per batch/token? Shape [B, T] ok.
  deriving Repr -- Assuming TensorView Repr exists

structure GPT2 (s : Type) where -- Unchanged structure
  config : Config
  paramsMemoryRef : ST.Ref s ByteArray; gradsMemoryRef : ST.Ref s ByteArray
  actsMemoryRef : ST.Ref s ByteArray; gradsActsMemoryRef : ST.Ref s ByteArray
  mMemoryRef : ST.Ref s ByteArray; vMemoryRef : ST.Ref s ByteArray
  params : ParameterTensors s; grads : ParameterTensors s
  acts : ActivationTensors s; gradsActs : ActivationTensors s
  numParameters : Nat; numActivations : Nat
  -- Proofs about buffer sizes could be stored here if needed outside init
  deriving Repr -- Assuming component Repr instances exist

-- Repr instances for ParameterTensors, ActivationTensors, GPT2 (Assume they adapt to TensorView Repr)

-- == Section 5: Initialization Logic with Enhanced Safety ==

/-- Helper to calculate total elements and check shape validity. -/
def calculateLayout (shapeList : List (String × Array Nat))
  : Except TensorError (List (String × Array Nat × Nat × Nat) × Nat) := Id.run do
  let mut currentOffsetBytes := 0
  let mut viewInfo : List (String × Array Nat × Nat × Nat) := [] -- name, shape, offset, elementCount
  let mut totalElementCount : Nat := 0
  for (name, shape) in shapeList do
    -- Basic dimension validation (>0)
    let ⟨rank, h_dims_pos, _⟩ ← match validateShape shape with
      | .ok res => pure res
      | .error e => return Except.error e
    -- Check alignment (trivial here as offsets accumulate based on sizeBytes)
    unless currentOffsetBytes % bytesPerFloat = 0 do
       -- This should be impossible if bytesPerFloat is constant and sizes are multiples
       panic! "Internal error: Misaligned offset during layout calculation"
    let elementCount := shape.foldl (· * ·) 1 -- Uses validated shape implicitly
    let viewSizeBytes := elementCount * bytesPerFloat
    viewInfo := (name, shape, currentOffsetBytes, elementCount) :: viewInfo
    currentOffsetBytes := currentOffsetBytes + viewSizeBytes
    totalElementCount := totalElementCount + elementCount
  let totalBytesRequired := currentOffsetBytes
  -- Check total size divisibility
  unless totalBytesRequired % bytesPerFloat = 0 do
    -- Should be impossible by construction
    panic! "Internal error: Total bytes not divisible by bytesPerFloat"

  return (viewInfo.reverse, totalBytesRequired)

/-- Creates a buffer reference and validated tensor views at specified offsets. -/
def createBufferAndViews (s : Type) (shapeList : List (String × Array Nat)) :
    ST s (Except TensorError (ST.Ref s ByteArray × List (String × TensorView s))) := do
  -- Calculate layout and total size, performing initial validation
  let (viewLayout, totalBytesRequired) ← match calculateLayout shapeList with
    | .ok res => pure res
    | .error e => return Except.error e

  -- Initialize buffer
  let bufferData := ByteArray.mkArray (Array.replicate totalBytesRequired 0) -- Efficient init?
  let bufferRef ← ST.mkRef bufferData

  -- Create views using mkUnsafe, relying on calculateLayout's validation
  let mut views : List (String × TensorView s) := []
  let storageSize := totalBytesRequired -- Size is fixed now
  for (name, shape, offsetBytes, _) in viewLayout do
    -- Re-validate shape (could pass proof from calculateLayout)
    let ⟨rank, h_dims_pos, _⟩ ← match validateShape shape with | .ok r => pure r | .error e => panic! "Shape validation mismatch"
    -- Re-validate alignment (could pass proof)
    let h_offset_aligned : offsetBytes % bytesPerFloat = 0 := by sorry -- Proof: follows from layout logic
    -- Create view (bounds validity h_valid is implicitly true by construction here)
    let view := TensorView.mkUnsafe s shape rank bufferRef offsetBytes h_offset_aligned h_dims_pos
    views := (name, view) :: views

  return Except.ok (bufferRef, views.reverse)


-- findView, buildParamTensors, buildActTensors adapted for Except and new Activation structure
def findView {s : Type} (views : List (String × TensorView s)) (name : String) :
    Except TensorError (TensorView s) :=
  match views.find? (·.1 == name) with
  | some (_, view) => Except.ok view
  | none => Except.error (TensorError.nameNotFound name)

-- Simplified buildParamTensors using Except monad
def buildParamTensors {s : Type} (views : List (String × TensorView s)) :
    Except TensorError (ParameterTensors s) := do
  let wte ← findView views "wte"; let wpe ← findView views "wpe"
  let ln1w ← findView views "ln1w"; let ln1b ← findView views "ln1b"
  -- ... find all other param views ...
  let fcprojw ← findView views "fcprojw"; let fcprojb ← findView views "fcprojb"
  let lnfw ← findView views "lnfw"; let lnfb ← findView views "lnfb"
  return ParameterTensors.mk wte wpe ln1w ln1b sorry sorry sorry sorry sorry sorry sorry sorry fcprojw fcprojb lnfw lnfb -- Fill in sorries

-- Simplified buildActTensors using Except monad and updated names/structure
def buildActTensors {s : Type} (views : List (String × TensorView s)) :
    Except TensorError (ActivationTensors s) := do
  let encoded ← findView views "encoded"
  let ln1 ← findView views "ln1"; let ln1Mean ← findView views "ln1Mean"; let ln1Rstd ← findView views "ln1Rstd"
  let qkv ← findView views "qkv"
  let attWeights ← findView views "attWeights" -- Updated name
  let attproj ← findView views "attproj"
  -- ... find all other act views ...
  let logits ← findView views "logits"; let probs ← findView views "probs"; let losses ← findView views "losses"
  return ActivationTensors.mk encoded ln1 ln1Mean ln1Rstd qkv attWeights attproj sorry ln2 sorry ln2Mean ln2Rstd sorry sorry fcproj sorry lnf lnfMean lnfRstd logits probs losses -- Fill in sorries


-- createParameterShapes (unchanged)
def createParameterShapes (config : Config) : List (String × Array Nat) :=
  -- ... same as before ...
  sorry

-- createActivationShapes (UPDATED for memory warning/changes)
def createActivationShapes (config : Config) (B : Nat) (T : Nat) : List (String × Array Nat) :=
  let L := config.numLayers; let C := config.channels
  let V := config.paddedVocabSize; let NH := config.numHeads
  [
    ("encoded",  #[B, T, C]),     ("ln1",      #[L, B, T, C]), ("ln1Mean",  #[L, B, T]),
    ("ln1Rstd",  #[L, B, T]),     ("qkv",      #[L, B, T, 3*C]),
    -- ("preatt",   #[L, B, NH, T, T]), -- REMOVED: Memory duplication
    ("attWeights", #[L, B, NH, T, T]),-- RENAMED (Warning: T*T memory!)
    ("attproj", #[L, B, T, C]), ("residual2",#[L, B, T, C]),
    ("ln2",      #[L, B, T, C]), ("ln2Mean",  #[L, B, T]),    ("ln2Rstd",  #[L, B, T]),
    ("fch",      #[L, B, T, 4*C]),("fchGelu",  #[L, B, T, 4*C]),("fcproj",   #[L, B, T, C]),
    ("residual3",#[L, B, T, C]), ("lnf",      #[B, T, C]),    ("lnfMean",  #[B, T]),
    ("lnfRstd",  #[B, T]),       ("logits",   #[B, T, V]),    ("probs",    #[B, T, V]),
    ("losses",   #[B, T]) -- Assuming batch/token losses
  ]

-- createOptimizerMemory (unchanged)
def createOptimizerMemory (s : Type) (numBytes : Nat) :
    ST s (ST.Ref s ByteArray × ST.Ref s ByteArray) := do
  -- ... same as before ...
  sorry

/-- Initializes a GPT2 model, now returning `Except TensorError`. -/
def GPT2.init (s : Type) (config : Config) (B : Nat := 1) (T : Nat := 1) :
    ST s (Except TensorError (GPT2 s)) := do

  -- Check B, T positivity (basic sanity)
  unless B > 0 && T > 0 do return Except.error (TensorError.negativeDimension #[B, T]) -- Simplified error type use

  let shapesP := createParameterShapes config
  let shapesA := createActivationShapes config B T

  -- Use Except for buffer/view creation
  let (paramsMemRef, paramViewsList) ← EStateT.run (createBufferAndViews s shapesP) ()
  let (gradsMemRef, gradViewsList) ← EStateT.run (createBufferAndViews s shapesP) ()
  let (actsMemRef, actViewsList) ← EStateT.run (createBufferAndViews s shapesA) ()
  let (gradsActsMemRef, gradActViewsList) ← EStateT.run (createBufferAndViews s shapesA) ()

  -- Check results of buffer creation
  match paramsMemRef, gradsMemRef, actsMemRef, gradsActsMemRef with
  | .ok (pRef, pViews), .ok (gRef, gViews), .ok (aRef, aViews), .ok (gaRef, gaViews) =>
      -- Build tensors using Except
      let buildResult := do
        let params ← buildParamTensors pViews
        let grads ← buildParamTensors gViews
        let acts ← buildActTensors aViews
        let gradsActs ← buildActTensors gaViews
        return (params, grads, acts, gradsActs)

      match buildResult with
      | .error e => return Except.error e -- Propagate findView/build errors
      | .ok (params, grads, acts, gradsActs) =>
          -- Calculate sizes and perform final checks
          let paramBuffer ← ST.Ref.get pRef
          let numParamsBytes := paramBuffer.size
          -- Check divisibility rigorously
          unless numParamsBytes % bytesPerFloat == 0 do
             return Except.error (TensorError.bufferSizeNotDivisible numParamsBytes bytesPerFloat)
          let numParamsElements := numParamsBytes / bytesPerFloat
          -- TODO: Add check: numParamsElements == sum of element counts from shapesP?

          let actBuffer ← ST.Ref.get aRef
          let numActsBytes := actBuffer.size
          unless numActsBytes % bytesPerFloat == 0 do
             return Except.error (TensorError.bufferSizeNotDivisible numActsBytes bytesPerFloat)
          let actsElementsCount := numActsBytes / bytesPerFloat
           -- TODO: Add check: actsElementsCount == sum of element counts from shapesA?

          -- Create optimizer memory
          let (mMemRef, vMemRef) ← createOptimizerMemory s numParamsBytes

          -- Assemble final GPT2 structure
          return Except.ok {
            config := config,
            paramsMemoryRef := pRef, gradsMemoryRef := gRef,
            actsMemoryRef := aRef, gradsActsMemoryRef := gaRef,
            mMemoryRef := mMemRef, vMemoryRef := vMemRef,
            params := params, grads := grads,
            acts := acts, gradsActs := gradsActs,
            numParameters := numParamsElements,
            numActivations := actsElementsCount
          }
  | .error e, _, _, _ => return Except.error e -- Propagate buffer creation errors
  | _, .error e, _, _ => return Except.error e
  | _, _, .error e, _ => return Except.error e
  | _, _, _, .error e => return Except.error e


/-- Placeholder for theorem: total size of views matches buffer size. -/
lemma check_buffer_size_matches_layout (shapeList : List (String × Array Nat)) (buffer : ByteArray) :
  (calculateLayout shapeList).bind (fun (_, totalBytes) => if buffer.size == totalBytes then .ok () else .error TensorError.bufferSizeMismatch) = .ok () := by sorry

--
