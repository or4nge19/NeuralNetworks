import NeuralNetworks.LLM.GPT2.Core
import NeuralNetworks.LLM.GPT2.ByteArrayUtils
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Array.Extract
import Mathlib.Data.Nat.Lattice

open LLM.GPT2 -- For Core types like TensorError, bytesPerFloat
open Batteries

namespace LLM.GPT2

-- == Section 3: TensorView Structure and Safety ==

/--
A view into a tensor stored in a ByteArray. Represents a multi-dimensional tensor with a specific
shape, stored in a ByteArray at a given byte offset. The view doesn't own the data but provides
safe access methods to it.
-/
structure TensorView (s : Type) where
  /-- Shape of the tensor, as an array of dimension sizes. Validated > 0. -/
  shape : Array Nat
  /-- Rank (number of dimensions). `shape.size`. -/
  rank : Nat
  /-- Proof that rank equals the size of shape. -/
  h_rank_eq_size : rank = shape.size
  /-- Reference to the underlying storage ByteArray containing the tensor data. -/
  storageRef : ST.Ref s ByteArray
  /-- Byte offset in the storage where this tensor view begins. Proven aligned to `bytesPerFloat`. -/
  offsetBytes : Nat
  /-- Proof that offsetBytes is aligned. -/
  h_offset_aligned : offsetBytes % bytesPerFloat = 0
  /-- Proof that all dimensions in shape are positive. -/
    h_dims_positive : ∀ (i : Fin rank), shape[i.val]'(by {
        have h1 : i.val < rank := i.isLt
        have h2 : rank = shape.size := h_rank_eq_size
        exact Nat.lt_of_lt_of_eq h1 h2
      }) > 0
  -- No Inhabited instance needed or desirable

/-- Total number of elements in the tensor view. Guaranteed > 0 since dims > 0. -/
@[inline] def TensorView.elementCount {s : Type} (tv : TensorView s) : Nat :=
  -- Foldl starts with 1, and all shape[i] > 0, so result > 0
  tv.shape.foldl (· * ·) 1

namespace Array

/--
If an index `i` is within the bounds of an array `arr`, then `arr[i]!` (unsafe get)
is equal to `arr[i]` (safe get, written as `arr[i]'h_bounds`).
-/
lemma getElem_eq_get! {α : Type} [Inhabited α] {arr : Array α} {i : Nat} (h_bounds : i < arr.size) :
    arr[i]! = arr[i]'h_bounds := by
  rw [getElem!_pos arr i h_bounds]

end Array

lemma exists_index_of_mem_with_get_bang
    {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    {arr : Array α} {x : α} (h_mem : x ∈ arr) :
    ∃ i : Nat, i < arr.size ∧ arr[i]! = x := by
  rcases Array.getElem_of_mem h_mem with ⟨i, h_i_lt, h_get⟩
  have h_get_bang : arr[i]! = x := by
    rw [Array.getElem_eq_get! h_i_lt]
    exact h_get
  exact ⟨i, h_i_lt, h_get_bang⟩

/-- Proof that the element count is positive. -/
lemma TensorView.elementCount_pos {s : Type} (tv : TensorView s) : tv.elementCount > 0 := by
  rw [TensorView.elementCount]
  have h_array_to_list : tv.shape.foldl (· * ·) 1 = List.foldl (· * ·) 1 tv.shape.toList := by
    simp only [Array.foldl_toList, Array.toListImpl_eq]
  rw [h_array_to_list]
  have h : List.foldl (· * ·) 1 tv.shape.toList = tv.shape.toList.prod := by
    exact (List.prod_eq_foldl (l := tv.shape.toList)).symm
  rw [h]
  apply List.prod_pos
  intro x hx_mem_list
  have h_mem := @Array.mem_toList_iff Nat x tv.shape
  have h_x_in_array : x ∈ tv.shape := by
    rw [← Array.mem_toList_iff]
    exact hx_mem_list
  have h_exists_idx : ∃ i < tv.shape.size, tv.shape[i]! = x := by
    have : ∃ i, i < tv.shape.size ∧ tv.shape[i]! = x := by
      by_contra h_no_idx
      simp only [not_exists, not_and] at h_no_idx
      have h_x_not_in : x ∉ tv.shape := by
        intro h_in
        have h_exists : ∃ i, i < tv.shape.size ∧ tv.shape[i]! = x :=
          exists_index_of_mem_with_get_bang h_x_in_array
        rcases h_exists with ⟨i, h_i_lt, h_x_eq⟩
        specialize h_no_idx i
        exact h_no_idx h_i_lt h_x_eq
      exact h_x_not_in h_x_in_array
    rcases this with ⟨i, h_i_lt, h_eq⟩
    exact ⟨i, h_i_lt, h_eq⟩
  rcases h_exists_idx with ⟨i, h_i_lt, h_x_eq⟩
  rw [← h_x_eq]
  have h_i_lt_rank : i < tv.rank := by { rw [tv.h_rank_eq_size]; exact h_i_lt }
  let fin_i_rank : Fin tv.rank := ⟨i, h_i_lt_rank⟩
  have h_get_eq_get_bang : tv.shape[fin_i_rank] = tv.shape[i]! := by
    exact Eq.symm (getElem!_pos tv.shape i h_i_lt)
  have h_pos : tv.shape[fin_i_rank] > 0 := tv.h_dims_positive fin_i_rank
  rw [h_get_eq_get_bang] at h_pos
  exact h_pos

/-- Total size in bytes of this tensor view. Guaranteed divisible by `bytesPerFloat`. -/
@[inline] def TensorView.sizeBytes {s : Type} (tv : TensorView s) : Nat :=
  tv.elementCount * bytesPerFloat

/-- Proof that sizeBytes is a multiple of bytesPerFloat. -/
lemma TensorView.sizeBytes_dvd {s : Type} (tv : TensorView s) : bytesPerFloat ∣ tv.sizeBytes := by
  simp [sizeBytes];

/-- Proof that the view fits within the storage, derived from creation. -/
structure TensorView.ValidView {s : Type} (tv : TensorView s) (storageSize : Nat) where
  h_valid : tv.offsetBytes + tv.sizeBytes <= storageSize

/-- Internal helper to validate shape dimensions. -/
def validateShape (shape : Array Nat) : Except TensorError (Nat × (Nat → Prop)) := Id.run do
  if shape.isEmpty then
    -- Allow scalar tensors (rank 0)
    return Except.ok (0, fun _ => True)
  else
    -- Check each dimension
    for i in [:shape.size] do
      if shape[i]! == 0 then return Except.error (TensorError.negativeDimension shape)
    -- If loop completes, all dimensions are positive
    let rank := shape.size
    -- Return the rank and a predicate that validates indices
    return Except.ok (rank, fun i => i < rank → shape[i]! > 0)

/-- Creates a TensorView assuming validation and checks passed during buffer construction. -/
@[inline]
def TensorView.mkUnsafe (s : Type) (shape : Array Nat) (rank : Nat) (storageRef : ST.Ref s ByteArray)
    (offsetBytes : Nat) (h_offset_aligned : offsetBytes % bytesPerFloat = 0)
    (h_rank_eq_size : rank = shape.size)
    (h_dims_positive : ∀ (i : Fin rank), shape[i.val]'(by
        rw [← h_rank_eq_size]
        exact i.isLt) > 0) : TensorView s :=
  { shape, rank, storageRef, offsetBytes, h_offset_aligned, h_dims_positive, h_rank_eq_size }

protected def TensorView.reprPrec {s : Type} (tv : TensorView s) (_prec : Nat) : Std.Format :=
  let shapeStr := toString tv.shape
  let rankStr := toString tv.rank
  let offsetStr := toString tv.offsetBytes
  Std.Format.bracket "TensorView(" (Std.Format.text ("shape: " ++ shapeStr ++ ",
    rank: " ++ rankStr ++ ", offsetBytes: " ++ offsetStr)) ")"

instance (s : Type) : Repr (TensorView s) where
  reprPrec := TensorView.reprPrec

/--
Helper function for computing flat indices. Processes the dimensions in reverse order
(from least significant to most significant).
-/
def computeHelper (shape : Array Nat) (rank : Nat) (indices : Array Nat)
                  (i_rev : Nat) (flatIndexRel : Nat) (stride : Nat)
                  : Except TensorError Nat :=
  if i_rev >= rank then
    Except.ok flatIndexRel
  else
    let i := rank - 1 - i_rev
    let index := indices[i]!
    let dimSize := shape[i]!
    if index >= dimSize then
      Except.error (TensorError.indexOutOfBounds indices shape)
    else
      let newFlatIndex := flatIndexRel + index * stride
      let newStride := stride * dimSize
      computeHelper shape rank indices (i_rev + 1) newFlatIndex newStride
termination_by rank - i_rev

/--
Computes the flat index relative to the start of the tensor view.
Returns an error if dimensions mismatch or indices are out of bounds.
Requires proof that shape dimensions are positive.
-/
@[inline]
def computeFlatIndex (shape : Array Nat) (rank : Nat)
                     (h_rank_eq_size : rank = shape.size)
                     (_ : ∀ (i : Fin rank), shape[i.val]'(by {
                        have h1 : i.val < rank := i.isLt
                        have h2 : rank = shape.size := h_rank_eq_size
                        exact Nat.lt_of_lt_of_eq h1 h2
                      }) > 0)
                     (indices : Array Nat) : Except TensorError Nat :=
  if indices.size != rank then
    Except.error (TensorError.shapeMismatch rank indices.size)
  else
    computeHelper shape rank indices 0 0 1
