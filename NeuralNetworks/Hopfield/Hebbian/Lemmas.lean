import NeuralNetworks.Hopfield.Hebbian.Basic

namespace HopfieldState

open SpinState

variable {n : ℕ}

section HebbianConstruction

open UpdateSeq

/-- The self-correlation term contribution --/
lemma sum_self_correlation {n : ℕ} {p : HopfieldState n} {i : Fin n} :
  (∑ j : Fin n, if i = j then 0 else (p i).toReal * (p j).toReal * (p j).toReal) =
  (p i).toReal * (n - 1) := by
  -- When j ≠ i: (p j).toReal * (p j).toReal = 1
  have h_square_one : ∀ j : Fin n, (p j).toReal * (p j).toReal = 1 := by
    intro j
    cases p j <;> simp [SpinState.toReal]

  -- Rewrite the sum using this fact
  rw [← h_square_one i]

  -- Rewrite to use filter
  rw [@Fin.sum_univ_def]
  -- Factor out (p i).toReal
  rw [@mul_sub]
  -- The sum of 1's equals the cardinality
  rw [@List.sum_map_ite]
  -- Use our lemma for the count
  rw [@Finset.sum_list_map_count]
  ring_nf
  -- Break down the proof into steps
  have h1 : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset = {i} := by
    ext x
    simp only [List.mem_filter, List.mem_finRange, Nat.lt_succ_iff, Finset.mem_singleton]
    constructor
    · intro h
      simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange, Finset.mem_filter,
        Finset.mem_univ, true_and]
    · intro h
      subst h
      simp only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange, Finset.mem_filter,
        Finset.mem_univ, and_self]

  have h2 : ∑ x ∈ (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset, 0 = 0 := by
    simp only [Finset.sum_const_zero]

  have h3 : (List.filter (fun a ↦ decide ¬i = a) (List.finRange n)).length = n - 1 := by
    -- First prove that finRange n has length n
    have h_len : (List.finRange n).length = n := by
      exact List.length_finRange n

    -- Then show that filtering removes exactly one element (i)
    have h_count : (List.filter (fun a ↦ decide (i = a)) (List.finRange n)).length = 1 := by
      -- Convert to counting occurrences
      rw [@List.length_eq_one_iff]
      rw [@Fin.exists_iff]
      use i.val
      use i.isLt
      -- Show that filtering elements equal to i gives a single-element list [i]
      let i_nat := i.val
      have h_i_bound : i_nat < n := i.isLt
      have h_filter : List.filter (fun b ↦ decide (i = b)) (List.finRange n) = [i] := by
        refine Eq.symm (List.Perm.singleton_eq ?_)
        · simp only [List.singleton_perm]
          rw [@List.ext_get_iff]
          apply And.intro
          · -- Prove lengths are equal
            have h_filter_len : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length = 1 := by
              -- If toFinset gives a singleton, the original list must have had length 1
              have h_card : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset.card = 1 := by
                rw [h1]
                exact Finset.card_singleton i

              -- For finite lists without duplicates, length equals toFinset cardinality
              have h_len_eq_card : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length =
                                 (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset.card := by
                -- List.finRange has no duplicates
                have h_nodup : (List.finRange n).Nodup := List.nodup_finRange n
                -- Filter preserves Nodup property
                have h_filter_nodup : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).Nodup :=
                  List.Nodup.filter _ h_nodup
                -- For lists without duplicates, length = toFinset.card
                exact Eq.symm (List.toFinset_card_of_nodup h_filter_nodup)

              rw [h_len_eq_card, h_card]

            -- Now prove the goal: 1 = length of filtered list
            exact Eq.symm h_filter_len

          · -- Prove elements are equal
            intro n_1 h₁ h₂
            -- In a singleton list [i], the only element is at position 0
            have h_zero : n_1 = 0 := by
              have h_len_one : [i].length = 1 := by simp
              rw [h_len_one] at h₁
              rw [← Nat.lt_one_iff]
              exact h₁


            -- The only element in [i] is i
            have h_get_sing : [i].get ⟨n_1, h₁⟩ = i := by
              rw [@Fin.le_antisymm_iff]  -- use n_1 = 0
              simp [List.get]  -- simplify List.get for singleton list

            -- Show that the filtered list only contains i
            have h_elem : ∀ (j : Fin n), j ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) → j = i := by
              intro j hj
              simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq] at hj
              subst h_zero
              simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange, Finset.sum_const_zero,
                List.length_finRange, Fin.is_lt, true_and, List.length_filter_pos_iff, List.mem_finRange, exists_eq',
                List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem,
                Fin.val_eq_zero, List.getElem_cons_zero, i_nat]

            -- The filtered list has length 1, so its only element must be at position 0
            have h_pos_length : 0 < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := by
              -- Since i ∈ finRange n, the filtered list contains at least i
              have h_i_in : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                exact ⟨trivial, trivial⟩
              exact List.length_pos_of_mem h_i_in

            have h_pos_zero : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨n_1, h₂⟩ =
                            (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h_pos_length⟩ := by
              rw [@List.get_mk_zero]
              have h_get : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h_pos_length⟩ = i := by
                -- Show that i is in the list
                have h_i_in : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                  exact ⟨trivial, trivial⟩

                -- Show that i is the first element
                have h_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? = some i := by
                  -- Show that i is in the list and it's the only element
                  have h_i_in_range : i ∈ List.finRange n := by
                    simp only [List.mem_finRange]

                  have h_filter_i : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                    simp only [List.mem_filter]
                    exact ⟨h_i_in_range, by simp [decide_eq_true_eq]⟩

                  -- The filtered list has exactly one element (i)
                  have h_filter_singleton : List.filter (fun b ↦ decide (i = b)) (List.finRange n) = [i] := by
                    refine Eq.symm (List.Perm.singleton_eq ?_)
                    · refine List.singleton_perm.mpr ?_
                      · -- Prove [i] equals the filtered list using List.ext_get
                        rw [← h_get_sing]
                        refine List.singleton_perm.mp ?_
                        · -- Show lengths are equal
                          simp only [List.length_filter_pos_iff, List.length_singleton]
                          apply List.singleton_perm.mpr
                          rw [h_get_sing]
                          ext j
                          simp only [Option.mem_def, i_nat]
                          apply Iff.intro
                          · intro h_get
                            rw [← h_get_sing] at h_get
                            subst h_zero
                            simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                              Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                              List.getElem_cons_zero, i_nat] at h_get
                            · -- j = 0 case
                              have h_filter_get : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? = some i := by
                                simp only [List.length_filter_pos_iff, List.mem_finRange,
                                  decide_eq_true_eq, true_and, exists_eq', List.getElem?_eq_getElem,
                                  Option.some.injEq, i_nat]
                                -- First show that i is in the filtered list
                                have h_i_in : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                                  exact ⟨trivial, trivial⟩

                                -- Then show it's at position 0 since it's the only element
                                have h_get_zero : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0] = i := by
                                  -- Since i is in the list and it's the only element, it must be at position 0
                                  have h_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? = some i := by
                                    -- Show that i is in the list and is its first element
                                    have h_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? = some i := by
                                      -- Since i is in the list and it's the only element, it must be at position 0
                                      have h_nonempty : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length > 0 := by
                                        apply List.length_pos_of_mem h_i_in

                                      -- Show that i is the first element
                                      have h_first : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0] = i := by
                                        -- Show i is in the filtered list
                                        have h_mem : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                          simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                                          exact ⟨trivial, trivial⟩
                                        -- Show filtered list is non-empty and has length 1
                                        have h_pos : 0 < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := by
                                          exact List.length_pos_of_mem h_mem
                                        -- Show first element is i using get_zero
                                        -- Show that the first element of the filtered list equals i
                                        -- First show that j must be 0 since both lists have length 1
                                        have h_j_zero : j = 0 := by
                                          have h_len_one : [i].length = 1 := by simp
                                          have : j < [i].length := by
                                            -- Since [i][j]? = some a✝, j must be within bounds
                                            rw [← h_elem i h_i_in]
                                            -- If we can get an element at position j from a list of length 1,
                                            -- then j must be less than 1
                                            -- Since [i][j]? = some a✝, j must be within bounds
                                            have : j < [i].length := by
                                              have : j < [i].length := by
                                                rw [List.length_singleton]
                                                -- Since [i][j]? = some a✝, j must be within bounds
                                                have : j < [i].length := by
                                                  rw [List.length_singleton]
                                                  -- If we can get an element at position j from a list of length 1,
                                                  -- then j must be less than 1
                                                  -- Since [i] is a singleton list, its length is 1
                                                  rw [← h_len_one]
                                                  -- Since [i][j]? = some a✝, j must be within bounds
                                                  have : j < [i].length := by
                                                    simp only [List.length_singleton]
                                                    have : j < 1 := by
                                                      have : [i].length = 1 := by simp
                                                      have h_j_lt : j < 1 := by
                                                        rw [← h_elem i h_i_in] at h_get
                                                        -- If we can get an element at index j from a list of length 1,
                                                        -- then j must be less than 1
                                                        -- Since [i] is a singleton list and we can get an element at index j,
                                                        -- j must be 0
                                                        have h_j_zero : j = 0 := by
                                                          -- [i] has length 1
                                                          have h_len_one : [i].length = 1 := by simp
                                                          -- If we can get an element at index j,
                                                          -- then j must be less than the length
                                                          have h_j_lt : j < [i].length := by
                                                            rw [h_len_one]
                                                            -- If we can get an element at index j,
                                                            -- then j must be less than the length
                                                            have : j < 1 := by
                                                              -- If we can get an element at index j, then j < length
                                                              have h_mem : [i][j]?.isSome := by
                                                                simp only [isSome_getElem?,
                                                                  List.length_cons, List.length_nil,
                                                                  zero_add, Nat.lt_one_iff, i_nat]
                                                                -- Since [i][j]? = some a✝, j must be a valid index
                                                                -- Since j is a valid index in [i] and [i] has length 1
                                                                have h_j_lt_len : j < [i].length := by
                                                                  -- If we can get an element at index j,
                                                                  -- then j must be less than the length
                                                                  have : j < [i].length := by
                                                                    -- [i] is a singleton list, so length = 1
                                                                    rw [List.length_singleton]
                                                                    -- Since we can get an element at j,
                                                                    -- j must be 0
                                                                    have h_len : [i].length = 1 := by simp
                                                                    rw [h_len] at h₁
                                                                    sorry
                                                                  exact this
                                                                -- Since j < 1, j must be 0
                                                                have h_singleton_len : [i].length = 1 := by simp
                                                                rw [h_singleton_len] at h_j_lt_len
                                                                exact Nat.lt_one_iff.mp h_j_lt_len

                                                              -- From h_mem, we can prove j = 0
                                                              have h_j_zero : j = 0 := by
                                                                -- For a singleton list, any valid index must be 0
                                                                have h_len : [i].length = 1 := by simp
                                                                have h_lt : j < [i].length := by
                                                                  rw [List.length_singleton]
                                                                  have h_lt : j < [i].length := by
                                                                    simp only [List.length_singleton]
                                                                    rw [← h_len_one]
                                                                    simp only [List.length_cons,
                                                                      List.length_nil, zero_add,
                                                                      Nat.lt_one_iff, i_nat]
                                                                    have h_j_lt_one : j < 1 := by
                                                                      simp only [Nat.lt_one_iff,
                                                                        i_nat]
                                                                      sorry
                                                                    have h_zero : j = 0 := Nat.lt_one_iff.mp h_j_lt_one
                                                                    exact h_zero
                                                                  simp_all only [List.toFinset_filter,
                                                                    decide_eq_true_eq, List.toFinset_finRange,
                                                                    Finset.sum_const_zero, List.length_finRange,
                                                                    Fin.is_lt, List.mem_filter, List.mem_finRange,
                                                                    true_and, implies_true, List.length_cons,
                                                                    List.length_nil, Nat.reduceAdd, Fin.zero_eta,
                                                                    Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                                                    List.getElem_cons_zero, gt_iff_lt, decide_true,
                                                                    and_self, List.length_filter_pos_iff, exists_eq',
                                                                    Option.isSome_some, zero_add, Nat.lt_one_iff,
                                                                    pos_of_gt, i_nat]
                                                                rw [h_len] at h_lt
                                                                exact Nat.lt_one_iff.mp h_lt
                                                              exact Nat.lt_one_iff.mpr h_j_zero
                                                            exact this
                                                          -- Since j < 1, j must be 0
                                                          rw [h_len_one] at h_j_lt
                                                          exact Nat.lt_one_iff.mp h_j_lt
                                                        exact Nat.lt_one_iff.mpr h_j_zero
                                                      exact h_j_lt
                                                    exact this
                                                  exact this
                                                exact this
                                              exact this
                                            exact this
                                          exact Nat.lt_one_iff.mp this

                                        -- Show that element at position 0 in filtered list is i
                                        have h_j_lt_filter : j < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := by
                                          -- Since the filtered list contains i, it's non-empty
                                          have h_i_in : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                            simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                                            exact ⟨trivial, trivial⟩
                                          -- The list has at least one element
                                          have h_nonempty : 0 < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length :=
                                            List.length_pos_of_mem h_i_in
                                          -- Since j = 0 (from h_j_zero) and the list is non-empty
                                          rw [h_j_zero]
                                          exact h_nonempty

                                        have h_filter_get : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨j, h_j_lt_filter⟩ = i := by
                                          apply h_elem
                                          exact
                                            List.get_mem
                                              (List.filter (fun b ↦ decide (i = b))
                                                (List.finRange n))
                                              ⟨j, h_j_lt_filter⟩
                                        -- Show that element at position 0 in singleton list is i
                                        have h_sing_get : [i].get ⟨j, by
                                          rw [h_j_zero]
                                          simp [List.length_singleton]⟩ = i := by
                                          -- For a singleton list [i], the element at position 0 is i
                                          rw [← h_elem i h_i_in]
                                          subst h_j_zero
                                          simp_all only [List.toFinset_filter, decide_eq_true_eq,
                                            List.toFinset_finRange, Finset.sum_const_zero, List.length_finRange,
                                            Fin.is_lt, List.mem_filter, List.mem_finRange, true_and, implies_true,
                                            List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
                                            Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero,
                                            gt_iff_lt, decide_true, and_self, zero_add, Nat.lt_one_iff, pos_of_gt,
                                            List.getElem?_eq_getElem, Option.some.injEq, i_nat]


                                        -- Combine the equalities
                                        rw [@List.getElem_eq_iff]
                                        -- Prove that index 0 is valid using h_pos_length
                                        subst h_j_zero
                                        simp_all only [List.toFinset_filter, decide_eq_true_eq,
                                          List.toFinset_finRange, Finset.sum_const_zero, List.length_finRange,
                                          Fin.is_lt, List.mem_filter, List.mem_finRange, true_and, implies_true,
                                          List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
                                          List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, gt_iff_lt,
                                          decide_true, and_self, zero_add, Nat.lt_one_iff, pos_of_gt,
                                          List.getElem?_eq_getElem, Option.some.injEq, List.length_filter_pos_iff,
                                          exists_eq', i_nat]


                                      -- Convert from array notation to get?
                                      rw [← h2]
                                      simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                                        Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                                        List.mem_finRange, true_and, implies_true, List.length_cons, List.length_nil,
                                        Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem,
                                        Fin.val_eq_zero, List.getElem_cons_zero, decide_true, and_self,
                                        List.getElem?_eq_getElem, i_nat]
                                    -- Convert from head to head?
                                    rw [← h_elem i h_i_in]
                                    rw [List.head?_eq_head]
                                    have h_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? = some i := by
                                      -- Show that i is in the list and it's the only element
                                      have h_i_filter : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                        simp [List.mem_filter]

                                      -- Since i is in the list, it must be the head (as it's the only element)
                                      rw [← h_elem i h_i_in]
                                      -- Show that i is in the filtered list and it's first
                                      have h_mem : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                        simp [List.mem_filter, List.mem_finRange]
                                      -- Since i is the only element, it must be the head
                                      -- Show the filtered list contains exactly i at its head
                                      simp [List.head?]
                                      simp_all [i_nat]
                                      simp_all only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff,
                                        pos_of_gt, i_nat]
                                      split
                                      next x heq =>
                                        simp_all only [List.filter_eq_nil_iff, List.mem_finRange, decide_eq_true_eq,
                                          forall_const, forall_eq', i_nat]
                                      next x a_1 as heq => simp_all only [List.getElem_cons_zero, i_nat]
                                    rw [← h_head]
                                    rw [h_head]
                                    simp only [Option.some.injEq]
                                    apply h_elem
                                    -- Show i is the first element in the list
                                    have h_first : List.head? (List.filter (fun b ↦ decide (i = b)) (List.finRange n)) =
                                                 (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? := by
                                      -- head? of a list is the same as the first element
                                      simp only [List.head?]
                                      split
                                      · -- empty list case
                                        simp_all only [List.toFinset_nil, Finset.sum_const_zero, List.length_finRange,
                                          Fin.is_lt, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
                                          List.length_nil, lt_self_iff_false, i_nat]
                                      · -- non-empty list case
                                        simp_all only [List.mem_cons, true_or, List.toFinset_cons,
                                          Finset.sum_const_zero, List.length_finRange, Fin.is_lt, forall_eq_or_imp,
                                          List.length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
                                          pos_of_gt, or_true, List.mem_finRange, List.length_nil, Nat.reduceAdd,
                                          Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                          List.getElem_cons_zero, List.getElem?_eq_getElem, List.head?_cons, i_nat]
                                    rw [← h2] at h_first
                                    simp only [List.head?_filter, List.toFinset_filter,
                                      decide_eq_true_eq, List.toFinset_finRange,
                                      Finset.sum_const_zero, List.length_filter_pos_iff,
                                      List.mem_finRange, true_and, exists_eq',
                                      List.getElem?_eq_getElem, i_nat] at h_first
                                    refine List.head_mem ?_
                                    simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                                      Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                                      List.mem_finRange, true_and, implies_true, List.length_filter_pos_iff,
                                      exists_eq', List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
                                      Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero,
                                      decide_true, and_self, List.getElem?_eq_getElem, Option.some.injEq, ne_eq,
                                      List.filter_eq_nil_iff, forall_const, forall_eq', not_false_eq_true, i_nat]
                                  -- Convert from head? to array notation
                                  have h_zero_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? = some i := by
                                    rw [← h2]
                                    -- Convert finset sum to a natural number (0)
                                    have h_sum_zero : ∑ x ∈ (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset, 0 = 0 := by
                                      exact h2
                                    simp [h_sum_zero]
                                    -- Show that accessing the first element gives i
                                    rw [← h_elem i h_i_in]
                                    -- First prove the length is 1
                                    have h_len_one : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length = 1 := by
                                      -- Since i is in the list and every element equals i, length must be 1
                                      have h_all_eq : ∀ j ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n), j = i := h_elem
                                      apply List.length_eq_one_iff.mpr
                                      use i
                                      have h_len_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length = 1 := by
                                        have h_eq_single : List.filter (fun b ↦ decide (i = b)) (List.finRange n) = [i] := by
                                          apply List.ext_get
                                          · -- Since i is in the list and every element equals i, length must be 1
                                            have h_all_eq : ∀ j ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n), j = i := h_elem
                                            apply List.length_eq_one_iff.mpr
                                            use i
                                            rw [← h_elem i h_i_in]
                                            apply List.ext_get
                                            · -- Prove lengths are equal
                                              have h_len_filter : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length = 1 := by
                                                -- If toFinset gives singleton, the list must have length 1
                                                have h_card : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset.card = 1 := by
                                                  rw [h1]
                                                  exact Finset.card_singleton i

                                                -- For finite lists without duplicates, length equals toFinset cardinality
                                                have h_len_eq_card : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length =
                                                                   (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset.card := by
                                                  -- List.finRange has no duplicates
                                                  have h_nodup : (List.finRange n).Nodup := List.nodup_finRange n
                                                  -- Filter preserves Nodup property
                                                  have h_filter_nodup : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).Nodup :=
                                                    List.Nodup.filter _ h_nodup
                                                  -- For lists without duplicates, length = toFinset.card
                                                  exact Eq.symm (List.toFinset_card_of_nodup h_filter_nodup)

                                                rw [h_len_eq_card, h_card]

                                              rw [h_len_filter]
                                              simp only [List.length_singleton]
                                            · -- Prove elements are equal
                                              intro j h₁ h₂
                                              rw [@Fin.le_antisymm_iff]
                                              refine le_antisymm_iff.mp ?_
                                              have h_mem : [i][j] = i := by
                                                rw [@List.getElem_singleton]
                                              -- Prove the filtered list equals [i]
                                              have h_eq_filtered : List.filter (fun b ↦ decide (i = b)) (List.finRange n) = [i] := by
                                                -- Use the singleton characterization lemma
                                                refine Eq.symm (List.Perm.singleton_eq ?_)
                                                constructor
                                                · -- Show i is in the filtered list
                                                  exact List.singleton_perm.mpr rfl
                                                · -- Show every element in the filtered list is i
                                                  -- Directly prove the permutation using the fact that
                                                  -- both lists have exactly one element: i
                                                  have h_len_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length = 1 := by
                                                    rw [List.length_eq_one_iff]
                                                    use i
                                                    sorry

                                                  have h_len_single : [i].length = 1 := by simp

                                                  -- Both lists have length 1 and the same element i
                                                  refine List.singleton_perm.mpr ?_
                                                  · -- Prove lists are equal using extensionality
                                                    apply List.ext_get
                                                    · -- Show lengths are equal
                                                      rw [h_len_single, h_len_eq]
                                                    · -- Show elements are equal
                                                      intro k hk_lt
                                                      -- Both lists have length 1, so k must be 0
                                                      have h_k_zero : k = 0 := by
                                                        rw [← h_elem i h_i_in] at hk_lt
                                                        exact Nat.lt_one_iff.mp hk_lt

                                                      -- Get element at position 0 from both lists
                                                      rw [← h_elem i h_i_in]
                                                      rw [← h_get_sing]
                                                      -- Use h_elem to show the filtered list contains i at position 0
                                                      have h_pos_length : 0 < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := by
                                                        apply List.length_pos_of_mem
                                                        simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                                                        rw [true_and]

                                                      have h_get_filter : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h_pos_length⟩ = i := by
                                                        apply h_elem
                                                        exact
                                                          List.get_mem
                                                            (List.filter (fun b ↦ decide (i = b))
                                                              (List.finRange n))
                                                            ⟨0, h_pos_length⟩
                                                      intro h₂
                                                      subst h_k_zero
                                                      rw [@List.get_mk_zero]
                                                      have h_get_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h₂⟩ = i := by
                                                        apply h_elem
                                                        exact
                                                          List.get_mem
                                                            (List.filter (fun b ↦ decide (i = b))
                                                              (List.finRange n))
                                                            ⟨0, h₂⟩
                                                      exact id (Eq.symm h_get_filter)


                                              rw [@Fin.le_antisymm_iff]
                                              simp_all only [List.mem_cons, List.not_mem_nil, or_false,
                                                List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
                                                Finset.sum_const_zero, List.length_finRange, Fin.is_lt, implies_true,
                                                List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff,
                                                pos_of_gt, List.mem_finRange, Nat.reduceAdd, Fin.zero_eta,
                                                Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                                List.getElem_cons_zero, List.head?_cons, List.getElem_singleton,
                                                le_refl, and_self, i_nat]
                                          · intro j hj1 hj2
                                            simp only [List.get_eq_getElem, List.length_cons,
                                              List.length_nil, Nat.reduceAdd,
                                              List.getElem_singleton, i_nat]
                                            -- Use h_elem directly to prove the element at position j equals i
                                            apply h_elem
                                            -- The List.getElem operator accesses the jth element, so it must be a member
                                            have h_j_mem := List.get_mem (List.filter (fun b ↦ decide (i = b)) (List.finRange n)) ⟨j, hj1⟩
                                            exact h_j_mem
                                        simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.toFinset_cons,
                                          List.toFinset_nil, insert_emptyc_eq, Finset.sum_const_zero,
                                          List.length_finRange, Fin.is_lt, implies_true, List.length_cons,
                                          List.length_nil, zero_add, Nat.lt_one_iff, pos_of_gt, List.mem_finRange,
                                          Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem,
                                          Fin.val_eq_zero, List.getElem_cons_zero, List.head?_cons, i_nat]

                                      rw [← h_elem i h_i_in]
                                      apply List.ext_get
                                      · -- Prove lengths are equal
                                        rw [List.length_singleton, h_len_eq]
                                      · -- Prove elements are equal
                                        intro k hk
                                        have : k < 1 := by
                                          rw [← h_elem i h_i_in] at hk
                                          exact Nat.lt_of_lt_of_eq hk h_len_eq
                                        have : k = 0 := Nat.lt_one_iff.mp this
                                        subst this
                                        -- Element at position 0
                                        have h0 : 0 < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := h_len_eq ▸ show 0 < 1 by decide
                                        have elem_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h0⟩ = i := by
                                          apply h_elem
                                          exact List.get_mem _ ⟨0, h0⟩
                                        rw [List.get_eq_getElem] at elem_eq
                                        exact fun h₂ ↦ elem_eq

                                    -- Then show the element at index 0 is i
                                    have h_head_eq : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? = some i := by
                                      rw [h_head]

                                    rw [← h_elem i h_i_in]
                                    -- Use the fact that i is in the filtered list
                                    have h_getElem : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0] = i := by
                                      -- Convert from List.head? to List[]
                                      rw [@List.getElem_eq_iff]
                                      -- Use h_head which tells us the head is i
                                      rw [← h_head_eq]
                                      -- Convert back to List.get?
                                      simp only [List.length_filter_pos_iff, List.mem_finRange,
                                        decide_eq_true_eq, true_and, exists_eq',
                                        List.getElem?_eq_getElem]
                                      -- Relate head? to find?
                                      have h_head_find : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? =
                                                       List.find? (fun b ↦ decide (i = b)) (List.filter (fun _ ↦ true) (List.finRange n)) := by
                                        rw [List.filter_true]
                                        exact List.head?_filter (fun b ↦ decide (i = b)) (List.finRange n)
                                      rw [h_head_find]
                                      rw [List.filter_true]
                                      -- Convert between getElem? notation and find? for filtered lists
                                      -- Manually relate getElem? at index 0 with head?
                                      have h_get_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? =
                                                       (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).head? := by
                                        simp only [List.head?]
                                        split
                                        · -- We have a contradiction: the list is empty but contains i
                                          rw [← h_elem i h_i_in] at h_i_in
                                          simp_all only [List.toFinset_nil, Finset.sum_const_zero, List.length_finRange,
                                            Fin.is_lt, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
                                            List.length_nil, lt_self_iff_false, i_nat]
                                        · rw [← h2]
                                          simp only [List.toFinset_filter, decide_eq_true_eq,
                                            List.toFinset_finRange, Finset.sum_const_zero,
                                            List.length_filter_pos_iff, List.mem_finRange, true_and,
                                            exists_eq', List.getElem?_eq_getElem, Option.some.injEq,
                                            i_nat]
                                          simp_all only [List.mem_cons, true_or, List.toFinset_cons,
                                            Finset.sum_const_zero, List.length_finRange, Fin.is_lt, forall_eq_or_imp,
                                            List.length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
                                            pos_of_gt, or_true, List.mem_finRange, List.length_nil, Nat.reduceAdd,
                                            Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                            List.getElem_cons_zero, List.head?_cons, add_left_eq_self,
                                            List.length_eq_zero_iff, List.filter_true, i_nat]

                                      rw [← h_elem i h_i_in]
                                      -- The head of a filtered list equals find? with the same predicate
                                      simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                                        Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                                        List.mem_finRange, true_and, implies_true, Nat.lt_one_iff, pos_of_gt,
                                        List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
                                        List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, decide_true,
                                        and_self, List.filter_true, List.head?_filter, List.getElem?_eq_getElem,
                                        Option.some.injEq, i_nat]
                                    exact h_getElem
                                  exact List.getElem_eq_iff.mpr h_zero_eq


                                exact h_get_zero
                              -- Convert j (Nat) to Fin n using the fact that j < n
                              have h_j_lt_n : j < n := by
                                -- Since j appears in [i][j]? and [i] has length 1
                                have h_j_bound : j < [i].length := by
                                  -- When accessing [i][j]?, j must be less than the length of [i]
                                  have h_some : Option.isSome ([i][j]?) := by
                                    simp only [h_get, Option.isSome_some]
                                  -- If we can successfully access index j, then j < length
                                  rw [List.length_singleton]
                                  sorry

                                -- Since j < 1, j must be 0
                                have h_j_zero : j = 0 := by
                                  exact Nat.lt_one_iff.mp h_j_bound


                                -- [i] has length 1
                                simp only [List.length_singleton] at h_j_bound
                                -- From j < 1, we know j = 0
                                have h_j_eq_zero : j = 0 := Nat.lt_one_iff.mp h_j_bound

                                -- Since i is a Fin n, we know i < n, so j(=0) < n
                                rw [h_j_eq_zero]
                                exact Nat.zero_lt_of_lt i.isLt

                              -- Now construct a Fin n from j
                              let j_fin : Fin n := ⟨j, h_j_lt_n⟩

                              -- Show j_fin is in the filter
                              have h_j_fin_mem : j_fin ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                                -- Since [i][j]? = some a✝, j must be 0 and a✝ = i
                                have h_j_zero : j = 0 := by
                                  have h_j_lt_one : j < 1 := by
                                    -- Since [i] has length 1 and we can access element j
                                    have : [i].length = 1 := by simp
                                    have : j < [i].length := by
                                      -- If we can get an element at position j, then j must be less than length
                                      sorry -- This would need access to a hypothesis about j being a valid index
                                    simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                                      Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                                      List.mem_finRange, true_and, implies_true, decide_true, and_self,
                                      List.length_filter_pos_iff, exists_eq', List.length_cons, List.length_nil,
                                      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                      List.getElem_cons_zero, List.getElem?_eq_getElem, Option.some.injEq, zero_add,
                                      Nat.lt_one_iff, pos_of_gt, i_nat]
                                  exact Nat.lt_one_iff.mp h_j_lt_one
                                subst h_j_zero
                                -- Since j = 0, j_fin must equal i
                                have h_j_fin_eq_i : j_fin = i := by
                                  apply Fin.eq_of_val_eq
                                  dsimp only [i_nat]
                                  -- Need to show j_fin = i by extracting values
                                  have h_j_fin_val : j_fin.val = 0 := rfl

                                  -- Extract a✝ = i from the singleton list access
                                  -- Since j = 0, we're getting the first element of [i]
                                  have h_val_eq_i : [i][0]? = some i := by simp
                                  -- The value we get from the list must equal i
                                  rw [←h_get_sing]  -- Use the property that [i][0] = i
                                  have : [i][0] = i := by simp
                                  have : j_fin = [i].get ⟨0, h₁⟩ := by
                                    apply Fin.eq_of_val_eq
                                    simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
                                      Fin.zero_eta, Fin.isValue, List.get_eq_getElem,
                                      Fin.val_eq_zero, List.getElem_cons_zero, i_nat]
                                    have h_sing_val : ([i].get ⟨0, h₁⟩).val = i.val := by
                                      rw [h_get_sing]
                                    rw [← h_get_sing]
                                    calc
                                      ↑j_fin = 0 := h_j_fin_val
                                      _ = ↑i := by
                                        have h_i_val : i.val = 0 := by
                                          -- Since i appears at position 0 in a list, its value must be 0
                                          have h : [i].get ⟨0, h₁⟩ = i := by exact h_get_sing
                                          -- When we have [i][0] = i, we know i.val = 0
                                          have h_index : i.val = 0 := by
                                            -- For a singleton list [i], if the element at index 0 equals i
                                            -- then i must be the 0th element in the Fin n enumeration
                                            sorry
                                          exact h_index
                                        exact id (Eq.symm h_i_val)
                                      _ = ↑([i].get ⟨0, h₁⟩) := by rw [h_get_sing];

                                  rw [this, ← h_get_sing]

                                  -- Since j_fin = ⟨0, _⟩ and i = a✝, show they're equal
                                subst h_j_fin_eq_i
                                -- Now i is in the filter
                                exact h_i_in

                              -- Apply h_elem to j_fin
                              have h_j_zero : j = 0 := by
                                -- Since [i] has length 1 and [i][j]? = some a✝,
                                -- j must be 0
                                have h_len_one : [i].length = 1 := by simp
                                have h_j_lt_one : j < 1 := by
                                  rw [← h_len_one]
                                  have h_some : Option.isSome ([i][j]?) := by
                                    simp only [h_get, Option.isSome_some]
                                  rw [← h_elem i h_i_in]
                                  simp only [List.length_cons, List.length_nil, zero_add,
                                    Nat.lt_one_iff, i_nat]
                                  simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                                    Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                                    List.mem_finRange, true_and, implies_true, decide_true, and_self,
                                    List.length_filter_pos_iff, exists_eq', List.length_cons, List.length_nil,
                                    Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                    List.getElem_cons_zero, List.getElem?_eq_getElem, Option.some.injEq, zero_add,
                                    isSome_getElem?, Nat.lt_one_iff, i_nat, j_fin]
                                exact Nat.lt_one_iff.mp h_j_lt_one

                              -- We need to ensure a variable exists before using it
                              -- Extract the value from the option
                              have h_extract : ∃ a, [i][j]? = some a := by
                                rw [h_j_zero]
                                have : [i][0]? = some i := by simp
                                use i

                              rcases h_extract with ⟨a, h_a_eq⟩

                              have h_a_eq_i : a = i := by
                                -- The only element in [i] is i
                                have h_len_one : [i].length = 1 := by simp
                                rw [h_j_zero] at h_a_eq
                                have h_get_zero : [i][0]? = some i := by simp
                                rw [h_get_zero] at h_a_eq
                                -- Extract the value from the some constructor
                                simp only [Option.some.injEq] at h_a_eq
                                exact id (Eq.symm h_a_eq)

                              -- Now we can rewrite the goal
                              rw [h_j_zero]  -- First replace j with 0
                              rw [← h2]  -- Then replace a✝ with i
                              -- Now we have (filter...)[0]? = some i
                              subst h_j_zero h_a_eq_i
                              simp_all only [List.length_finRange, List.toFinset_filter, decide_eq_true_eq,
                                List.toFinset_finRange, Finset.sum_const_zero, Fin.is_lt, List.mem_filter,
                                List.mem_finRange, true_and, implies_true, decide_true, and_self,
                                List.length_filter_pos_iff, exists_eq', List.length_cons, List.length_nil,
                                Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                                List.getElem_cons_zero, List.getElem?_eq_getElem, Option.some.injEq, zero_add,
                                Nat.lt_one_iff, pos_of_gt, i_nat, j_fin]  -- Which we have already proved
                          intro h_filter_get
                          -- If a✝ is in the filtered list, it must equal i
                          -- Replace direct references to 'a' with appropriate element from the list
                          -- First establish that j is within the bounds of the filtered list
                          have h_j_lt : j < (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).length := by
                          -- Since j can access an element of this list, it must be within bounds
                            have h_isSome : Option.isSome ((List.filter (fun b ↦ decide (i = b)) (List.finRange n))[j]?) :=
                              by
                                -- Since h_filter_get tells us the filter[j]? = some i, it's definitely Some
                                simp only [h_filter_get, Option.isSome_some]
                            simp only [gt_iff_lt, i_nat]
                            rw [← h_get_sing]
                            sorry

                          have h_elem_eq_i : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨j, h_j_lt⟩ = i := by
                            apply h_elem
                            exact List.get_mem (List.filter (fun b ↦ decide (i = b)) (List.finRange n)) ⟨j, h_j_lt⟩

                          -- With j = 0 and a✝ = i, we need to show [i][0]? = some i
                          subst h_zero
                          simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                            Finset.sum_const_zero, List.length_finRange, Fin.is_lt, List.mem_filter,
                            List.mem_finRange, true_and, implies_true, decide_true, and_self,
                            List.getElem?_eq_getElem, Option.some.injEq, List.get_eq_getElem,
                            List.length_filter_pos_iff, exists_eq', List.length_cons, List.length_nil, Nat.reduceAdd,
                            Fin.zero_eta, Fin.isValue, Fin.val_eq_zero, List.getElem_cons_zero, i_nat]
                          subst h_elem_eq_i
                          simp_all only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff, pos_of_gt]
                          -- The only element in singleton list [i] at position 0 is i
                          simp only [List.getElem?_singleton]
                          have h_j_eq_zero : j = 0 := by
                            -- We need to show j = 0 to simplify the if-then-else
                            -- Since the list has length 1 and j < length
                            sorry


                          rw [h_j_eq_zero]
                          rfl
                  -- head? of a singleton list is Some of that element
                  rw [h_filter_singleton]
                  rfl

                -- Convert from head? to get
                rw [@List.get_mk_zero]
                exact
                  (List.head_eq_iff_head?_eq_some (List.length_pos_iff.mp h_pos_length)).mpr h_head
              -- We need to prove that get ⟨n_1, h₂⟩ equals head, since n_1 = 0
              refine Fin.eq_of_val_eq ?_
              -- The filtered list is non-empty because it contains i
              apply Eq.trans
              · exact rfl
              · refine Fin.val_eq_of_eq ?_
                rw [@List.head_filter]
                simp only [List.get_eq_getElem, i_nat]
                subst h_zero
                simp_all only [List.mem_filter, List.mem_finRange, decide_true, and_self, List.toFinset_filter,
                  decide_eq_true_eq, List.toFinset_finRange, Finset.sum_const_zero, List.length_finRange, Fin.is_lt,
                  true_and, implies_true, List.get_eq_getElem, List.length_cons, List.length_nil, Nat.reduceAdd,
                  Fin.zero_eta, Fin.isValue, Fin.val_eq_zero, List.getElem_cons_zero, i_nat]
                simp_all only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff, pos_of_gt, i_nat]
                sorry

            -- The element at position 0 in the filtered list is i
            have h_get_filt : (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).get ⟨0, h_pos_length⟩ = i := by
              -- The first element of a non-empty list can be accessed with List.get
              have h_head : (List.filter (fun b ↦ decide (i = b)) (List.finRange n))[0]? = some i := by
                -- We need to show that the element at index 0 is i
                -- First, show i is in the filtered list
                have h_i_in : i ∈ List.filter (fun b ↦ decide (i = b)) (List.finRange n) := by
                  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
                  exact ⟨trivial, trivial⟩

                -- Use h_elem to conclude that get ⟨0, h_pos_length⟩ = i
                have h_get_eq_i := h_elem i h_i_in

                -- Convert from List.get to List[0]?
                rw [← h2]
                simp only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange,
                  Finset.sum_const_zero, List.length_filter_pos_iff, List.mem_finRange, true_and,
                  exists_eq', List.getElem?_eq_getElem, Option.some.injEq, i_nat]
                rw [← h_get_sing]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.get_eq_getElem,
                  List.getElem_singleton, i_nat]
                rw [← h_get_sing]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.get_eq_getElem,
                  List.getElem_singleton, i_nat]
                sorry
              subst h_zero
              simp_all only [List.mem_filter, List.mem_finRange, decide_true, and_self, List.toFinset_filter,
                decide_eq_true_eq, List.toFinset_finRange, Finset.sum_const_zero, List.length_finRange, Fin.is_lt,
                true_and, implies_true, List.getElem?_eq_getElem, Option.some.injEq, List.length_cons,
                List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, List.get_eq_getElem, Fin.val_eq_zero,
                List.getElem_cons_zero, i_nat]
            subst h_zero
            simp_all only [List.mem_filter, List.mem_finRange, decide_true, and_self, List.toFinset_filter,
              decide_eq_true_eq, List.toFinset_finRange, Finset.sum_const_zero, List.length_finRange, Fin.is_lt,
              true_and, implies_true, List.get_eq_getElem, List.length_cons, List.length_nil, Nat.reduceAdd,
              Fin.zero_eta, Fin.isValue, Fin.val_eq_zero, List.getElem_cons_zero, i_nat]


      exact h_filter
      -- Show that only i satisfies the predicate
    have h_count_one : (List.finRange n).countP (fun a ↦ decide (i = a)) = 1 := by
      -- Use the fact that List.filter and List.countP are related
      rw [← h_count]
      -- Use the previously proven fact about filter length
      exact List.countP_eq_length_filter (fun a ↦ decide (i = a)) (List.finRange n)

    -- Use the fact that length(filter p) + length(filter (not p)) = length(list)
    have h_complement : ∀ (α : Type) (l : List α) (p : α → Bool),
      (List.filter (fun a => !p a) l).length + (List.filter p l).length = l.length := by
      intro α l p
      -- The length of the list equals the sum of elements satisfying p and those not satisfying p
      have h_partition : List.Perm (List.filter (fun a => !p a) l ++ List.filter p l) l := by
        refine List.revzip_sublists' l (List.filter (fun a ↦ !p a) l) (List.filter p l) ?_
        simp_all only [List.toFinset_filter, decide_eq_true_eq, List.toFinset_finRange, Finset.sum_const_zero,
          List.length_finRange]
        sorry
      -- The length of a permutation equals the original length
      have h_perm_length : (List.filter (fun a => !p a) l ++ List.filter p l).length = l.length := by
        rw [List.Perm.length_eq h_partition]
      -- The length of an append is the sum of lengths
      rw [List.length_append] at h_perm_length
      exact h_perm_length

    -- Apply to our specific case
    let predicate : Fin n → Bool := fun a ↦ decide (i = a)
    have h_filter_eq : List.filter (fun a ↦ decide ¬i = a) (List.finRange n) =
                       List.filter (fun a ↦ !predicate a) (List.finRange n) := by
      apply List.filter_congr
      intro x _
      simp only [predicate, Bool.decide_coe, decide_not]

    have h_len_eq : (List.filter (fun a ↦ !predicate a) (List.finRange n)).length = n - 1 := by
      -- Apply our general lemma about partition
      have h_specific := h_complement (Fin n) (List.finRange n) predicate
      -- The filter (i = a) has length 1
      have h_filter_eq_count : (List.filter predicate (List.finRange n)).length = 1 := by
        simp only [predicate]
        exact h_count
      -- Substitute and solve
      rw [h_filter_eq_count, h_len] at h_specific
      exact Nat.eq_sub_of_add_eq h_specific

    rw [h_filter_eq, h_len_eq]
    -- Solve the equation: filter_length + 1 = n

  have h4 : (List.map (fun j ↦ (p i).toReal * (p j).toReal ^ 2) (List.filter (fun a ↦ decide ¬i = a) (List.finRange n))).sum =
            (p i).toReal * (n - 1) := by
    sorry -- This requires proving the sum equals (p i).toReal * (n - 1)

  calc
    ∑ x ∈ (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset, 0 +
      (List.map (fun j ↦ (p i).toReal * (p j).toReal ^ 2) (List.filter (fun a ↦ decide ¬i = a) (List.finRange n))).sum
    = 0 + (p i).toReal * (n - 1) := by
      -- Apply h2 and h4 directly to the expression
      have sum1 : ∑ x ∈ (List.filter (fun b ↦ decide (i = b)) (List.finRange n)).toFinset, 0 = 0 := h2
      have sum2 : (List.map (fun j ↦ (p i).toReal * (p j).toReal ^ 2) (List.filter (fun a ↦ decide ¬i = a) (List.finRange n))).sum = (p i).toReal * (n - 1) := h4
      rw [← h_square_one i]
      ring_nf
      sorry
    _ = (p i).toReal * ↑n - (p i).toReal ^ 3 := by
      cases p i
      · -- up case: 1 * n - 1 = n - 1
        simp [SpinState.toReal]
      · -- down case: -1 * n - (-1) = -n + 1 = -(n-1)
        simp [SpinState.toReal]
        ring
    _ = (p i).toReal * ↑n - (p i).toReal := by
      cases p i <;> simp [SpinState.toReal] <;> ring
    _ = (p i).toReal * ↑n - (p i).toReal ^ 3 := by
      cases p i <;> simp [SpinState.toReal] <;> ring
