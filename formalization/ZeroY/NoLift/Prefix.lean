import ZeroY.NoLift.Construction

/-!
# Prefix structure of frozen expansion

The copied parent template is independent of the number of blocks. Summation
is causal, so increasing that number only appends entries. Freezing also leaves
the original prefix and first replacement entry unchanged. These statements
hold for every freezing list, without eligibility or descent certificates.
-/

namespace ZeroY.NoLift

private def sumStep (parent : ParentMap) (acc : Sequence) (value : Nat) : Sequence :=
  acc ++ [match parent acc.length with
    | none => value
    | some column => value + acc[column]?.getD 0]

private theorem sumFold_extends (parent : ParentMap) (upper acc : Sequence) :
    acc.IsPrefix (upper.foldl (sumStep parent) acc) := by
  induction upper generalizing acc with
  | nil => exact List.prefix_refl _
  | cons value rest ih =>
      exact (List.prefix_append acc _).trans (ih (sumStep parent acc value))

theorem sumRow_prefix (parent : ParentMap) {left right : Sequence}
    (hPrefix : left.IsPrefix right) :
    (sumRow parent left).IsPrefix (sumRow parent right) := by
  rcases hPrefix with ⟨tail, rfl⟩
  change (left.foldl (sumStep parent) []).IsPrefix
    ((left ++ tail).foldl (sumStep parent) [])
  rw [List.foldl_append]
  exact sumFold_extends parent tail _

theorem sumRow_take (parent : ParentMap) (upper : Sequence) (count : Nat) :
    sumRow parent (upper.take count) = (sumRow parent upper).take count := by
  have h := List.prefix_iff_eq_take.mp (sumRow_prefix parent (List.take_prefix count upper))
  rw [sumRow_length, List.length_take] at h
  rw [List.take_eq_take_min (l := sumRow parent upper), sumRow_length]
  exact h

theorem sumRow_foldr_take (parents : Nat → ParentMap) (rows : List Nat)
    (upper : Sequence) (count : Nat) :
    rows.foldr (fun row next => sumRow (parents row) next) (upper.take count) =
      (rows.foldr (fun row next => sumRow (parents row) next) upper).take count := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.foldr_cons, ih, sumRow_take]

theorem sumRow_foldr_prefix (parents : Nat → ParentMap) (rows : List Nat)
    {left right : Sequence} (hPrefix : left.IsPrefix right) :
    (rows.foldr (fun row next => sumRow (parents row) next) left).IsPrefix
      (rows.foldr (fun row next => sumRow (parents row) next) right) := by
  induction rows with
  | nil => exact hPrefix
  | cons row rest ih => exact sumRow_prefix _ ih

theorem sumRow_foldr_take_congr {left right : Nat → ParentMap} (rows : List Nat)
    (upper : Sequence) (count : Nat)
    (hParents : ∀ row ∈ rows, ∀ column, column < count → left row column = right row column) :
    (rows.foldr (fun row next => sumRow (left row) next) upper).take count =
      (rows.foldr (fun row next => sumRow (right row) next) upper).take count := by
  rw [← sumRow_foldr_take, ← sumRow_foldr_take]
  apply sumRow_foldr_congr_parent
  intro row hRow column hColumn
  apply hParents row hRow column
  simp only [List.length_take] at hColumn
  omega

/-- At the first replacement column the seam shift is zero, whether or not
the last column occurs in the supplied freezing list. -/
theorem frozenMountainParent_eq_copied_le (frozen : FreezeSet) (row : Nat)
    (parent : ParentMap) (root last target : Nat)
    (hRoot : root < last) (hTarget : target ≤ last) :
    frozenMountainParent frozen row parent root last target =
      copiedMountainParent parent root last target := by
  rcases Nat.eq_or_lt_of_le hTarget with hEqual | hLess
  · subst target
    have hLength : 0 < last - root := by omega
    simp [frozenMountainParent, copiedMountainParent, Nat.div_self hLength]
  · simp [frozenMountainParent, copiedMountainParent, hLess]

theorem mountainFold_reconstruct (s : Expr) (height : Nat) :
    (List.range height).foldr (fun row next => sumRow (mountainParent s.values row) next)
      (mountainLayer s.values height).values = s.values := by
  induction height with
  | zero => rfl
  | succ height ih =>
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      have hSum : sumRow (mountainParent s.values height)
          (mountainLayer s.values (height + 1)).values =
          (mountainLayer s.values height).values := by
        unfold mountainParent mountainLayer
        rw [layerAfter_succ_next]
        exact legal_layerAfter_sumRow_nextLayer s.legal height
      rw [hSum]
      exact ih

theorem copyMountainRow_take_last (values : Sequence) (root last count : Nat)
    (hLast : last ≤ values.length) :
    (copyMountainRow values root last count).take last = values.take last := by
  unfold copyMountainRow
  rw [List.take_append_of_le_length (by
    simpa only [List.length_take, Nat.min_eq_left hLast] using Nat.le_refl last)]
  simp [List.take_take]

theorem copyMountainRow_prefix (values : Sequence) (root last : Nat)
    {smaller larger : Nat} (hCount : smaller ≤ larger) :
    (copyMountainRow values root last smaller).IsPrefix
      (copyMountainRow values root last larger) := by
  induction larger generalizing smaller with
  | zero =>
      have : smaller = 0 := by omega
      subst smaller
      exact List.prefix_refl _
  | succ larger ih =>
      by_cases hEqual : smaller = larger + 1
      · subst smaller; exact List.prefix_refl _
      · have hLess : smaller ≤ larger := by omega
        rw [copyMountainRow_succ]
        exact (ih hLess).trans (List.prefix_append _ _)

/-- Every output retains the input with its final entry removed. -/
theorem freezeExpand_take_pred (s : Expr) (frozen : FreezeSet) (count : Nat) :
    (freezeExpand s frozen count).values.take (s.values.length - 1) =
      s.values.take (s.values.length - 1) := by
  by_cases hCount : count = 0
  · subst count
    simp [freezeExpand_zero, Expr.take, List.take_take]
  · simp only [freezeExpand_values, freezeExpandRaw, hCount, ↓reduceIte]
    cases hSite : expansionSite s.values with
    | none => simp [List.take_take]
    | some pair =>
        rcases pair with ⟨height, root⟩
        have hTopLength : s.values.length - 1 ≤ (mountainLayer s.values height).values.length := by
          simp only [mountainLayer, layerAfter_length]
          omega
        rw [sumRow_foldr_take_congr (right := mountainParent s.values) _ _ _
          (fun row _ column hColumn => frozenMountainParent_prefix _ _ _ _ _ _ hColumn)]
        rw [← sumRow_foldr_take, copyMountainRow_take_last _ _ _ _ hTopLength,
          sumRow_foldr_take, mountainFold_reconstruct]

theorem freezeExpand_length_ge_pred (s : Expr) (frozen : FreezeSet) (count : Nat) :
    s.values.length - 1 ≤ (freezeExpand s frozen count).values.length := by
  have hLength := congrArg List.length (freezeExpand_take_pred s frozen count)
  simp only [List.length_take, Nat.min_eq_left (Nat.sub_le s.values.length 1)] at hLength
  omega

theorem freezeExpand_preserves_prefix (s : Expr) (frozen : FreezeSet) (count : Nat) :
    (s.values.take (s.values.length - 1)).IsPrefix (freezeExpand s frozen count).values := by
  apply List.prefix_iff_eq_take.mpr
  simp only [List.length_take, Nat.min_eq_left (Nat.sub_le s.values.length 1)]
  exact (freezeExpand_take_pred s frozen count).symm

/-- A fixed freezing template gives nested prefixes as the parameter increases. -/
theorem freezeExpand_prefix (s : Expr) (frozen : FreezeSet)
    {smaller larger : Nat} (hCount : smaller ≤ larger) :
    (freezeExpand s frozen smaller).values.IsPrefix (freezeExpand s frozen larger).values := by
  by_cases hSmall : smaller = 0
  · subst smaller
    simpa only [freezeExpand_zero, Expr.take] using freezeExpand_preserves_prefix s frozen larger
  · have hLarge : larger ≠ 0 := by omega
    simp only [freezeExpand_values, freezeExpandRaw, hSmall, hLarge, ↓reduceIte]
    cases expansionSite s.values with
    | none => exact List.prefix_refl _
    | some pair =>
        rcases pair with ⟨height, root⟩
        exact sumRow_foldr_prefix _ _ (copyMountainRow_prefix _ _ _ hCount)

/-- Freezing cannot alter any position up to and including the original last
column; this includes the first new entry when the expansion is nontrivial. -/
theorem freezeExpand_take_input_length (s : Expr) (frozen : FreezeSet) (count : Nat) :
    (freezeExpand s frozen count).values.take s.values.length =
      (expandY s count).values.take s.values.length := by
  by_cases hCount : count = 0
  · subst count
    rw [freezeExpand_zero, expandY_zero]
  · simp only [freezeExpand_values, freezeExpandRaw, expandY_values, expandYRaw,
      hCount, ↓reduceIte]
    cases hSite : expansionSite s.values with
    | none => rfl
    | some pair =>
        rcases pair with ⟨height, root⟩
        apply sumRow_foldr_take_congr
        intro row _ column hColumn
        exact frozenMountainParent_eq_copied_le _ _ _ _ _ _
          (expansionSite_root_lt hSite) (by omega)

private theorem seqLt_of_take_eq {left right other : Sequence} (hLess : SeqLt left right)
    (hTake : other.take right.length = left.take right.length) : SeqLt other right := by
  induction hLess generalizing other with
  | nil value rest =>
      cases other with
      | nil => exact .nil _ _
      | cons first tail => simp at hTake
  | @head first second left right hLess =>
      cases other with
      | nil => exact .nil _ _
      | cons value rest =>
          simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at hTake
          rcases hTake with ⟨rfl, _⟩
          exact .head hLess
  | @tail value left right hLess ih =>
      cases other with
      | nil => exact .nil _ _
      | cons first rest =>
          simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at hTake
          rcases hTake with ⟨rfl, hTake⟩
          exact .tail _ (ih hTake)

/-- Every frozen expansion of a nonempty input is lexicographically smaller.
This does not by itself imply well-foundedness on all legal expressions. -/
theorem freezeExpand_lt (s : Expr) (frozen : FreezeSet) (count : Nat)
    (hNonempty : s.values ≠ []) : ExprLt (freezeExpand s frozen count) s := by
  exact seqLt_of_take_eq
    (expandY_lt s count (List.length_pos_iff.mpr hNonempty))
    (freezeExpand_take_input_length s frozen count)

end ZeroY.NoLift
