import ZeroY.Experimental.AncestralWeakening
import ZeroY.Dynamics.Equivalence

/-!
# Executable descent certificates for weakened expansion

The parent checker visits every stored column and every row of that column.
The BMS parent bounds prove that no edge outside this finite range is omitted.
When called on `encode` it therefore checks the complete canonical parent graph,
not the parent pointers used while drawing or constructing a copied mountain.

The second certificate is a finite list of ordinary expansion parameters.  Its
endpoint is calculated, rather than supplied together with an assumed descent.
Neither checker assumes well-foundedness, standard generation, or preservation
of the ordinal value of the original expression.
-/

namespace ZeroY.NoLift

open YesMetaZFC.BMS
open ZeroY.Experimental

/-- The actual stored height of one column, including any stored zero rows. -/
def columnHeight (array : BMSArray) (column : Nat) : Nat :=
  (array[column]?.getD []).length

private theorem row_lt_columnHeight_of_entry {array : BMSArray}
    {column row value : Nat} (hEntry : entry? array column row = some value) :
    row < columnHeight array column := by
  cases hColumn : array[column]? with
  | none => simp [entry?, hColumn] at hEntry
  | some values =>
      have hValue : values[row]? = some value := by
        simpa [entry?, hColumn] using hEntry
      have hRow : row < values.length := by
        by_cases hLess : row < values.length
        · exact hLess
        · have hNone : values[row]? = none := List.getElem?_eq_none (by omega)
          rw [hNone] at hValue
          contradiction
      simpa [columnHeight, hColumn] using hRow

/-- Every source parent edge must be an ancestor edge of the target, at the
same column indices.  A reference edge may stand for several target edges. -/
def sameColumnParentCheck (source target : ValidArray) : Bool :=
  decide (source.raw.length = target.raw.length) &&
    (List.range source.raw.length).all (fun column =>
      (List.range (columnHeight source.raw column)).all (fun row =>
        match parent row source.raw column with
        | none => true
        | some found => isAncestor target.raw row found column))

theorem sameColumnParentCheck_iff (source target : ValidArray) :
    sameColumnParentCheck source target = true ↔
      source.raw.length = target.raw.length ∧
      ∀ row column found, parent row source.raw column = some found →
        isAncestor target.raw row found column = true := by
  constructor
  · intro hCheck
    simp only [sameColumnParentCheck, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range] at hCheck
    refine ⟨hCheck.1, ?_⟩
    intro row column found hParent
    have hColumn := parent_some_target_valid hParent
    obtain ⟨left, right, _, hEntry, _⟩ := parent_some_entry_lt hParent
    have hRow := row_lt_columnHeight_of_entry hEntry
    have hEdge := hCheck.2 column hColumn row hRow
    simpa only [hParent] using hEdge
  · rintro ⟨hLength, hEdge⟩
    simp only [sameColumnParentCheck, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_range]
    refine ⟨hLength, ?_⟩
    intro column _ row _
    cases hParent : parent row source.raw column with
    | none => rfl
    | some found => exact hEdge row column found hParent

/-- Successful finite edge checks give the all-rows ancestor embedding. -/
def sameColumnParentEmbedding {source target : ValidArray}
    (hCheck : sameColumnParentCheck source target = true) :
    AncestorEmbedding source target :=
  AncestorEmbedding.ofSameColumnParentEdges
    ((sameColumnParentCheck_iff source target).mp hCheck).1
    ((sameColumnParentCheck_iff source target).mp hCheck).2

theorem sameColumnParentCheck_sound {source target : ValidArray}
    (hCheck : sameColumnParentCheck source target = true) :
    Nonempty (AncestorEmbedding source target) :=
  ⟨sameColumnParentEmbedding hCheck⟩

@[simp]
theorem sameColumnParentCheck_self (array : ValidArray) :
    sameColumnParentCheck array array = true := by
  apply (sameColumnParentCheck_iff array array).mpr
  exact ⟨rfl, fun _ _ _ hParent => direct_parent_isAncestor hParent⟩

/-- Execute an ordinary finite path in the order in which its indices occur. -/
def runPath : Expr → List Nat → Expr
  | start, [] => start
  | start, index :: rest => runPath (expandY start index) rest

theorem runPath_yExpansionPath (start : Expr) (indices : List Nat) :
    YExpansionPath start (runPath start indices) := by
  induction indices generalizing start with
  | nil => exact .refl _
  | cons index rest ih =>
      exact (YExpansionPath.single start index).trans (ih (expandY start index))

private theorem strictDescent_expandY_of_ne {start : Expr} (index : Nat)
    (hChanged : expandY start index ≠ start) :
    StrictDescent (encode (expandY start index)) (encode start) :=
  Relation.TransGen.single
    ((encode_step_iff _ _).mpr ⟨⟨index, rfl⟩, hChanged⟩)

/-- Equal steps, including any extra steps after reaching the empty expression,
can be removed from an ordinary path. -/
theorem runPath_eq_or_strictDescent (start : Expr) (indices : List Nat) :
    runPath start indices = start ∨
      StrictDescent (encode (runPath start indices)) (encode start) := by
  induction indices generalizing start with
  | nil => exact Or.inl rfl
  | cons index rest ih =>
      change runPath (expandY start index) rest = start ∨
        StrictDescent (encode (runPath (expandY start index) rest)) (encode start)
      rcases ih (expandY start index) with hSame | hPath
      · by_cases hEqual : expandY start index = start
        · exact Or.inl (hSame.trans hEqual)
        · apply Or.inr
          rw [hSame]
          exact strictDescent_expandY_of_ne index hEqual
      · by_cases hEqual : expandY start index = start
        · exact Or.inr (by simpa only [hEqual] using hPath)
        · exact Or.inr ((strictDescent_expandY_of_ne index hEqual).trans hPath)

theorem expandY_ne_of_nonempty {start : Expr} (index : Nat)
    (hNonempty : start.values ≠ []) : expandY start index ≠ start := by
  have hLength : 0 < start.values.length := List.length_pos_iff.mpr hNonempty
  intro hEqual
  have hLess := expandY_lt start index hLength
  rw [hEqual] at hLess
  exact exprLt_irrefl start hLess

/-- A nonempty list of ordinary indices from a nonempty input really descends,
even when the path subsequently reaches zero and contains redundant steps. -/
theorem runPath_strictDescent {start : Expr} {indices : List Nat}
    (hNonempty : start.values ≠ []) (hIndices : indices ≠ []) :
    StrictDescent (encode (runPath start indices)) (encode start) := by
  cases indices with
  | nil => exact False.elim (hIndices rfl)
  | cons index rest =>
      have hFirst := strictDescent_expandY_of_ne index
        (expandY_ne_of_nonempty index hNonempty)
      rcases runPath_eq_or_strictDescent (expandY start index) rest with hSame | hPath
      · change StrictDescent (encode (runPath (expandY start index) rest)) (encode start)
        rw [hSame]
        exact hFirst
      · exact hFirst.trans hPath

theorem runPath_lt {start : Expr} {indices : List Nat}
    (hNonempty : start.values ≠ []) (hIndices : indices ≠ []) :
    ExprLt (runPath start indices) start :=
  (encode_lt_iff _ _).mp
    (BMS.matrixLt_of_strictDescent (runPath_strictDescent hNonempty hIndices))

/-- Check a nonempty ordinary path and its exact endpoint by finite execution. -/
def checkPath (smaller larger : Expr) (indices : List Nat) : Bool :=
  decide (larger.values ≠ []) && decide (indices ≠ []) &&
    decide ((runPath larger indices).values = smaller.values)

theorem checkPath_sound {smaller larger : Expr} {indices : List Nat}
    (hCheck : checkPath smaller larger indices = true) :
    StrictDescent (encode smaller) (encode larger) := by
  simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at hCheck
  have hEqual : runPath larger indices = smaller := Expr.ext hCheck.2
  rw [← hEqual]
  exact runPath_strictDescent hCheck.1.1 hCheck.1.2

/-- An ancestry certificate references one ordinary expansion.  A path
certificate records all ordinary expansion parameters, without a search bound. -/
inductive DescentCertificate where
  | ancestry (index : Nat)
  | ordinaryPath (indices : List Nat)
  deriving DecidableEq, Repr

/-- Both branches are executable finite checks; no accessibility proof is input. -/
def checkDescent (smaller larger : Expr) : DescentCertificate → Bool
  | .ancestry index =>
      decide (larger.values ≠ []) &&
        sameColumnParentCheck (encode smaller) (encode (expandY larger index))
  | .ordinaryPath indices => checkPath smaller larger indices

theorem checkDescent_sound {smaller larger : Expr} {certificate : DescentCertificate}
    (hCheck : checkDescent smaller larger certificate = true) :
    MixedYStep smaller larger := by
  cases certificate with
  | ancestry index =>
      simp only [checkDescent, Bool.and_eq_true, decide_eq_true_eq] at hCheck
      apply mixedYStep_of_ancestralYStep
      exact ancestralYStep_of_embedding index
        (expandY_ne_of_nonempty index hCheck.1) (sameColumnParentEmbedding hCheck.2)
  | ordinaryPath indices =>
      exact mixedYStep_of_ordinaryDescent (checkPath_sound hCheck)

/-- Ordinary expansion is always available as the certified fallback. -/
theorem checkDescent_ordinary (larger : Expr) (index : Nat)
    (hNonempty : larger.values ≠ []) :
    checkDescent (expandY larger index) larger (.ancestry index) = true := by
  simp [checkDescent, hNonempty]

end ZeroY.NoLift
