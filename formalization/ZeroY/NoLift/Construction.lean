import ZeroY.Expansion.Conjugacy

/-!
# Two policies for freezing copied mountain edges

This file defines the actual numerical construction, independently of any
descent certificate or choice of a freezing set. Rows and columns are zero
based. `internal` permits an original parent in the bad part; `directRoot`
requires that original parent to be the bad root itself.

Legality here means positive entries with initial entry 1 (or the empty
expression). It does not mean standardness, preservation of an ordinal, or
absence of lifting. Those properties do not follow from this construction.
-/

namespace ZeroY.NoLift

inductive FreezePolicy where
  | internal
  | directRoot
  deriving DecidableEq, Repr

abbrev FreezeSet := List (Nat × Nat)

/-- The only distinction between the two policies. -/
def parentAllowed (policy : FreezePolicy) (root parent : Nat) : Bool :=
  match policy with
  | .internal => root ≤ parent
  | .directRoot => parent == root

/-- Candidate side branches, excluding the previous-row ancestry of the last
column. The seam (the original last column) is never a candidate. -/
def freezeCandidate (policy : FreezePolicy) (s : Expr) (edge : Nat × Nat) : Bool :=
  match expansionSite s.values with
  | none => false
  | some (height, root) =>
      let row := edge.1
      let column := edge.2
      0 < row && row < height && root < column && column < s.values.length - 1 &&
        !(YesMetaZFC.BMS.ancestorChain (mountainParent s.values (row - 1))
          (s.values.length - 1) (s.values.length - 1)).contains column &&
        (mountainParent s.values row column).any (parentAllowed policy root)

/-- Finite enumeration in increasing row, then increasing column order. -/
def freezeCandidates (policy : FreezePolicy) (s : Expr) : FreezeSet :=
  match expansionSite s.values with
  | none => []
  | some (height, _) =>
      ((List.range height).flatMap fun row =>
        (List.range (s.values.length - 1)).map fun column => (row, column)).filter
          (freezeCandidate policy s)

/-- Lists represent sets without duplicate coordinates. -/
def FrozenValid (policy : FreezePolicy) (s : Expr) (frozen : FreezeSet) : Prop :=
  frozen.Nodup ∧ ∀ edge ∈ frozen, freezeCandidate policy s edge = true

theorem mem_freezeCandidates_iff (policy : FreezePolicy) (s : Expr)
    (edge : Nat × Nat) :
    edge ∈ freezeCandidates policy s ↔ freezeCandidate policy s edge = true := by
  unfold freezeCandidates
  cases hSite : expansionSite s.values with
  | none => simp [freezeCandidate, hSite]
  | some pair =>
      rcases pair with ⟨height, root⟩
      rw [List.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hCandidate
        refine ⟨?_, hCandidate⟩
        have hBounds := hCandidate
        simp only [freezeCandidate, hSite, Bool.and_eq_true, decide_eq_true_eq] at hBounds
        rcases hBounds with ⟨⟨⟨⟨⟨_, hRow⟩, _⟩, hColumn⟩, _⟩, _⟩
        apply List.mem_flatMap.mpr
        refine ⟨edge.1, List.mem_range.mpr hRow, ?_⟩
        exact List.mem_map.mpr ⟨edge.2, List.mem_range.mpr hColumn, by cases edge; rfl⟩

theorem frozenValid_iff_subset (policy : FreezePolicy) (s : Expr) (frozen : FreezeSet) :
    FrozenValid policy s frozen ↔ frozen.Nodup ∧ frozen ⊆ freezeCandidates policy s := by
  constructor
  · rintro ⟨hNodup, hCandidates⟩
    exact ⟨hNodup, fun edge hMem => (mem_freezeCandidates_iff _ _ _).mpr (hCandidates edge hMem)⟩
  · rintro ⟨hNodup, hSubset⟩
    exact ⟨hNodup, fun edge hMem => (mem_freezeCandidates_iff _ _ _).mp (hSubset hMem)⟩

@[simp] theorem frozenValid_nil (policy : FreezePolicy) (s : Expr) :
    FrozenValid policy s [] := by
  simp [FrozenValid]

theorem parentAllowed_direct_implies_internal {root parent : Nat}
    (h : parentAllowed .directRoot root parent = true) :
    parentAllowed .internal root parent = true := by
  simp only [parentAllowed, beq_iff_eq] at h
  simp [parentAllowed, h]

theorem freezeCandidate_direct_implies_internal {s : Expr} {edge : Nat × Nat}
    (h : freezeCandidate .directRoot s edge = true) :
    freezeCandidate .internal s edge = true := by
  unfold freezeCandidate at h ⊢
  cases hSite : expansionSite s.values with
  | none => simp [hSite] at h
  | some site =>
      rcases site with ⟨height, root⟩
      simp only [hSite, Bool.and_eq_true] at h ⊢
      refine ⟨h.1, ?_⟩
      cases hParent : mountainParent s.values edge.1 edge.2 with
      | none => simp [hParent] at h
      | some parent =>
          exact parentAllowed_direct_implies_internal (by simpa [hParent] using h.2)

theorem frozenValid_direct_implies_internal {s : Expr} {frozen : FreezeSet}
    (h : FrozenValid .directRoot s frozen) : FrozenValid .internal s frozen := by
  exact ⟨h.1, fun edge hMem => freezeCandidate_direct_implies_internal (h.2 edge hMem)⟩

theorem freezeCandidates_direct_subset_internal (s : Expr) :
    freezeCandidates .directRoot s ⊆ freezeCandidates .internal s := by
  intro edge hMem
  apply (mem_freezeCandidates_iff _ _ _).mpr
  exact freezeCandidate_direct_implies_internal ((mem_freezeCandidates_iff _ _ _).mp hMem)

/-- The usual copied parent, except that an explicitly frozen original edge
retains its original endpoint. Boundary columns still use the original last
column, as in `copiedMountainParent`. -/
def frozenMountainParent (frozen : FreezeSet) (row : Nat) (parent : ParentMap)
    (root last target : Nat) : Option Nat :=
  if target < last then parent target
  else
    let blockLength := last - root
    let copy := (target - root) / blockLength
    let source := root + (target - root) % blockLength
    if source = root then
      (parent last).map fun p =>
        if p < root || (frozen.contains (row, last)) then p
        else p + (copy - 1) * blockLength
    else
      (parent source).map fun p =>
        if p < root || (frozen.contains (row, source)) then p
        else p + copy * blockLength

@[simp] theorem frozenMountainParent_nil (row : Nat) (parent : ParentMap)
    (root last target : Nat) :
    frozenMountainParent [] row parent root last target =
      copiedMountainParent parent root last target := by
  simp [frozenMountainParent, copiedMountainParent]

@[simp] theorem frozenMountainParent_nil_map (row : Nat) (parent : ParentMap)
    (root last : Nat) :
    frozenMountainParent [] row parent root last = copiedMountainParent parent root last := by
  funext target
  exact frozenMountainParent_nil row parent root last target

theorem frozenMountainParent_prefix (frozen : FreezeSet) (row : Nat)
    (parent : ParentMap) (root last target : Nat) (hTarget : target < last) :
    frozenMountainParent frozen row parent root last target = parent target := by
  simp [frozenMountainParent, hTarget]

theorem frozenMountainParent_zero (frozen : FreezeSet) (row : Nat)
    (parent : ParentMap) (root last : Nat)
    (hLast : 0 < last) (hParent : parent 0 = none) :
    frozenMountainParent frozen row parent root last 0 = none := by
  simp [frozenMountainParent, hLast, hParent]

/-- Copy the top row and sum downwards using the explicitly frozen parent
template. Count zero always deletes the final entry. -/
def freezeExpandRaw (s : Sequence) (frozen : FreezeSet) (count : Nat) : Sequence :=
  if count = 0 then s.take (s.length - 1)
  else
    match expansionSite s with
    | none => s.take (s.length - 1)
    | some (row, root) =>
        (List.range row).foldr (fun lower upper =>
          sumRow (frozenMountainParent frozen lower (mountainParent s lower)
            root (s.length - 1)) upper)
          (copyMountainRow (mountainLayer s row).values root (s.length - 1) count)

private theorem frozenFold_legal (s : Sequence) (frozen : FreezeSet)
    (root last : Nat) (hLast : 0 < last)
    (rows : List Nat) (upper : Sequence) (hUpper : Legal upper) :
    Legal (rows.foldr (fun row next =>
      sumRow (frozenMountainParent frozen row (mountainParent s row) root last) next)
        upper) := by
  induction rows with
  | nil => exact hUpper
  | cons row rest ih =>
      exact sumRow_legal _ _
        (frozenMountainParent_zero _ _ _ _ _ hLast (mountainParent_zero s row)) ih

/-- No eligibility assumption on the chosen coordinates is needed for legality. -/
theorem freezeExpandRaw_legal {s : Sequence} (hLegal : Legal s)
    (frozen : FreezeSet) (count : Nat) : Legal (freezeExpandRaw s frozen count) := by
  unfold freezeExpandRaw
  split
  · exact legal_take hLegal _
  · cases hSite : expansionSite s with
    | none => exact legal_take hLegal _
    | some pair =>
        rcases pair with ⟨row, root⟩
        have hLast : 0 < s.length - 1 := by
          have := expansionSite_root_lt hSite
          omega
        exact frozenFold_legal s frozen root _ hLast _ _
          (copyMountainRow_legal (mountainLayer_legal hLegal row) root _ count hLast)

def freezeExpand (s : Expr) (frozen : FreezeSet) (count : Nat) : Expr :=
  ⟨freezeExpandRaw s.values frozen count, freezeExpandRaw_legal s.legal frozen count⟩

@[simp] theorem freezeExpand_values (s : Expr) (frozen : FreezeSet) (count : Nat) :
    (freezeExpand s frozen count).values = freezeExpandRaw s.values frozen count := rfl

@[simp] theorem freezeExpand_zero (s : Expr) (frozen : FreezeSet) :
    freezeExpand s frozen 0 = s.take (s.values.length - 1) := by
  apply Expr.ext
  simp [freezeExpandRaw]
  rfl

@[simp] theorem freezeExpand_nil (s : Expr) (count : Nat) :
    freezeExpand s [] count = expandY s count := by
  by_cases hCount : count = 0
  · subst count
    rw [freezeExpand_zero, expandY_zero]
  · apply Expr.ext
    simp only [freezeExpand_values, expandY_values, freezeExpandRaw, hCount, ↓reduceIte]
    unfold expandYRaw
    cases expansionSite s.values with
    | none => rfl
    | some pair =>
        rcases pair with ⟨row, root⟩
        simp only [frozenMountainParent_nil_map]

/-- Freezing changes entries, but never changes the output width. -/
theorem freezeExpand_length (s : Expr) (frozen : FreezeSet) (count : Nat) :
    (freezeExpand s frozen count).values.length = (expandY s count).values.length := by
  by_cases hCount : count = 0
  · subst count
    rw [freezeExpand_zero, expandY_zero]
  · simp only [freezeExpand_values, expandY_values, freezeExpandRaw, hCount, ↓reduceIte]
    unfold expandYRaw
    cases expansionSite s.values with
    | none => rfl
    | some pair =>
        rcases pair with ⟨row, root⟩
        simp only [sumRow_foldr_length]

theorem freezeExpand_of_no_site (s : Expr) (frozen : FreezeSet) (count : Nat)
    (hSite : expansionSite s.values = none) :
    freezeExpand s frozen count = s.take (s.values.length - 1) := by
  apply Expr.ext
  simp [freezeExpandRaw, hSite]
  rfl

end ZeroY.NoLift
