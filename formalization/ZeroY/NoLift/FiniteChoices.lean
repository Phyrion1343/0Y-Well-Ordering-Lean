import ZeroY.NoLift.Construction

/-!
# Finitely many frozen templates at a fixed input

Different list orders describe the same frozen set. Enumerating all sublists
of the candidate list covers every legal frozen template up to this equality.
No uniform choice of a template across expansion parameters is assumed.
-/

namespace ZeroY.NoLift

def freezeSubsets : FreezeSet → List FreezeSet
  | [] => [[]]
  | edge :: rest => freezeSubsets rest ++ (freezeSubsets rest).map (edge :: ·)

theorem filter_mem_freezeSubsets (allowed : FreezeSet) (test : Nat × Nat → Bool) :
    allowed.filter test ∈ freezeSubsets allowed := by
  induction allowed with
  | nil => simp [freezeSubsets]
  | cons edge rest ih =>
      cases h : test edge <;> simp [freezeSubsets, h, ih]

theorem freezeExpand_eq_of_mem_iff (input : Expr) {first second : FreezeSet}
    (hSame : ∀ edge, edge ∈ first ↔ edge ∈ second) (count : Nat) :
    freezeExpand input first count = freezeExpand input second count := by
  have hContains : ∀ edge, first.contains edge = second.contains edge := by
    intro edge
    exact Bool.eq_iff_iff.mpr (by simpa using hSame edge)
  have hParent : frozenMountainParent first = frozenMountainParent second := by
    funext row parent root last target
    simp only [frozenMountainParent, hContains]
  apply Expr.ext
  simp only [freezeExpand_values, freezeExpandRaw, hParent]

def frozenFamilies (policy : FreezePolicy) (input : Expr) : List FreezeSet :=
  freezeSubsets (freezeCandidates policy input)

/-- A finite list of templates covers every legal frozen output for every
parameter simultaneously, even when the supplied list is in a different order. -/
theorem frozenFamilies_cover (policy : FreezePolicy) (input : Expr)
    (frozen : FreezeSet) (hValid : FrozenValid policy input frozen) :
    ∃ chosen ∈ frozenFamilies policy input,
      ∀ count, freezeExpand input frozen count = freezeExpand input chosen count := by
  let chosen := (freezeCandidates policy input).filter (frozen.contains ·)
  refine ⟨chosen, filter_mem_freezeSubsets _ _, ?_⟩
  intro count
  apply freezeExpand_eq_of_mem_iff
  intro edge
  simp only [chosen, List.mem_filter, List.contains_iff_mem]
  constructor
  · intro hMem
    exact ⟨(mem_freezeCandidates_iff _ _ _).mpr (hValid.2 edge hMem), hMem⟩
  · exact fun h => h.2

end ZeroY.NoLift
