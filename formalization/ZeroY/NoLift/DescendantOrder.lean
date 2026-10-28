import ZeroY.Dynamics.Prefix
import ZeroY.SequenceOrder

/-!
# Lexicographic well-order of descendants of prefix-family systems

A family need only cover the actual steps: some of its parameters may fail a
certificate. The proof therefore does not assume that a selector chooses the
same family at every parameter.
-/

namespace ZeroY.NoLift.Order

/-- Finite paths, including their starting point. Edges point from result to input. -/
inductive Descendant (R : Expr → Expr → Prop) : Expr → Expr → Prop
  | refl (root : Expr) : Descendant R root root
  | step {root child target : Expr} (first : R child root)
      (rest : Descendant R child target) : Descendant R root target

namespace Descendant

theorem single {R : Expr → Expr → Prop} {child root : Expr} (h : R child root) :
    Descendant R root child := .step h (.refl _)

theorem trans {R : Expr → Expr → Prop} {root middle target : Expr}
    (first : Descendant R root middle) (second : Descendant R middle target) :
    Descendant R root target := by
  induction first with
  | refl => exact second
  | step h _ ih => exact .step h (ih second)

end Descendant

/-- The hypotheses concern a relation, not a particular search implementation. -/
structure PrefixFamilySystem (R : Expr → Expr → Prop) where
  wellFounded : WellFounded R
  step_lt : ∀ {smaller larger}, R smaller larger → ExprLt smaller larger
  step_prefix : ∀ {smaller larger}, R smaller larger →
    (larger.values.take (larger.values.length - 1)).IsPrefix smaller.values
  drop_step : ∀ s, s.values ≠ [] → R (s.take (s.values.length - 1)) s
  families : Expr → List (Nat → Expr)
  family_prefix : ∀ root family, family ∈ families root →
    ∀ {n m : Nat}, n ≤ m → (family n).values.IsPrefix (family m).values
  cover : ∀ {child root}, R child root →
    ∃ family ∈ families root, ∃ n, child = family n

private theorem prefix_eq_or_lt {first second : Expr}
    (h : first.values.IsPrefix second.values) : first = second ∨ ExprLt first second := by
  rcases h with ⟨tail, hTail⟩
  cases tail with
  | nil => exact Or.inl (Expr.ext (by simpa using hTail))
  | cons value rest =>
      apply Or.inr
      unfold ExprLt
      rw [← hTail]
      have h : SeqLt (first.values ++ []) (first.values ++ value :: rest) :=
        (SeqLt.prefix_iff first.values [] (value :: rest)).mpr (.nil _ _)
      simpa using h

private theorem prefix_not_lt {first second : Expr}
    (h : first.values.IsPrefix second.values) : ¬ ExprLt second first := by
  rcases prefix_eq_or_lt h with hEq | hLt
  · subst second; exact exprLt_irrefl _
  · exact fun hReverse => exprLt_irrefl _ (exprLt_trans hLt hReverse)

private theorem prefix_pred_of_ne {first second : Expr}
    (h : first.values.IsPrefix second.values) (hNe : first ≠ second) :
    first.values.IsPrefix (second.values.take (second.values.length - 1)) := by
  have hLe := h.length_le
  have hStrict : first.values.length < second.values.length := by
    by_cases hEq : first.values.length = second.values.length
    · have hValues := List.prefix_iff_eq_take.mp h
      rw [hEq, List.take_length] at hValues
      exact False.elim (hNe (Expr.ext hValues))
    · omega
  apply List.prefix_iff_eq_take.mpr
  rw [List.take_take, Nat.min_eq_left (by omega : first.values.length ≤ second.values.length - 1)]
  exact List.prefix_iff_eq_take.mp h

theorem descendant_eq_or_lt {R : Expr → Expr → Prop}
    (system : PrefixFamilySystem R) {root target : Expr}
    (h : Descendant R root target) : target = root ∨ ExprLt target root := by
  induction h with
  | refl => exact Or.inl rfl
  | step hStep _ ih =>
      apply Or.inr
      rcases ih with hEq | hLt
      · subst hEq; exact system.step_lt hStep
      · exact exprLt_trans hLt (system.step_lt hStep)

/-- Dropping final entries makes every prefix reachable. -/
theorem descendant_take {R : Expr → Expr → Prop} (system : PrefixFamilySystem R)
    (s : Expr) (count : Nat) : Descendant R s (s.take count) := by
  generalize hLength : s.values.length = length
  induction length using Nat.strongRecOn generalizing s with
  | ind length ih =>
      by_cases hCount : length ≤ count
      · rw [expr_take_of_length_le s count (by omega)]
        exact .refl _
      · have hLengthPos : 0 < length := by omega
        have hMiddleLength : (s.take (s.values.length - 1)).values.length = length - 1 := by
          simp only [Expr.take, List.length_take, hLength, Nat.min_eq_left (Nat.sub_le ..)]
        have hNonempty : s.values ≠ [] := by intro h; simp [h] at hLength; omega
        have hPrior := Descendant.single (system.drop_step s hNonempty)
        have hNext := ih (length - 1) (by omega) (s.take (s.values.length - 1)) hMiddleLength
        rw [expr_take_take, Nat.min_eq_left (by omega : count ≤ s.values.length - 1)] at hNext
        exact hPrior.trans hNext

theorem descendant_of_prefix {R : Expr → Expr → Prop} (system : PrefixFamilySystem R)
    {initial start : Expr} (h : initial.values.IsPrefix start.values) :
    Descendant R start initial := by
  have hEq : start.take initial.values.length = initial :=
    Expr.ext (List.prefix_iff_eq_take.mp h).symm
  rw [← hEq]
  exact descendant_take system _ _

/-- A path cannot cross below a prefix without passing through that prefix. -/
theorem prefix_barrier {R : Expr → Expr → Prop} (system : PrefixFamilySystem R)
    {start target initial : Expr} (hPath : Descendant R start target)
    (hPrefix : initial.values.IsPrefix start.values) (hLess : ExprLt target initial) :
    Descendant R initial target := by
  induction hPath with
  | refl => exact False.elim (prefix_not_lt hPrefix hLess)
  | @step root child target hStep rest ih =>
      by_cases hEq : initial = root
      · subst root; exact .step hStep rest
      · exact ih ((prefix_pred_of_ne hPrefix hEq).trans (system.step_prefix hStep)) hLess

/-- Every nonempty subset has an element with no smaller member. -/
def LexMinimumProperty (P : Expr → Prop) : Prop :=
  ∀ S : Expr → Prop, (∃ x, P x ∧ S x) →
    ∃ m, P m ∧ S m ∧ ∀ t, P t → S t → ¬ ExprLt t m

private theorem minimum_subset {P Q : Expr → Prop} (hP : LexMinimumProperty P)
    (hSub : ∀ x, Q x → P x) : LexMinimumProperty Q := by
  intro S hExists
  obtain ⟨x, hQx, hSx⟩ := hExists
  obtain ⟨m, _, ⟨hQm, hSm⟩, hMin⟩ :=
    hP (fun x => Q x ∧ S x) ⟨x, hSub x hQx, hQx, hSx⟩
  exact ⟨m, hQm, hSm, fun t hQt hSt => hMin t (hSub t hQt) ⟨hQt, hSt⟩⟩

private theorem minimum_singleton (root : Expr) : LexMinimumProperty (· = root) := by
  rintro S ⟨x, hEq, hS⟩
  subst x
  exact ⟨root, rfl, hS, fun t hEq _ => by subst t; exact exprLt_irrefl _⟩

private theorem minimum_union {P Q : Expr → Prop}
    (hP : LexMinimumProperty P) (hQ : LexMinimumProperty Q) :
    LexMinimumProperty (fun x => P x ∨ Q x) := by
  classical
  intro S hExists
  by_cases hPExists : ∃ x, P x ∧ S x
  · obtain ⟨a, hPa, hSa, hA⟩ := hP S hPExists
    by_cases hQExists : ∃ x, Q x ∧ S x
    · obtain ⟨b, hQb, hSb, hB⟩ := hQ S hQExists
      rcases exprLt_trichotomy a b with hEq | hAB | hBA
      · subst b
        exact ⟨a, Or.inl hPa, hSa, fun t hMem hSt =>
          hMem.elim (fun h => hA t h hSt) (fun h => hB t h hSt)⟩
      · refine ⟨a, Or.inl hPa, hSa, ?_⟩
        intro t hMem hSt hLt
        rcases hMem with hPt | hQt
        · exact hA t hPt hSt hLt
        · exact hB t hQt hSt (exprLt_trans hLt hAB)
      · refine ⟨b, Or.inr hQb, hSb, ?_⟩
        intro t hMem hSt hLt
        rcases hMem with hPt | hQt
        · exact hA t hPt hSt (exprLt_trans hLt hBA)
        · exact hB t hQt hSt hLt
    · refine ⟨a, Or.inl hPa, hSa, ?_⟩
      intro t hMem hSt
      rcases hMem with hPt | hQt
      · exact hA t hPt hSt
      · exact False.elim (hQExists ⟨t, hQt, hSt⟩)
  · have hQExists : ∃ x, Q x ∧ S x := by
      obtain ⟨x, hMem, hSx⟩ := hExists
      rcases hMem with hPx | hQx
      · exact False.elim (hPExists ⟨x, hPx, hSx⟩)
      · exact ⟨x, hQx, hSx⟩
    obtain ⟨b, hQb, hSb, hB⟩ := hQ S hQExists
    refine ⟨b, Or.inr hQb, hSb, ?_⟩
    intro t hMem hSt
    rcases hMem with hPt | hQt
    · exact False.elim (hPExists ⟨t, hPt, hSt⟩)
    · exact hB t hQt hSt

private theorem minimum_finite_union {ι : Type} (indices : List ι) (P : ι → Expr → Prop)
    (h : ∀ i ∈ indices, LexMinimumProperty (P i)) :
    LexMinimumProperty (fun x => ∃ i ∈ indices, P i x) := by
  induction indices with
  | nil =>
      intro S hExists
      obtain ⟨x, ⟨i, hMem, _⟩, _⟩ := hExists
      cases hMem
  | cons first rest ih =>
      have hBoth := minimum_union (h first (by simp))
        (ih (fun i hi => h i (by simp [hi])))
      apply minimum_subset hBoth
      rintro x ⟨i, hi, hPi⟩
      rcases List.mem_cons.mp hi with hEq | hRest
      · subst i; exact Or.inl hPi
      · exact Or.inr ⟨i, hRest, hPi⟩

/-- One prefix-increasing family has a minimum even when only some parameters
are accepted. A chosen accepted child contains every smaller rival descendant. -/
private theorem family_minimum {R : Expr → Expr → Prop} (system : PrefixFamilySystem R)
    (root : Expr) (family : Nat → Expr)
    (hFamily : family ∈ system.families root)
    (hChildren : ∀ child, R child root → LexMinimumProperty (Descendant R child)) :
    LexMinimumProperty (fun x => ∃ n, R (family n) root ∧ Descendant R (family n) x) := by
  intro S hExists
  obtain ⟨s, ⟨n, hChild, hDesc⟩, hSs⟩ := hExists
  obtain ⟨least, hLeastDesc, hSLeast, hLeast⟩ :=
    hChildren (family n) hChild S ⟨s, hDesc, hSs⟩
  refine ⟨least, ⟨n, hChild, hLeastDesc⟩, hSLeast, ?_⟩
  rintro t ⟨m, _, hTDesc⟩ hSt hLt
  have hToChild : ExprLt t (family n) := by
    rcases descendant_eq_or_lt system hLeastDesc with hEq | hBelow
    · simpa [hEq] using hLt
    · exact exprLt_trans hLt hBelow
  have hInChild : Descendant R (family n) t := by
    by_cases hMN : m ≤ n
    · exact (descendant_of_prefix system (system.family_prefix root family hFamily hMN)).trans hTDesc
    · exact prefix_barrier system hTDesc
        (system.family_prefix root family hFamily (by omega : n ≤ m)) hToChild
  exact hLeast t hInChild hSt hLt

theorem descendants_minimum {R : Expr → Expr → Prop} (system : PrefixFamilySystem R)
    (root : Expr) : LexMinimumProperty (Descendant R root) := by
  have hAcc := system.wellFounded.apply root
  induction hAcc with
  | intro root _ ih =>
      have hFamilies := minimum_finite_union (system.families root)
        (fun family x => ∃ n, R (family n) root ∧ Descendant R (family n) x)
        (fun family hFamily => family_minimum system root family hFamily ih)
      apply minimum_subset (minimum_union (minimum_singleton root) hFamilies)
      intro x hDesc
      cases hDesc with
      | refl => exact Or.inl rfl
      | @step _ child _ hStep hRest =>
          obtain ⟨family, hFamily, n, hEq⟩ := system.cover hStep
          subst child
          exact Or.inr ⟨family, hFamily, n, hStep, hRest⟩

/-- The minimum principle gives accessibility on the restricted domain. -/
theorem wellFounded_of_minimum {P : Expr → Prop} (h : LexMinimumProperty P) :
    WellFounded (fun a b : {s : Expr // P s} => ExprLt a.val b.val) := by
  classical
  constructor
  intro x
  by_cases hAcc : Acc (fun a b : {s : Expr // P s} => ExprLt a.val b.val) x
  · exact hAcc
  · let S := fun s : Expr => ∃ hs : P s,
        ¬ Acc (fun a b : {s : Expr // P s} => ExprLt a.val b.val) ⟨s, hs⟩
    obtain ⟨m, hPm, hSm, hMin⟩ := h S ⟨x.val, x.property, x.property, hAcc⟩
    obtain ⟨hPm', hNotAcc⟩ := hSm
    apply False.elim
    apply hNotAcc
    apply Acc.intro
    intro t hLt
    by_cases hTAcc : Acc (fun a b : {s : Expr // P s} => ExprLt a.val b.val) t
    · exact hTAcc
    · exact False.elim (hMin t.val t.property ⟨t.property, hTAcc⟩ hLt)

/-- The lexicographic relation on all finite descendants of a fixed root is
well-founded; accepted parameters need not form a prefix or an interval. -/
theorem descendant_lex_wellFounded {R : Expr → Expr → Prop}
    (system : PrefixFamilySystem R) (root : Expr) :
    WellFounded (fun a b : {s : Expr // Descendant R root s} => ExprLt a.val b.val) :=
  wellFounded_of_minimum (descendants_minimum system root)

end ZeroY.NoLift.Order
