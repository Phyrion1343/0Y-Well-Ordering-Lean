import ZeroY.NoLift.Prefix
import ZeroY.NoLift.FiniteChoices
import ZeroY.NoLift.WellFounded

/-!
# Structural properties of certified steps

At each fixed input, finitely many prefix-monotone families cover all certified
outputs. The covering families may include outputs which do not pass a descent
certificate. Every actual step is strictly lexicographically smaller, retains
the input's proper prefix, and has a nonempty input. Deleting the final entry
is always an available certified step from a nonempty input.
-/

namespace ZeroY.NoLift

theorem checkDescent_nonempty {smaller larger : Expr} {certificate : DescentCertificate}
    (hCheck : checkDescent smaller larger certificate = true) : larger.values ≠ [] := by
  cases certificate with
  | ancestry index =>
      simp only [checkDescent, Bool.and_eq_true, decide_eq_true_eq] at hCheck
      exact hCheck.1
  | ordinaryPath indices =>
      simp only [checkDescent, checkPath, Bool.and_eq_true, decide_eq_true_eq] at hCheck
      exact hCheck.1.1

theorem certifiedStep_nonempty {policy : FreezePolicy} {smaller larger : Expr}
    (hStep : CertifiedStep policy smaller larger) : larger.values ≠ [] := by
  rcases hStep with ⟨proposal, hCheck, _⟩
  simp only [checkProposal, Bool.and_eq_true] at hCheck
  exact checkDescent_nonempty hCheck.2

theorem certifiedStep_lt {policy : FreezePolicy} {smaller larger : Expr}
    (hStep : CertifiedStep policy smaller larger) : ExprLt smaller larger := by
  have hNonempty := certifiedStep_nonempty hStep
  rcases hStep with ⟨proposal, _, rfl⟩
  exact freezeExpand_lt larger proposal.frozen proposal.count hNonempty

theorem certifiedStep_preserves_prefix {policy : FreezePolicy} {smaller larger : Expr}
    (hStep : CertifiedStep policy smaller larger) :
    (larger.values.take (larger.values.length - 1)).IsPrefix smaller.values := by
  rcases hStep with ⟨proposal, _, rfl⟩
  exact freezeExpand_preserves_prefix larger proposal.frozen proposal.count

theorem certifiedStep_length_ge_pred {policy : FreezePolicy} {smaller larger : Expr}
    (hStep : CertifiedStep policy smaller larger) :
    larger.values.length - 1 ≤ smaller.values.length :=
  (by simpa only [List.length_take, Nat.min_eq_left (Nat.sub_le larger.values.length 1)]
    using (certifiedStep_preserves_prefix hStep).length_le)

theorem certifiedStep_delete (policy : FreezePolicy) (input : Expr)
    (hNonempty : input.values ≠ []) :
    CertifiedStep policy (input.take (input.values.length - 1)) input := by
  refine ⟨ordinaryProposal 0, checkProposal_ordinary policy input 0 hNonempty, ?_⟩
  simp only [ordinaryProposal, Proposal.result, freezeExpand_zero]

/-- Finite families cover outputs, without asserting that every family member
passes the descent checker for every expansion parameter. -/
def certifiedFamilies (policy : FreezePolicy) (input : Expr) : List (Nat → Expr) :=
  (frozenFamilies policy input).map (fun frozen => freezeExpand input frozen)

theorem certifiedFamilies_prefix (policy : FreezePolicy) (input : Expr)
    {family : Nat → Expr} (hFamily : family ∈ certifiedFamilies policy input)
    {smaller larger : Nat} (hCount : smaller ≤ larger) :
    (family smaller).values.IsPrefix (family larger).values := by
  rcases List.mem_map.mp hFamily with ⟨frozen, _, rfl⟩
  exact freezeExpand_prefix input frozen hCount

theorem certifiedStep_covered {policy : FreezePolicy} {smaller larger : Expr}
    (hStep : CertifiedStep policy smaller larger) :
    ∃ family ∈ certifiedFamilies policy larger, ∃ count, smaller = family count := by
  rcases hStep with ⟨proposal, hCheck, rfl⟩
  obtain ⟨chosen, hChosen, hEqual⟩ :=
    frozenFamilies_cover policy larger proposal.frozen (checkProposal_valid hCheck)
  refine ⟨freezeExpand larger chosen, List.mem_map.mpr ⟨chosen, hChosen, rfl⟩,
    proposal.count, ?_⟩
  exact hEqual proposal.count

/-- Allowing either policy gives exactly the internal policy's certified
candidate relation; this says nothing about independently chosen minima. -/
theorem eitherStep_iff_internal {smaller larger : Expr} :
    EitherStep smaller larger ↔ CertifiedStep .internal smaller larger := by
  constructor
  · rintro ⟨policy, hStep⟩
    cases policy with
    | internal => exact hStep
    | directRoot => exact certifiedStep_direct_implies_internal hStep
  · exact fun hStep => ⟨.internal, hStep⟩

theorem eitherStep_nonempty {smaller larger : Expr} (hStep : EitherStep smaller larger) :
    larger.values ≠ [] := certifiedStep_nonempty (eitherStep_iff_internal.mp hStep)

theorem eitherStep_lt {smaller larger : Expr} (hStep : EitherStep smaller larger) :
    ExprLt smaller larger := certifiedStep_lt (eitherStep_iff_internal.mp hStep)

theorem eitherStep_preserves_prefix {smaller larger : Expr}
    (hStep : EitherStep smaller larger) :
    (larger.values.take (larger.values.length - 1)).IsPrefix smaller.values :=
  certifiedStep_preserves_prefix (eitherStep_iff_internal.mp hStep)

theorem eitherStep_delete (input : Expr) (hNonempty : input.values ≠ []) :
    EitherStep (input.take (input.values.length - 1)) input :=
  eitherStep_iff_internal.mpr (certifiedStep_delete .internal input hNonempty)

theorem eitherStep_covered {smaller larger : Expr} (hStep : EitherStep smaller larger) :
    ∃ family ∈ certifiedFamilies .internal larger, ∃ count, smaller = family count :=
  certifiedStep_covered (eitherStep_iff_internal.mp hStep)

end ZeroY.NoLift
