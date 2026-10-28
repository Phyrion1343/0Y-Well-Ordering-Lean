import ZeroY.NoLift.Construction
import ZeroY.NoLift.Certificate

/-!
# Certified steps for both no-lift policies

The numerical result is the explicit frozen mountain construction. A finite
certificate is checked on that result, not on a caller-supplied graph. Source
template checks and search heuristics can further restrict these steps without
affecting the theorem. This file does not identify the JavaScript search with
a Lean executable, or assert lexicographic well-ordering of its descendants.
-/

namespace ZeroY.NoLift

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame
open ZeroY.Experimental

universe u

/-- A proposal contains data only; the verifier recomputes its output. -/
structure Proposal where
  count : Nat
  frozen : FreezeSet
  certificate : DescentCertificate

def Proposal.result (proposal : Proposal) (input : Expr) : Expr :=
  freezeExpand input proposal.frozen proposal.count

def frozenCheck (policy : FreezePolicy) (input : Expr) (frozen : FreezeSet) : Bool :=
  decide frozen.Nodup && frozen.all (freezeCandidate policy input)

theorem frozenCheck_iff (policy : FreezePolicy) (input : Expr) (frozen : FreezeSet) :
    frozenCheck policy input frozen = true ↔ FrozenValid policy input frozen := by
  simp [frozenCheck, FrozenValid, List.all_eq_true]

/-- The ancestor branch compares with the ordinary expansion at this count. -/
def matchesCount (count : Nat) : DescentCertificate → Bool
  | .ancestry referenceCount => count == referenceCount
  | .ordinaryPath _ => true

/-- Concrete candidate restrictions, followed by a checked descent witness. -/
def checkProposal (policy : FreezePolicy) (input : Expr) (proposal : Proposal) : Bool :=
  frozenCheck policy input proposal.frozen &&
    matchesCount proposal.count proposal.certificate &&
    checkDescent (proposal.result input) input proposal.certificate

theorem checkProposal_sound {policy : FreezePolicy} {input : Expr} {proposal : Proposal}
    (h : checkProposal policy input proposal = true) :
    MixedYStep (proposal.result input) input := by
  have hParts := h
  simp only [checkProposal, Bool.and_eq_true] at hParts
  exact checkDescent_sound hParts.2

theorem checkProposal_valid {policy : FreezePolicy} {input : Expr} {proposal : Proposal}
    (h : checkProposal policy input proposal = true) :
    FrozenValid policy input proposal.frozen := by
  have hParts := h
  simp only [checkProposal, Bool.and_eq_true] at hParts
  exact (frozenCheck_iff _ _ _).mp hParts.1.1

/-- A certified no-lift step, with the relation directed from result to input. -/
def CertifiedStep (policy : FreezePolicy) (smaller larger : Expr) : Prop :=
  ∃ proposal, checkProposal policy larger proposal = true ∧
    smaller = proposal.result larger

theorem certifiedStep_mixed {policy : FreezePolicy} {smaller larger : Expr}
    (h : CertifiedStep policy smaller larger) : MixedYStep smaller larger := by
  rcases h with ⟨proposal, hChecked, rfl⟩
  exact checkProposal_sound hChecked

theorem checkProposal_direct_implies_internal {input : Expr} {proposal : Proposal}
    (h : checkProposal .directRoot input proposal = true) :
    checkProposal .internal input proposal = true := by
  have hParts := h
  simp only [checkProposal, Bool.and_eq_true] at hParts ⊢
  refine ⟨⟨?_, hParts.1.2⟩, hParts.2⟩
  exact (frozenCheck_iff _ _ _).mpr
    (frozenValid_direct_implies_internal (checkProposal_valid h))

/-- Inclusion concerns all certified candidates, not the functions which pick
the lexicographically least candidate under the two different policies. -/
theorem certifiedStep_direct_implies_internal {smaller larger : Expr}
    (h : CertifiedStep .directRoot smaller larger) :
    CertifiedStep .internal smaller larger := by
  rcases h with ⟨proposal, hChecked, hResult⟩
  exact ⟨proposal, checkProposal_direct_implies_internal hChecked, hResult⟩

theorem certifiedStep_wellFounded {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (policy : FreezePolicy) :
    WellFounded (CertifiedStep policy) :=
  wellFounded_of_relation_map id (fun h => certifiedStep_mixed h)
    (mixedYStep_wellFounded system)

/-- Even the choice of policy may change from one step to the next. -/
def EitherStep (smaller larger : Expr) : Prop :=
  ∃ policy, CertifiedStep policy smaller larger

theorem eitherStep_mixed {smaller larger : Expr} (h : EitherStep smaller larger) :
    MixedYStep smaller larger := by
  rcases h with ⟨_, hStep⟩
  exact certifiedStep_mixed hStep

theorem eitherStep_wellFounded {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : WellFounded EitherStep :=
  wellFounded_of_relation_map id (fun h => eitherStep_mixed h)
    (mixedYStep_wellFounded system)

theorem no_infinite_certified_chain {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → Expr, ∀ index, EitherStep (chain (index + 1)) (chain index) := by
  rintro ⟨chain, hSteps⟩
  exact no_infinite_mixedYStep_chain system
    ⟨chain, fun index => eitherStep_mixed (hSteps index)⟩

/-- Parameters, frozen sets, certificate kind and policy may all vary. -/
theorem certified_trajectory_terminates {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (chain : Nat → Expr)
    (hSteps : ∀ index, (chain index).values ≠ [] →
      EitherStep (chain (index + 1)) (chain index)) :
    ∃ index, (chain index).values = [] :=
  mixedTrajectory_terminates system chain
    (fun index hNonempty => eitherStep_mixed (hSteps index hNonempty))

/-- Further source/template filters cannot create an infinite expansion chain. -/
theorem restrictedStep_wellFounded {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (policy : FreezePolicy)
    (restriction : Expr → Expr → Prop) :
    WellFounded (fun smaller larger =>
      CertifiedStep policy smaller larger ∧ restriction smaller larger) :=
  wellFounded_of_relation_map id (fun h => h.1)
    (certifiedStep_wellFounded system policy)

/-- A successful check packages its evidence with the original proposal. -/
structure CheckedProposal (policy : FreezePolicy) (input : Expr) where
  proposal : Proposal
  checked : checkProposal policy input proposal = true

def checkProposal? (policy : FreezePolicy) (input : Expr) (proposal : Proposal) :
    Option (CheckedProposal policy input) :=
  if h : checkProposal policy input proposal = true then some ⟨proposal, h⟩ else none

def ordinaryProposal (count : Nat) : Proposal :=
  ⟨count, [], .ancestry count⟩

theorem checkProposal_ordinary (policy : FreezePolicy) (input : Expr) (count : Nat)
    (hNonempty : input.values ≠ []) :
    checkProposal policy input (ordinaryProposal count) = true := by
  simpa [checkProposal, frozenCheck, ordinaryProposal, Proposal.result, matchesCount] using
    checkDescent_ordinary input count hNonempty

/-- The fallback exists for every nonempty legal input and every finite count. -/
def ordinaryChecked (policy : FreezePolicy) (input : Expr) (count : Nat)
    (hNonempty : input.values ≠ []) : CheckedProposal policy input :=
  ⟨ordinaryProposal count, checkProposal_ordinary policy input count hNonempty⟩

/-- A finite search may apply any extra source filter and preference function.
Each retained result is checked; no supplied graph or descent assertion is
trusted. The ordinary fallback does not require the extra source filter. -/
def chooseCertified (policy : FreezePolicy) (input : Expr) (count : Nat)
    (hNonempty : input.values ≠ []) (proposals : List Proposal)
    (sourceFilter : Proposal → Bool) (prefer : Proposal → Proposal → Bool) :
    CheckedProposal policy input :=
  proposals.foldl (fun best proposal =>
    if proposal.count == count && sourceFilter proposal then
      match checkProposal? policy input proposal with
      | none => best
      | some checked => if prefer proposal best.proposal then checked else best
    else best) (ordinaryChecked policy input count hNonempty)

def CheckedProposal.result {policy : FreezePolicy} {input : Expr}
    (checked : CheckedProposal policy input) : Expr := checked.proposal.result input

theorem CheckedProposal.step {policy : FreezePolicy} {input : Expr}
    (checked : CheckedProposal policy input) :
    CertifiedStep policy checked.result input :=
  ⟨checked.proposal, checked.checked, rfl⟩

/-- Any selection procedure returning a verified proposal inherits termination.
The procedure may use a source filter, a minimum rule, or external search. -/
def Selector (policy : FreezePolicy) :=
  (input : Expr) → input.values ≠ [] → CheckedProposal policy input

def selectedNext {policy : FreezePolicy} (select : Selector policy) (input : Expr) : Expr :=
  if h : input.values = [] then input else (select input h).result

def selectedTrajectory {policy : FreezePolicy} (select : Selector policy) (initial : Expr) :
    Nat → Expr
  | 0 => initial
  | step + 1 => selectedNext select (selectedTrajectory select initial step)

theorem selected_trajectory_terminates {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) {policy : FreezePolicy}
    (select : Selector policy) (initial : Expr) :
    ∃ index, (selectedTrajectory select initial index).values = [] := by
  apply certified_trajectory_terminates system
  intro index hNonempty
  refine ⟨policy, ?_⟩
  simpa only [selectedTrajectory, selectedNext, dif_neg hNonempty] using
    (select (selectedTrajectory select initial index) hNonempty).step

end ZeroY.NoLift
