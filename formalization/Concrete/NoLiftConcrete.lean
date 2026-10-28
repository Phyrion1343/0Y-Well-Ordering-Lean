import ZeroY.NoLift.WellFounded
import BMSConstructibleBridge.FinalAssembly

/-!
Model-free final statements for the two certified frozen-expansion relations.
These theorems instantiate the same constructed BMS descent model as the
ordinary 0-Y development. They assert expansion well-foundedness and finite
termination, not lexicographic well-ordering of the new descendant sets.
-/

namespace ZeroY.NoLift.Concrete

open YesMetaZFC.BMS.ConstructibleBridge

theorem internalStep_wellFounded : WellFounded (CertifiedStep .internal) :=
  certifiedStep_wellFounded
    reflectionData_l.wellOrderingModel.representationDescentSystem .internal

theorem directRootStep_wellFounded : WellFounded (CertifiedStep .directRoot) :=
  certifiedStep_wellFounded
    reflectionData_l.wellOrderingModel.representationDescentSystem .directRoot

theorem eitherStep_wellFounded : WellFounded EitherStep :=
  ZeroY.NoLift.eitherStep_wellFounded
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem no_infinite_certified_chain :
    ¬ ∃ chain : Nat → Expr, ∀ index, EitherStep (chain (index + 1)) (chain index) :=
  ZeroY.NoLift.no_infinite_certified_chain
    reflectionData_l.wellOrderingModel.representationDescentSystem

theorem certified_trajectory_terminates (chain : Nat → Expr)
    (hSteps : ∀ index, (chain index).values ≠ [] →
      EitherStep (chain (index + 1)) (chain index)) :
    ∃ index, (chain index).values = [] :=
  ZeroY.NoLift.certified_trajectory_terminates
    reflectionData_l.wellOrderingModel.representationDescentSystem chain hSteps

theorem selected_trajectory_terminates {policy : FreezePolicy}
    (select : Selector policy) (initial : Expr) :
    ∃ index, (selectedTrajectory select initial index).values = [] :=
  ZeroY.NoLift.selected_trajectory_terminates
    reflectionData_l.wellOrderingModel.representationDescentSystem select initial

theorem restrictedStep_wellFounded (policy : FreezePolicy)
    (restriction : Expr → Expr → Prop) :
    WellFounded (fun smaller larger =>
      CertifiedStep policy smaller larger ∧ restriction smaller larger) :=
  ZeroY.NoLift.restrictedStep_wellFounded
    reflectionData_l.wellOrderingModel.representationDescentSystem policy restriction

end ZeroY.NoLift.Concrete
