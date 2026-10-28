import ZeroY.NoLift.SeedOrder
import BMSConstructibleBridge.FinalAssembly

/-!
Model-free final statements for the two certified frozen-expansion relations.
These theorems instantiate the same constructed BMS descent model as the
ordinary 0-Y development. The finite-prefix-family theorem additionally gives
lexicographic well-ordering of every fixed root's certified descendants and
of the generated sets obtained from all finite standard seeds.
-/

namespace ZeroY.NoLift.Concrete

open YesMetaZFC.BMS.ConstructibleBridge
open YesMetaZFC.BMS.StabilityFrame

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

theorem internalDescendants_strictWellOrder (root : Expr) :
    StrictWellOrder (CertifiedDescendant .internal root) CertifiedDescendantLt :=
  certifiedDescendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem .internal root

theorem directRootDescendants_strictWellOrder (root : Expr) :
    StrictWellOrder (CertifiedDescendant .directRoot root) CertifiedDescendantLt :=
  certifiedDescendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem .directRoot root

theorem eitherDescendants_strictWellOrder (root : Expr) :
    StrictWellOrder (EitherDescendant root) EitherDescendantLt :=
  ZeroY.NoLift.eitherDescendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem root

theorem restrictedDescendants_strictWellOrder (rule : Expr → Expr → Prop)
    (hCertified : ∀ {smaller larger}, rule smaller larger → EitherStep smaller larger)
    (root : Expr) :
    StrictWellOrder {s : Expr // Order.Descendant rule root s}
      (fun first second => ExprLt first.val second.val) :=
  ZeroY.NoLift.restrictedDescendants_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem rule hCertified root

theorem internalGenerated_strictWellOrder :
    StrictWellOrder (CertifiedGeneratedExpr .internal) CertifiedGeneratedLt :=
  certifiedGenerated_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem .internal

theorem directRootGenerated_strictWellOrder :
    StrictWellOrder (CertifiedGeneratedExpr .directRoot) CertifiedGeneratedLt :=
  certifiedGenerated_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem .directRoot

theorem eitherGenerated_strictWellOrder :
    StrictWellOrder {s : Expr // ∃ height, Order.Descendant EitherStep (Expr.seed height) s}
      (fun first second => ExprLt first.val second.val) :=
  restrictedGenerated_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem EitherStep (fun h => h)

theorem restrictedGenerated_strictWellOrder (rule : Expr → Expr → Prop)
    (hCertified : ∀ {smaller larger}, rule smaller larger → EitherStep smaller larger) :
    StrictWellOrder {s : Expr // ∃ height, Order.Descendant rule (Expr.seed height) s}
      (fun first second => ExprLt first.val second.val) :=
  ZeroY.NoLift.restrictedGenerated_strictWellOrder
    reflectionData_l.wellOrderingModel.representationDescentSystem rule hCertified

end ZeroY.NoLift.Concrete
