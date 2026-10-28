import ZeroY.NoLift.StepProperties
import ZeroY.NoLift.DescendantOrder

/-!
# Lexicographic well-ordering of certified descendants

Finite frozen templates, rather than a parameter-independent winning template,
connect expansion well-foundedness to lexicographic well-ordering. This covers
each policy, arbitrary switches between them, and any further restricted rule.
-/

namespace ZeroY.NoLift

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

universe u

def certifiedPrefixFamilySystem {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (policy : FreezePolicy) :
    Order.PrefixFamilySystem (CertifiedStep policy) where
  wellFounded := certifiedStep_wellFounded system policy
  step_lt := fun h => certifiedStep_lt h
  step_prefix := fun h => certifiedStep_preserves_prefix h
  drop_step := certifiedStep_delete policy
  families := certifiedFamilies policy
  family_prefix := by
    intro root family hFamily n m hCount
    exact certifiedFamilies_prefix policy root hFamily hCount
  cover := fun h => certifiedStep_covered h

abbrev CertifiedDescendant (policy : FreezePolicy) (root : Expr) :=
  {s : Expr // Order.Descendant (CertifiedStep policy) root s}

def CertifiedDescendantLt {policy : FreezePolicy} {root : Expr}
    (first second : CertifiedDescendant policy root) : Prop := ExprLt first.val second.val

theorem certifiedDescendants_strictWellOrder {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (policy : FreezePolicy) (root : Expr) :
    StrictWellOrder (CertifiedDescendant policy root) CertifiedDescendantLt where
  wellFounded := Order.descendant_lex_wellFounded (certifiedPrefixFamilySystem system policy) root
  transitive := fun first second => exprLt_trans first second
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

def eitherPrefixFamilySystem {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) : Order.PrefixFamilySystem EitherStep where
  wellFounded := eitherStep_wellFounded system
  step_lt := fun h => eitherStep_lt h
  step_prefix := fun h => eitherStep_preserves_prefix h
  drop_step := eitherStep_delete
  families := certifiedFamilies .internal
  family_prefix := by
    intro root family hFamily n m hCount
    exact certifiedFamilies_prefix .internal root hFamily hCount
  cover := fun h => eitherStep_covered h

abbrev EitherDescendant (root : Expr) := {s : Expr // Order.Descendant EitherStep root s}

def EitherDescendantLt {root : Expr} (first second : EitherDescendant root) : Prop :=
  ExprLt first.val second.val

theorem eitherDescendants_strictWellOrder {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) (root : Expr) :
    StrictWellOrder (EitherDescendant root) EitherDescendantLt where
  wellFounded := Order.descendant_lex_wellFounded (eitherPrefixFamilySystem system) root
  transitive := fun first second => exprLt_trans first second
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

theorem descendant_map {source target : Expr → Expr → Prop}
    (hMap : ∀ {smaller larger}, source smaller larger → target smaller larger)
    {root result : Expr} (hPath : Order.Descendant source root result) :
    Order.Descendant target root result := by
  induction hPath with
  | refl root => exact .refl root
  | step hStep _ ih => exact .step (hMap hStep) ih

/-- Additional source tests, minimization or resource guards may remove steps.
Their descendant sets inherit the proved order, even if they omit deletion. -/
theorem restrictedDescendants_strictWellOrder {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (rule : Expr → Expr → Prop)
    (hCertified : ∀ {smaller larger}, rule smaller larger → EitherStep smaller larger)
    (root : Expr) :
    StrictWellOrder {s : Expr // Order.Descendant rule root s}
      (fun first second => ExprLt first.val second.val) where
  wellFounded := by
    let embed : {s : Expr // Order.Descendant rule root s} → EitherDescendant root :=
      fun s => ⟨s.val, descendant_map hCertified s.property⟩
    exact wellFounded_of_relation_map embed (fun h => h)
      (eitherDescendants_strictWellOrder system root).wellFounded
  transitive := fun first second => exprLt_trans first second
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

end ZeroY.NoLift
