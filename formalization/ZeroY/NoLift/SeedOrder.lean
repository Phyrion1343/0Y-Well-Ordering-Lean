import ZeroY.NoLift.Lexicographic
import ZeroY.Seed

/-!
# Compatibility of the unchanged standard seeds

Seeds have only two entries, so neither freezing policy has any candidate at a
seed. Their ordinary first expansion connects consecutive seed heights. These
facts supply the extra compatibility needed to combine the well-orders of the
individual descendant sets; a union of well-orders alone would not suffice.
-/

namespace ZeroY.NoLift

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

universe u

theorem freezeCandidate_false_of_length_le_two (policy : FreezePolicy) (input : Expr)
    (hLength : input.values.length ≤ 2) (edge : Nat × Nat) :
    freezeCandidate policy input edge = false := by
  apply Bool.eq_false_iff.mpr
  intro hCandidate
  unfold freezeCandidate at hCandidate
  cases hSite : expansionSite input.values with
  | none => simp [hSite] at hCandidate
  | some site =>
      rcases site with ⟨height, root⟩
      simp only [hSite, Bool.and_eq_true, decide_eq_true_eq] at hCandidate
      omega

theorem frozenValid_eq_nil_of_length_le_two {policy : FreezePolicy} {input : Expr}
    {frozen : FreezeSet} (hLength : input.values.length ≤ 2)
    (hValid : FrozenValid policy input frozen) : frozen = [] := by
  cases frozen with
  | nil => rfl
  | cons edge rest =>
      have h := hValid.2 edge List.mem_cons_self
      rw [freezeCandidate_false_of_length_le_two policy input hLength edge] at h
      contradiction

theorem certifiedStep_of_ordinary (policy : FreezePolicy) (input : Expr) (count : Nat)
    (hNonempty : input.values ≠ []) :
    CertifiedStep policy (expandY input count) input := by
  refine ⟨ordinaryProposal count, checkProposal_ordinary policy input count hNonempty, ?_⟩
  simp [ordinaryProposal, Proposal.result]

/-- At a seed every certified numerical output is an ordinary expansion. -/
theorem certifiedStep_seed_iff (policy : FreezePolicy) (height : Nat) (output : Expr) :
    CertifiedStep policy output (Expr.seed height) ↔
      ∃ count, output = expandY (Expr.seed height) count := by
  constructor
  · rintro ⟨proposal, hCheck, hResult⟩
    have hFrozen : proposal.frozen = [] :=
      frozenValid_eq_nil_of_length_le_two (by simp [Expr.seed]) (checkProposal_valid hCheck)
    refine ⟨proposal.count, ?_⟩
    simpa only [Proposal.result, hFrozen, freezeExpand_nil] using hResult
  · rintro ⟨count, rfl⟩
    exact certifiedStep_of_ordinary policy _ count (by simp [Expr.seed])

theorem expandY_seed_succ_one (height : Nat) :
    expandY (Expr.seed (height + 1)) 1 = Expr.seed height := by
  apply encode_injective
  rw [encode_expandY, encode_seed, encode_seed]
  exact YesMetaZFC.BMS.validSeed_succ_expand_one height

/-- Every positive expansion of a seed extends the previous seed. -/
theorem seed_prefix_expandY_succ (height : Nat) {count : Nat} (hCount : 0 < count) :
    (Expr.seed height).values.IsPrefix (expandY (Expr.seed (height + 1)) count).values := by
  have h := freezeExpand_prefix (Expr.seed (height + 1)) [] (by omega : 1 ≤ count)
  simpa only [freezeExpand_nil, expandY_seed_succ_one] using h

theorem seed_lt_of_height_lt {first second : Nat} (hHeight : first < second) :
    ExprLt (Expr.seed first) (Expr.seed second) :=
  SeqLt.tail 1 (SeqLt.head (by omega))

theorem seed_lt_iff_height_lt (first second : Nat) :
    ExprLt (Expr.seed first) (Expr.seed second) ↔ first < second := by
  constructor
  · intro h
    cases h with
    | head h => omega
    | tail _ h =>
        cases h with
        | head h => omega
        | tail _ h => cases h
  · exact seed_lt_of_height_lt

/-- The lower seed is a certified descendant of every higher seed. -/
theorem seed_descendant_of_le (policy : FreezePolicy) {lower upper : Nat}
    (hHeight : lower ≤ upper) :
    Order.Descendant (CertifiedStep policy) (Expr.seed upper) (Expr.seed lower) := by
  induction upper generalizing lower with
  | zero =>
      have h : lower = 0 := by omega
      subst lower
      exact .refl _
  | succ upper ih =>
      by_cases hEqual : lower = upper + 1
      · subst lower; exact .refl _
      · have hFirst : CertifiedStep policy (Expr.seed upper) (Expr.seed (upper + 1)) := by
          rw [← expandY_seed_succ_one upper]
          exact certifiedStep_of_ordinary policy _ 1 (by simp [Expr.seed])
        exact (Order.Descendant.single hFirst).trans (ih (by omega))

/-- Seed descendant sets fit together as lexicographic initial segments.
The endpoint may be nonstandard for the ordinary expansion rule. -/
theorem seed_descendant_below {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (policy : FreezePolicy)
    {lower upper : Nat} {target : Expr}
    (hPath : Order.Descendant (CertifiedStep policy) (Expr.seed upper) target)
    (hLess : ExprLt target (Expr.seed lower)) :
    Order.Descendant (CertifiedStep policy) (Expr.seed lower) target := by
  let prefixSystem := certifiedPrefixFamilySystem system policy
  induction upper generalizing target with
  | zero => exact (seed_descendant_of_le policy (Nat.zero_le lower)).trans hPath
  | succ upper ih =>
      by_cases hHeight : upper + 1 ≤ lower
      · exact (seed_descendant_of_le policy hHeight).trans hPath
      · have hLower : lower ≤ upper := by omega
        cases hPath with
        | refl =>
            have h := (seed_lt_iff_height_lt (upper + 1) lower).mp hLess
            omega
        | @step _ child _ hStep hRest =>
            obtain ⟨count, hChild⟩ := (certifiedStep_seed_iff policy (upper + 1) child).mp hStep
            rw [hChild] at hRest
            cases count with
            | zero =>
                have hZero : expandY (Expr.seed (upper + 1)) 0 = (Expr.seed lower).take 1 := by
                  rw [expandY_zero]
                  apply Expr.ext
                  simp [Expr.seed, Expr.take]
                rw [hZero] at hRest
                exact (Order.descendant_take prefixSystem (Expr.seed lower) 1).trans hRest
            | succ count =>
                have hBelow : ExprLt target (Expr.seed upper) := by
                  rcases Nat.lt_or_eq_of_le hLower with hStrict | hEqual
                  · exact exprLt_trans hLess (seed_lt_of_height_lt hStrict)
                  · simpa only [hEqual] using hLess
                have hPrevious := Order.prefix_barrier prefixSystem hRest
                  (seed_prefix_expandY_succ upper (Nat.succ_pos count)) hBelow
                exact ih hPrevious hLess

/-- Generation by these certified rules, not an assertion of ordinary
standardness. The starting points are the unchanged ordinary standard seeds. -/
def CertifiedGenerated (policy : FreezePolicy) (input : Expr) : Prop :=
  ∃ height, Order.Descendant (CertifiedStep policy) (Expr.seed height) input

abbrev CertifiedGeneratedExpr (policy : FreezePolicy) :=
  {input : Expr // CertifiedGenerated policy input}

def CertifiedGeneratedLt {policy : FreezePolicy}
    (first second : CertifiedGeneratedExpr policy) : Prop := ExprLt first.val second.val

theorem certifiedGenerated_minimum {Label : Type u} {frame : StabilityFrame Label}
    (system : RepresentationDescentSystem frame) (policy : FreezePolicy) :
    Order.LexMinimumProperty (CertifiedGenerated policy) := by
  intro subset hExists
  obtain ⟨start, ⟨height, hStart⟩, hSubset⟩ := hExists
  obtain ⟨least, hLeast, hSubsetLeast, hMinimum⟩ :=
    Order.descendants_minimum (certifiedPrefixFamilySystem system policy)
      (Expr.seed height) subset ⟨start, hStart, hSubset⟩
  refine ⟨least, ⟨height, hLeast⟩, hSubsetLeast, ?_⟩
  rintro candidate ⟨otherHeight, hCandidate⟩ hSubsetCandidate hLess
  have hBelow : ExprLt candidate (Expr.seed height) := by
    rcases Order.descendant_eq_or_lt (certifiedPrefixFamilySystem system policy) hLeast with
      hEqual | hStrict
    · simpa only [hEqual] using hLess
    · exact exprLt_trans hLess hStrict
  exact hMinimum candidate (seed_descendant_below system policy hCandidate hBelow)
    hSubsetCandidate hLess

/-- Both policies' entire generated sets are lexicographically well-ordered,
including the union over all finite seed heights. -/
theorem certifiedGenerated_strictWellOrder {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (policy : FreezePolicy) :
    StrictWellOrder (CertifiedGeneratedExpr policy) CertifiedGeneratedLt where
  wellFounded := Order.wellFounded_of_minimum (certifiedGenerated_minimum system policy)
  transitive := fun first second => exprLt_trans first second
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

/-- Any further rule whose returned steps carry one of the two certificates
inherits the generated-set result, even when it removes ordinary steps. -/
theorem restrictedGenerated_strictWellOrder {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (rule : Expr → Expr → Prop)
    (hCertified : ∀ {smaller larger}, rule smaller larger → EitherStep smaller larger) :
    StrictWellOrder {s : Expr // ∃ height, Order.Descendant rule (Expr.seed height) s}
      (fun first second => ExprLt first.val second.val) where
  wellFounded := by
    let embed : {s : Expr // ∃ height, Order.Descendant rule (Expr.seed height) s} →
        CertifiedGeneratedExpr .internal := fun s =>
      ⟨s.val, by
        obtain ⟨height, hPath⟩ := s.property
        exact ⟨height, descendant_map
          (fun h => eitherStep_iff_internal.mp (hCertified h)) hPath⟩⟩
    exact wellFounded_of_relation_map embed (fun h => h)
      (certifiedGenerated_strictWellOrder system .internal).wellFounded
  transitive := fun first second => exprLt_trans first second
  trichotomy := by
    intro first second
    rcases exprLt_trichotomy first.val second.val with hEqual | hLess | hGreater
    · exact Or.inl (Subtype.ext hEqual)
    · exact Or.inr (Or.inl hLess)
    · exact Or.inr (Or.inr hGreater)

end ZeroY.NoLift
