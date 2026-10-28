import ZeroY.BMS.AnyArray
import ZeroY.Expansion.Conjugacy
import ZeroY.Transport

/-!
# 祖先约束弱化的全域终止充分条件

目标矩阵只需有一个严格递增列嵌入，逐行保持到普通展开结果中的祖先关系。
稳定表示可沿该嵌入拉回，故普通展开的表示上界下降仍适用。

这里只证明终止性。没有断言标准性、原序数保持或全局无提升，也没有把
几个复制次数的检查当作所有复制次数的证书。
-/

namespace ZeroY.Experimental

open YesMetaZFC.BMS
open YesMetaZFC.BMS.StabilityFrame

universe u

/-- 按原行号保持祖先关系的严格递增列嵌入；无需保持矩阵数值。 -/
structure AncestorEmbedding (source target : ValidArray) where
  column : Fin source.raw.length → Fin target.raw.length
  increasing : ∀ {left right}, left < right → column left < column right
  ancestor : ∀ {row : Nat} {left right : Fin source.raw.length},
    isAncestor source.raw row left.val right.val = true →
      isAncestor target.raw row (column left).val (column right).val = true

def AncestorEmbedding.refl (array : ValidArray) : AncestorEmbedding array array where
  column := id
  increasing := fun h => h
  ancestor := fun h => h

/-- 等列数情形只需按同一索引检查祖先包含，不必寻找其他嵌入。 -/
def AncestorEmbedding.ofSameColumns {source target : ValidArray}
    (hLength : source.raw.length = target.raw.length)
    (hAncestor : ∀ row left right,
      isAncestor source.raw row left right = true →
        isAncestor target.raw row left right = true) :
    AncestorEmbedding source target where
  column := fun column => ⟨column.val, by rw [← hLength]; exact column.isLt⟩
  increasing := fun h => h
  ancestor := fun h => hAncestor _ _ _ h

/-- 只检查直接父边即可推出全部祖先包含；每条候选父边可以匹配多条参考父边。 -/
theorem ancestor_of_parent_edges {source target : ValidArray}
    (hEdge : ∀ row column found,
      parent row source.raw column = some found →
        isAncestor target.raw row found column = true)
    {row left right : Nat}
    (hAncestor : isAncestor source.raw row left right = true) :
    isAncestor target.raw row left right = true := by
  have hPath := isAncestor_iff_strictAncestor.mp hAncestor
  clear hAncestor
  induction hPath with
  | single h => exact hEdge _ _ _ h
  | tail _ h ih => exact isAncestor_trans (hEdge _ _ _ h) ih

def AncestorEmbedding.ofSameColumnParentEdges {source target : ValidArray}
    (hLength : source.raw.length = target.raw.length)
    (hEdge : ∀ row column found,
      parent row source.raw column = some found →
        isAncestor target.raw row found column = true) :
    AncestorEmbedding source target :=
  .ofSameColumns hLength (fun _ _ _ h => ancestor_of_parent_edges hEdge h)

/-- 祖先保持嵌入允许直接复用目标稳定表示的标签。 -/
def AncestorEmbedding.pullback {Label : Type u} {frame : StabilityFrame Label}
    {source target : ValidArray} (embedding : AncestorEmbedding source target)
    (representation : StableRepresentation frame target) :
    StableRepresentation frame source where
  label := fun column => representation.label (embedding.column column)
  strictlyIncreasing := fun h => representation.strictlyIncreasing (embedding.increasing h)
  preservesAncestor := fun h => representation.preservesAncestor (embedding.ancestor h)

theorem AncestorEmbedding.pullback_bounded {Label : Type u}
    {frame : StabilityFrame Label} {source target : ValidArray}
    (embedding : AncestorEmbedding source target)
    (representation : StableRepresentation frame target) {bound : Label}
    (hBounded : representation.BoundedBy bound) :
    (embedding.pullback representation).BoundedBy bound :=
  fun column => hBounded (embedding.column column)

/-- 关系方向为“新结果，旧输入”；普通展开本身必须非平凡。 -/
def AncestralStep (smaller larger : ValidArray) : Prop :=
  ∃ index, larger.expand index ≠ larger ∧
    Nonempty (AncestorEmbedding smaller (larger.expand index))

private theorem accessible_of_bounded {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    ∀ {bound : Label}, Acc frame.lt bound →
      ∀ {array : ValidArray} (representation : StableRepresentation frame array),
        representation.BoundedBy bound → Acc AncestralStep array := by
  intro bound hAccessible
  induction hAccessible with
  | intro bound _ ih =>
      intro array representation hBounded
      apply Acc.intro array
      rintro smaller ⟨index, hChanged, ⟨embedding⟩⟩
      obtain ⟨smallerBound, hLess, expandedRepresentation, hExpandedBounded⟩ :=
        system.expand_bounded index representation hBounded hChanged
      exact ih smallerBound hLess (embedding.pullback expandedRepresentation)
        (embedding.pullback_bounded expandedRepresentation hExpandedBounded)

/-- 任意矩阵上的祖先约束弱化关系良基，不需要标准生成性或往返可逆性。 -/
theorem ancestralStep_wellFounded {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    WellFounded AncestralStep := by
  constructor
  intro array
  obtain ⟨bound, representation, hBounded⟩ := ZeroY.BMS.exists_bounded_any system array
  exact accessible_of_bounded system (frame.lt_wellFounded.apply bound)
    representation hBounded

/-- 一条普通展开的末端可以替换为祖先嵌入该结果的任意矩阵。 -/
theorem ancestralStep_of_step_embedding {reference smaller larger : ValidArray}
    (hStep : Step reference larger) (embedding : AncestorEmbedding smaller reference) :
    AncestralStep smaller larger := by
  rcases hStep with ⟨⟨index, rfl⟩, hChanged⟩
  exact ⟨index, hChanged, ⟨embedding⟩⟩

theorem ancestralStep_of_step {smaller larger : ValidArray}
    (hStep : Step smaller larger) : AncestralStep smaller larger :=
  ancestralStep_of_step_embedding hStep (.refl smaller)

/-- 普通非空有限下降也是祖先弱化关系的非空有限下降。 -/
theorem transGen_ancestralStep_of_strictDescent {smaller larger : ValidArray}
    (hPath : StrictDescent smaller larger) :
    Relation.TransGen AncestralStep smaller larger := by
  induction hPath with
  | single hStep => exact .single (ancestralStep_of_step hStep)
  | tail _ hStep ih =>
      exact (Relation.TransGen.single (ancestralStep_of_step hStep)).trans ih

/-- 多步普通路径末端的祖先投影可并入同一个已良基关系的传递闭包。 -/
theorem transGen_ancestralStep_of_strictDescent_embedding
    {reference smaller larger : ValidArray}
    (hPath : StrictDescent reference larger)
    (embedding : AncestorEmbedding smaller reference) :
    Relation.TransGen AncestralStep smaller larger := by
  cases hPath with
  | single hStep => exact .single (ancestralStep_of_step_embedding hStep embedding)
  | tail prior hStep =>
      exact (Relation.TransGen.single
        (ancestralStep_of_step_embedding hStep embedding)).trans
          (transGen_ancestralStep_of_strictDescent prior)

/-- 每一步检查实际输出的完整编码父图；不要求各步使用同一选择策略。 -/
def AncestralYStep (smaller larger : Expr) : Prop :=
  AncestralStep (encode smaller) (encode larger)

theorem ancestralYStep_wellFounded {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    WellFounded AncestralYStep :=
  wellFounded_of_relation_map encode (fun h => h) (ancestralStep_wellFounded system)

/-- 数值山脉展开与 BMS 的已证交换式将实际候选检查接入抽象关系。 -/
theorem ancestralYStep_of_embedding {smaller larger : Expr} (index : Nat)
    (hChanged : expandY larger index ≠ larger)
    (embedding : AncestorEmbedding (encode smaller) (encode (expandY larger index))) :
    AncestralYStep smaller larger := by
  refine ⟨index, ?_, ?_⟩
  · intro hEqual
    apply hChanged
    apply encode_injective
    rw [encode_expandY]
    exact hEqual
  · rw [← encode_expandY]
    exact ⟨embedding⟩

theorem no_infinite_ancestralYStep_chain {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → Expr,
      ∀ index, AncestralYStep (chain (index + 1)) (chain index) := by
  rintro ⟨chain, hStep⟩
  have hNoChain : ∀ s, Acc AncestralYStep s → ∀ index, chain index ≠ s := by
    intro s hAcc
    induction hAcc with
    | intro s _ ih =>
        intro index hEqual
        apply ih (chain (index + 1))
        · rw [← hEqual]
          exact hStep index
        · rfl
  exact hNoChain _ ((ancestralYStep_wellFounded system).apply (chain 0)) 0 rfl

/-- 任意逐步通过证书的迭代必到空式；参数及冻结集均可逐步改变。 -/
theorem certifiedTrajectory_terminates {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (chain : Nat → Expr)
    (hCertified : ∀ index, (chain index).values ≠ [] →
      AncestralYStep (chain (index + 1)) (chain index)) :
    ∃ index, (chain index).values = [] := by
  apply Classical.byContradiction
  intro hNever
  apply no_infinite_ancestralYStep_chain system
  refine ⟨chain, ?_⟩
  intro index
  apply hCertified index
  intro hEmpty
  exact hNever ⟨index, hEmpty⟩

/-- 允许混合单步祖先证书、多步普通路径与其末端投影；中间矩阵无需可逆。 -/
def MixedYStep (smaller larger : Expr) : Prop :=
  Relation.TransGen AncestralStep (encode smaller) (encode larger)

theorem mixedYStep_of_ancestralYStep {smaller larger : Expr}
    (hStep : AncestralYStep smaller larger) : MixedYStep smaller larger :=
  .single hStep

theorem mixedYStep_of_ordinaryDescent {smaller larger : Expr}
    (hPath : StrictDescent (encode smaller) (encode larger)) :
    MixedYStep smaller larger :=
  transGen_ancestralStep_of_strictDescent hPath

theorem mixedYStep_of_projectedDescent {reference : ValidArray} {smaller larger : Expr}
    (hPath : StrictDescent reference (encode larger))
    (embedding : AncestorEmbedding (encode smaller) reference) :
    MixedYStep smaller larger :=
  transGen_ancestralStep_of_strictDescent_embedding hPath embedding

theorem mixedYStep_wellFounded {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    WellFounded MixedYStep :=
  wellFounded_of_relation_map encode (fun h => h)
    (ancestralStep_wellFounded system).transGen

theorem no_infinite_mixedYStep_chain {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame) :
    ¬ ∃ chain : Nat → Expr, ∀ index, MixedYStep (chain (index + 1)) (chain index) := by
  rintro ⟨chain, hStep⟩
  have hNoChain : ∀ s, Acc MixedYStep s → ∀ index, chain index ≠ s := by
    intro s hAcc
    induction hAcc with
    | intro s _ ih =>
        intro index hEqual
        apply ih (chain (index + 1))
        · rw [← hEqual]
          exact hStep index
        · rfl
  exact hNoChain _ ((mixedYStep_wellFounded system).apply (chain 0)) 0 rfl

/-- 各步可在祖先弱化证书与普通路径证书之间任意切换，迭代仍到空式。 -/
theorem mixedTrajectory_terminates {Label : Type u}
    {frame : StabilityFrame Label} (system : RepresentationDescentSystem frame)
    (chain : Nat → Expr)
    (hCertified : ∀ index, (chain index).values ≠ [] →
      MixedYStep (chain (index + 1)) (chain index)) :
    ∃ index, (chain index).values = [] := by
  apply Classical.byContradiction
  intro hNever
  apply no_infinite_mixedYStep_chain system
  refine ⟨chain, ?_⟩
  intro index
  apply hCertified index
  intro hEmpty
  exact hNever ⟨index, hEmpty⟩

end ZeroY.Experimental
