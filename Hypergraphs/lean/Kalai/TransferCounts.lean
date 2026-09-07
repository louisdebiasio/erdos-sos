import Kalai.StateEnumeration
import Kalai.AnchoredGluing
import Kalai.LeafTransfer

namespace Kalai

universe u v

variable {Vertex : Type u} {Target : Type u} {Host : Type v}

theorem gluing_count (remaining : List Vertex) (distinct : remaining.Nodup)
    (first second joint : List Vertex → Prop)
    (compatible : GluingCompatible first second joint)
    (jointFirst : ∀ block, joint block → first block) :
    cutCount remaining first + cutCount remaining second ≤
      (cutUniverse remaining).card + cutCount remaining joint := by
  have injectionBound := (cutListing remaining (fun block => first block ∧ ¬ joint block)).card_le_of_injection
    (cutListing remaining (fun block => ¬ second block))
    (enumeratedGluingMap remaining distinct first second joint compatible)
    (enumeratedGluingMap_injective remaining distinct first second joint compatible)
  have firstSplit := (cutUniverse remaining).restrict_card_split
    (fun state => first state.prefix) (fun state => joint state.prefix)
    (fun state _ => jointFirst state.prefix)
  have secondSplit := (cutUniverse remaining).restrict_card_complement
    (fun state => second state.prefix)
  change cutCount remaining (fun block => first block ∧ ¬ joint block) ≤
    cutCount remaining (fun block => ¬ second block) at injectionBound
  change cutCount remaining first =
    cutCount remaining (fun block => first block ∧ ¬ joint block) + cutCount remaining joint at firstSplit
  change cutCount remaining (fun block => ¬ second block) + cutCount remaining second =
    (cutUniverse remaining).card at secondSplit
  omega

theorem anchored_gluing_count (first second joined : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (root : List Target) (rootMap : Target → Host)
    (amalgam : EdgeAmalgam first second joined root) (remaining : List Host)
    (frame : EdgeFirstFrame host root rootMap remaining) :
    cutCount remaining (AnchoredSupport first host root rootMap) +
      cutCount remaining (AnchoredSupport second host root rootMap) ≤
      (cutUniverse remaining).card + cutCount remaining (AnchoredSupport joined host root rootMap) :=
  gluing_count remaining (frame.remaining_nodup host root rootMap remaining)
    (AnchoredSupport first host root rootMap) (AnchoredSupport second host root rootMap)
    (AnchoredSupport joined host root rootMap)
    (anchored_gluing_compatible first second joined host root rootMap amalgam)
    (anchoredSupport_joined_first first second joined host root rootMap amalgam)

noncomputable def shadowOrderingListing (host : FiniteHypergraph Host) (face remaining : List Host) :=
  (orderingUniverse remaining).restrict (fun _ => FaceInShadow host face)

noncomputable def shadowOrderingCount (host : FiniteHypergraph Host) (face remaining : List Host) : Nat :=
  (shadowOrderingListing host face remaining).card

theorem leaf_transfer_count (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining) :
    markedCount remaining (SupportsAt smaller host face faceMap oldEndpoint) ≤
      markedCount remaining (SupportsAt larger host face faceMap newVertex) +
      shadowOrderingCount host (face.map faceMap) remaining :=
  (markedListing remaining (SupportsAt smaller host face faceMap oldEndpoint)).card_le_add_of_injection
    (markedListing remaining (SupportsAt larger host face faceMap newVertex))
    (shadowOrderingListing host (face.map faceMap) remaining)
    (leafTransferMap smaller larger host face faceMap oldEndpoint newVertex extension remaining frame)
    (leafTransferMap_injective smaller larger host face faceMap oldEndpoint newVertex extension remaining frame)

theorem shadowOrderingCount_le (host : FiniteHypergraph Host) (face remaining : List Host) :
    shadowOrderingCount host face remaining ≤ (orderingUniverse remaining).card :=
  (shadowOrderingListing host face remaining).card_le_of_injection (orderingUniverse remaining)
    (fun source => ⟨source.val, source.property.1⟩)
    (fun _ _ same => Subtype.ext
      (congrArg (fun word : {word : List Host // word.Perm remaining} => word.val) same))

theorem shadowOrderingCount_of_shadow (host : FiniteHypergraph Host) (face remaining : List Host)
    (inShadow : FaceInShadow host face) :
    shadowOrderingCount host face remaining = (orderingUniverse remaining).card := by
  apply Nat.le_antisymm (shadowOrderingCount_le host face remaining)
  exact (orderingUniverse remaining).card_le_of_injection (shadowOrderingListing host face remaining)
    (fun source => ⟨source.val, source.property, inShadow⟩)
    (fun _ _ same => Subtype.ext
      (congrArg (fun word : ShadowOrderings host face remaining => word.val) same))

theorem shadowOrderingCount_of_not_shadow (host : FiniteHypergraph Host) (face remaining : List Host)
    (notInShadow : ¬ FaceInShadow host face) : shadowOrderingCount host face remaining = 0 := by
  have empty : (shadowOrderingListing host face remaining).values = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro word present
    exact notInShadow (((shadowOrderingListing host face remaining).membership word).mp present).2
  exact congrArg List.length empty

theorem leaf_transfer_count_orderings (smaller larger : FiniteHypergraph Target)
    (host : FiniteHypergraph Host) (face : List Target) (faceMap : Target → Host)
    (oldEndpoint newVertex : Target)
    (extension : LeafExtension smaller larger face oldEndpoint newVertex)
    (remaining : List Host) (frame : FaceFrame host (face.map faceMap) remaining) :
    markedCount remaining (SupportsAt smaller host face faceMap oldEndpoint) ≤
      markedCount remaining (SupportsAt larger host face faceMap newVertex) +
      (orderingUniverse remaining).card :=
  Nat.le_trans (leaf_transfer_count smaller larger host face faceMap oldEndpoint newVertex extension remaining frame)
    (Nat.add_le_add_left (shadowOrderingCount_le host (face.map faceMap) remaining) _)

theorem cutCount_eq_zero_of_unsupported (remaining : List Vertex) (support : List Vertex → Prop)
    (unsupported : ∀ state : Cut Vertex, state.word.Perm remaining → ¬ support state.prefix) :
    cutCount remaining support = 0 := by
  have empty : (cutListing remaining support).values = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro state present
    have supported := ((cutListing remaining support).membership state).mp present
    exact unsupported state supported.1 supported.2
  exact congrArg List.length empty

theorem markedCount_eq_zero_of_unsupported (remaining : List Vertex) (support : MarkedCut Vertex → Prop)
    (unsupported : ∀ state : MarkedCut Vertex, state.word.Perm remaining → ¬ support state) :
    markedCount remaining support = 0 := by
  have empty : (markedListing remaining support).values = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro state present
    have supported := ((markedListing remaining support).membership state).mp present
    exact unsupported state supported.1 supported.2
  exact congrArg List.length empty

end Kalai
