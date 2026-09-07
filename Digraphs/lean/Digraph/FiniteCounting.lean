import Std

namespace Digraph

universe u v w

theorem nodup_map_injective {Domain : Type u} {Codomain : Type v}
    (mapping : Domain → Codomain)
    (injective : ∀ first second, mapping first = mapping second → first = second)
    (values : List Domain) (distinct : values.Nodup) : (values.map mapping).Nodup := by
  change (values.map mapping).Pairwise (fun first second => first ≠ second)
  rw [List.pairwise_map]
  exact distinct.imp (fun different same => different (injective _ _ same))

theorem nodup_length_le_of_subset {Item : Type u} (source target : List Item)
    (distinct : source.Nodup) (contained : ∀ item ∈ source, item ∈ target) :
    source.length ≤ target.length := by
  classical
  induction source generalizing target with
  | nil => simp
  | cons head tail inductionHypothesis =>
    have headPresent := contained head (by simp)
    have tailBound := inductionHypothesis (target.erase head) (List.nodup_cons.mp distinct).2
      (by
        intro item present
        apply (List.mem_erase_of_ne ?_).mpr (contained item (by simp [present]))
        intro same
        exact (List.nodup_cons.mp distinct).1 (same ▸ present))
    have erasedLength := List.length_erase_of_mem headPresent
    have targetPositive : 0 < target.length := List.length_pos_of_mem headPresent
    simp only [List.length_cons]
    omega

noncomputable def uniqueItems {Item : Type u} : List Item → List Item
  | [] => []
  | head :: tail => by
    classical
    exact if head ∈ uniqueItems tail then uniqueItems tail else head :: uniqueItems tail

theorem mem_uniqueItems {Item : Type u} (values : List Item) (item : Item) :
    item ∈ uniqueItems values ↔ item ∈ values := by
  classical
  induction values generalizing item with
  | nil => simp [uniqueItems]
  | cons head tail inductionHypothesis =>
    simp only [uniqueItems]
    split
    · rename_i repeated
      have headPresent := (inductionHypothesis head).mp repeated
      simp only [inductionHypothesis, List.mem_cons]
      constructor
      · exact Or.inr
      · intro present
        rcases present with same | present
        · exact same ▸ headPresent
        · exact present
    · simp [inductionHypothesis]

theorem uniqueItems_nodup {Item : Type u} (values : List Item) :
    (uniqueItems values).Nodup := by
  classical
  induction values with
  | nil => simp [uniqueItems]
  | cons head tail inductionHypothesis =>
    simp only [uniqueItems]
    split <;> simp_all [List.nodup_cons]

structure ListingFor {Item : Type u} (predicate : Item → Prop) where
  values : List Item
  distinct : values.Nodup
  membership : ∀ item, item ∈ values ↔ predicate item

def ListingFor.card {Item : Type u} {predicate : Item → Prop}
    (listing : ListingFor predicate) : Nat := listing.values.length

noncomputable def ListingFor.ofCover {Item : Type u} (candidates : List Item)
    (predicate : Item → Prop) (complete : ∀ item, predicate item → item ∈ candidates) :
    ListingFor predicate := by
  classical
  exact ⟨(uniqueItems candidates).filter (fun item => decide (predicate item)),
    (uniqueItems_nodup candidates).filter _, by
      intro item
      simp only [List.mem_filter, mem_uniqueItems, decide_eq_true_eq]
      exact ⟨fun present => present.2, fun supported => ⟨complete item supported, supported⟩⟩⟩

def ListingFor.attached {Item : Type u} {predicate : Item → Prop}
    (listing : ListingFor predicate) : List {item // predicate item} :=
  listing.values.attachWith predicate (fun item present => (listing.membership item).mp present)

theorem ListingFor.attached_complete {Item : Type u} {predicate : Item → Prop}
    (listing : ListingFor predicate) (item : {item // predicate item}) :
    item ∈ listing.attached := by
  simp only [ListingFor.attached, List.mem_attachWith, listing.membership]
  exact item.property

theorem ListingFor.attached_nodup {Item : Type u} {predicate : Item → Prop}
    (listing : ListingFor predicate) : listing.attached.Nodup := by
  apply List.Pairwise.of_map (S := fun first second => first ≠ second) Subtype.val
    (fun first second different same => different (congrArg Subtype.val same))
  simpa only [ListingFor.attached, List.attachWith_map_subtype_val] using listing.distinct

theorem ListingFor.attached_length {Item : Type u} {predicate : Item → Prop}
    (listing : ListingFor predicate) : listing.attached.length = listing.card := by
  simp [ListingFor.attached, ListingFor.card]

theorem ListingFor.card_le_of_injection {Domain : Type u} {Codomain : Type v}
    {sourcePredicate : Domain → Prop} {targetPredicate : Codomain → Prop}
    (source : ListingFor sourcePredicate) (target : ListingFor targetPredicate)
    (mapping : {item // sourcePredicate item} → {item // targetPredicate item})
    (injective : ∀ first second, mapping first = mapping second → first = second) :
    source.card ≤ target.card := by
  have bound := nodup_length_le_of_subset (source.attached.map mapping) target.attached
    (nodup_map_injective mapping injective source.attached source.attached_nodup)
    (fun item _ => target.attached_complete item)
  simpa only [List.length_map, ListingFor.attached_length] using bound

theorem ListingFor.card_eq {Item : Type u} {predicate : Item → Prop}
    (first second : ListingFor predicate) : first.card = second.card :=
  Nat.le_antisymm (first.card_le_of_injection second id (fun _ _ same => same))
    (second.card_le_of_injection first id (fun _ _ same => same))

theorem ListingFor.card_eq_of_iff {Item : Type u} {firstPredicate secondPredicate : Item → Prop}
    (first : ListingFor firstPredicate) (second : ListingFor secondPredicate)
    (equivalent : ∀ item, firstPredicate item ↔ secondPredicate item) : first.card = second.card := by
  apply Nat.le_antisymm
  · exact first.card_le_of_injection second (fun item => ⟨item.val, (equivalent item.val).mp item.property⟩)
      (fun _ _ same => Subtype.ext (congrArg (fun item : {item // secondPredicate item} => item.val) same))
  · exact second.card_le_of_injection first (fun item => ⟨item.val, (equivalent item.val).mpr item.property⟩)
      (fun _ _ same => Subtype.ext (congrArg (fun item : {item // firstPredicate item} => item.val) same))

theorem ListingFor.card_eq_of_bijection {Domain : Type u} {Codomain : Type v}
    {sourcePredicate : Domain → Prop} {targetPredicate : Codomain → Prop}
    (source : ListingFor sourcePredicate) (target : ListingFor targetPredicate)
    (mapping : {item // sourcePredicate item} → {item // targetPredicate item})
    (injective : ∀ first second, mapping first = mapping second → first = second)
    (surjective : ∀ item, ∃ preimage, mapping preimage = item) :
    source.card = target.card := by
  classical
  apply Nat.le_antisymm (source.card_le_of_injection target mapping injective)
  let reverse := fun item => Classical.choose (surjective item)
  have reverseSpec : ∀ item, mapping (reverse item) = item :=
    fun item => Classical.choose_spec (surjective item)
  apply target.card_le_of_injection source reverse
  intro first second same
  have mapped := congrArg mapping same
  simpa only [reverseSpec] using mapped

noncomputable def ListingFor.restrict {Item : Type u} {base : Item → Prop}
    (listing : ListingFor base) (predicate : Item → Prop) :
    ListingFor (fun item => base item ∧ predicate item) := by
  classical
  exact ⟨listing.values.filter (fun item => decide (predicate item)),
    listing.distinct.filter _, by
      intro item
      simp only [List.mem_filter, listing.membership, decide_eq_true_eq]⟩

theorem filter_length_split {Item : Type u} (values : List Item)
    (first joint : Item → Prop) [DecidablePred first] [DecidablePred joint]
    (included : ∀ item ∈ values, joint item → first item) :
    (values.filter (fun item => decide (first item))).length =
      (values.filter (fun item => decide (first item ∧ ¬ joint item))).length +
      (values.filter (fun item => decide (joint item))).length := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
    have tailIncluded : ∀ item ∈ tail, joint item → first item :=
      fun item present => included item (by simp [present])
    have tailEquality := inductionHypothesis tailIncluded
    have headIncluded := included head (by simp)
    by_cases firstHead : first head <;> by_cases jointHead : joint head <;>
      simp_all [List.filter_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem ListingFor.restrict_card_split {Item : Type u} {base : Item → Prop}
    (listing : ListingFor base) (first joint : Item → Prop)
    (included : ∀ item, base item → joint item → first item) :
    (listing.restrict first).card =
      (listing.restrict (fun item => first item ∧ ¬ joint item)).card +
      (listing.restrict joint).card := by
  classical
  simpa [ListingFor.restrict, ListingFor.card] using filter_length_split listing.values first joint
    (fun item present => included item ((listing.membership item).mp present))

theorem ListingFor.restrict_card_complement {Item : Type u} {base : Item → Prop}
    (listing : ListingFor base) (predicate : Item → Prop) :
    (listing.restrict (fun item => ¬ predicate item)).card +
      (listing.restrict predicate).card = listing.card := by
  classical
  have split := filter_length_split listing.values (fun _ => True) predicate (by simp)
  have allValues : listing.values.filter (fun _ => true) = listing.values :=
    List.filter_eq_self.mpr (by simp)
  simpa [ListingFor.restrict, ListingFor.card, allValues] using split.symm

theorem ListingFor.card_le_add_of_injection
    {Domain : Type u} {Left : Type v} {Right : Type w}
    {sourcePredicate : Domain → Prop} {leftPredicate : Left → Prop} {rightPredicate : Right → Prop}
    (source : ListingFor sourcePredicate) (left : ListingFor leftPredicate)
    (right : ListingFor rightPredicate)
    (mapping : {item // sourcePredicate item} →
      Sum {item // leftPredicate item} {item // rightPredicate item})
    (injective : ∀ first second, mapping first = mapping second → first = second) :
    source.card ≤ left.card + right.card := by
  let target := left.attached.map (Sum.inl : _ → Sum _ {item // rightPredicate item}) ++
    right.attached.map (Sum.inr : _ → Sum {item // leftPredicate item} _)
  have bound := nodup_length_le_of_subset (source.attached.map mapping) target
    (nodup_map_injective mapping injective source.attached source.attached_nodup) (by
      intro item _
      cases item with
      | inl item => exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨item, left.attached_complete item, rfl⟩))
      | inr item => exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨item, right.attached_complete item, rfl⟩)))
  simpa only [target, List.length_append, List.length_map, ListingFor.attached_length] using bound

def ListingFor.product {Left : Type u} {Right : Type v}
    {leftPredicate : Left → Prop} {rightPredicate : Right → Prop}
    (left : ListingFor leftPredicate) (right : ListingFor rightPredicate) :
    ListingFor (fun pair : Left × Right => leftPredicate pair.1 ∧ rightPredicate pair.2) where
  values := left.values.flatMap (fun first => right.values.map (fun second => (first, second)))
  distinct := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro first _
      exact nodup_map_injective (fun second => (first, second))
        (fun _ _ same => congrArg Prod.snd same) right.values right.distinct
    · apply left.distinct.imp
      intro first second different firstPair inFirst secondPair inSecond samePair
      obtain ⟨firstRight, _, rfl⟩ := List.mem_map.mp inFirst
      obtain ⟨secondRight, _, rfl⟩ := List.mem_map.mp inSecond
      exact different (congrArg Prod.fst samePair)
  membership := by
    intro pair
    simp only [List.mem_flatMap, List.mem_map, left.membership, right.membership]
    constructor
    · rintro ⟨first, inLeft, second, inRight, same⟩
      cases same
      exact ⟨inLeft, inRight⟩
    · intro present
      exact ⟨pair.1, present.1, pair.2, present.2, rfl⟩

theorem ListingFor.product_card {Left : Type u} {Right : Type v}
    {leftPredicate : Left → Prop} {rightPredicate : Right → Prop}
    (left : ListingFor leftPredicate) (right : ListingFor rightPredicate) :
    (left.product right).card = left.card * right.card := by
  change (left.values.flatMap (fun first => right.values.map (fun second => (first, second)))).length =
    left.values.length * right.values.length
  induction left.values with
  | nil => simp
  | cons head tail inductionHypothesis =>
    simp [List.flatMap_cons, inductionHypothesis, Nat.succ_mul, Nat.add_comm]

def rangeListing (bound : Nat) : ListingFor (fun index : Nat => index < bound) :=
  ⟨List.range bound, List.nodup_range, fun _ => List.mem_range⟩

theorem rangeListing_card (bound : Nat) : (rangeListing bound).card = bound :=
  List.length_range

end Digraph
