import Kalai.FiniteCounting

namespace Kalai

universe u v

def sumOn {Item : Type u} (values : List Item) (weight : Item → Nat) : Nat :=
  (values.map weight).sum

theorem length_flatMap_constant {Base : Type u} {Value : Type v}
    (values : List Base) (fiber : Base → List Value) (size : Nat)
    (same : ∀ item ∈ values, (fiber item).length = size) :
    (values.flatMap fiber).length = values.length * size := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
    have headLength := same head (by simp)
    have tailLength := inductionHypothesis (fun item present => same item (by simp [present]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, headLength, tailLength,
      Nat.succ_mul, Nat.add_comm]

theorem sumOn_add {Item : Type u} (values : List Item) (first second : Item → Nat) :
    sumOn values (fun item => first item + second item) = sumOn values first + sumOn values second := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    simp only [sumOn, List.map_cons, List.sum_cons] at *
    omega

theorem sumOn_mono {Item : Type u} (values : List Item) (first second : Item → Nat)
    (bound : ∀ item ∈ values, first item ≤ second item) : sumOn values first ≤ sumOn values second := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons head tail inductionHypothesis =>
    have headBound := bound head (by simp)
    have tailBound := inductionHypothesis (fun item present => bound item (by simp [present]))
    simp only [sumOn, List.map_cons, List.sum_cons] at *
    omega

theorem sumOn_constant {Item : Type u} (values : List Item) (weight : Item → Nat) (constant : Nat)
    (same : ∀ item ∈ values, weight item = constant) : sumOn values weight = values.length * constant := by
  induction values with
  | nil => simp [sumOn]
  | cons head tail inductionHypothesis =>
    have headSame := same head (by simp)
    have tailSame := inductionHypothesis (fun item present => same item (by simp [present]))
    simp only [sumOn, List.map_cons, List.sum_cons] at *
    rw [headSame, tailSame, List.length_cons, Nat.succ_mul, Nat.add_comm]

def ListingFor.fiber {Base : Type u} {Value : Type v} {basePredicate : Base → Prop}
    {fiberPredicate : Base → Value → Prop} (base : ListingFor basePredicate)
    (fibers : ∀ item, ListingFor (fiberPredicate item)) :
    ListingFor (fun pair : Base × Value => basePredicate pair.1 ∧ fiberPredicate pair.1 pair.2) where
  values := base.values.flatMap (fun item => (fibers item).values.map (fun value => (item, value)))
  distinct := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro item _
      exact nodup_map_injective (fun value => (item, value))
        (fun _ _ same => congrArg Prod.snd same) (fibers item).values (fibers item).distinct
    · apply base.distinct.imp
      intro first second different firstPair inFirst secondPair inSecond same
      obtain ⟨firstValue, _, rfl⟩ := List.mem_map.mp inFirst
      obtain ⟨secondValue, _, rfl⟩ := List.mem_map.mp inSecond
      exact different (congrArg Prod.fst same)
  membership := by
    intro pair
    simp only [List.mem_flatMap, List.mem_map, base.membership]
    constructor
    · rintro ⟨item, present, value, inFiber, same⟩
      cases same
      exact ⟨present, ((fibers item).membership value).mp inFiber⟩
    · intro present
      exact ⟨pair.1, present.1, pair.2, ((fibers pair.1).membership pair.2).mpr present.2, rfl⟩

theorem ListingFor.fiber_card {Base : Type u} {Value : Type v} {basePredicate : Base → Prop}
    {fiberPredicate : Base → Value → Prop} (base : ListingFor basePredicate)
    (fibers : ∀ item, ListingFor (fiberPredicate item)) :
    (base.fiber fibers).card = sumOn base.values (fun item => (fibers item).card) := by
  change (base.values.flatMap (fun item => (fibers item).values.map (fun value => (item, value)))).length = _
  induction base.values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
    simp [List.flatMap_cons, sumOn, ListingFor.card] at *

end Kalai
