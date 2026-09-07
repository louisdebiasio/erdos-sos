import Digraph

namespace Digraph.Tests

def fromLists (vertices : List Nat) (arcs : List (Nat × Nat))
    (vn : vertices.Nodup) (an : arcs.Nodup)
    (endpoints : ∀ e ∈ arcs, e.1 ∈ vertices ∧ e.2 ∈ vertices)
    (loops : ∀ e ∈ arcs, e.1 ≠ e.2) : FiniteDigraph Nat where
  vertices := vertices
  arcs := arcs
  vertices_nodup := vn
  arcs_nodup := an
  endpoints := fun a b h => endpoints (a, b) h
  loopless := fun a h => loops (a, a) h rfl

def leftEdge := fromLists [0, 1] [(0, 1)] (by decide) (by decide)
  (by simp) (by simp)
def rightEdge := fromLists [0, 2] [(0, 2)] (by decide) (by decide)
  (by simp) (by simp)
def outStar := fromLists [0, 1, 2] [(0, 1), (0, 2)] (by decide) (by decide)
  (by simp) (by simp)
def thirdEdge := fromLists [0, 3] [(0, 3)] (by decide) (by decide)
  (by simp) (by simp)
def branchingStar := fromLists [0, 1, 2, 3] [(0, 1), (0, 2), (0, 3)] (by decide) (by decide)
  (by simp) (by simp)
def directedPath := fromLists [0, 1, 2] [(0, 1), (1, 2)] (by decide) (by decide)
  (by simp) (by simp)
def mutualPair := fromLists [0, 1] [(0, 1), (1, 0)] (by decide) (by decide)
  (by simp) (by simp)
def completeThree := fromLists [0, 1, 2]
  [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] (by decide) (by decide)
  (by simp) (by simp)
def emptyHost := fromLists [] [] (by decide) (by decide) (by simp) (by simp)

theorem leftSingle : SingleArc leftEdge 0 1 .plus := by
  constructor
  · decide
  · intro a; simp [leftEdge, fromLists]
  · intro a b; simp [FiniteDigraph.Arc, leftEdge, fromLists]

theorem rightSingle : SingleArc rightEdge 0 2 .plus := by
  constructor
  · decide
  · intro a; simp [rightEdge, fromLists]
  · intro a b; simp [FiniteDigraph.Arc, rightEdge, fromLists]

theorem starAmalgam : RootAmalgam leftEdge rightEdge outStar 0 := by
  constructor
  · decide
  · decide
  · intro a; simp [leftEdge, rightEdge, outStar, fromLists]; omega
  · intro a; simp [leftEdge, rightEdge, fromLists]; omega
  · intro a b; simp [FiniteDigraph.Arc, leftEdge, rightEdge, outStar, fromLists]

theorem starRooted : RootedTree outStar 0 .plus 1 :=
  RootedTree.branch leftEdge rightEdge outStar 0 .plus 0 0
    (.edge leftEdge 0 1 .plus leftSingle) (.edge rightEdge 0 2 .plus rightSingle) starAmalgam

theorem starLeaf : LeafExtension leftEdge outStar 0 2 .minus := by
  constructor
  · decide
  · decide
  · intro a; simp [leftEdge, outStar, fromLists, or_assoc]
  · intro a b; simp [FiniteDigraph.Arc, leftEdge, outStar, fromLists]

theorem starSinkRooted : RootedTree outStar 2 .minus 1 :=
  .leaf leftEdge outStar 0 2 .minus 0 (.edge leftEdge 0 1 .plus leftSingle) starLeaf

theorem branchingRooted : RootedTree branchingStar 0 .plus 2 := by
  have one : SingleArc thirdEdge 0 3 .plus := by
    constructor
    · decide
    · intro a; simp [thirdEdge, fromLists]
    · intro a b; simp [FiniteDigraph.Arc, thirdEdge, fromLists]
  have am : RootAmalgam outStar thirdEdge branchingStar 0 := by
    constructor
    · decide
    · decide
    · intro a; simp [outStar, thirdEdge, branchingStar, fromLists]; omega
    · intro a; simp [outStar, thirdEdge, fromLists]; omega
    · intro a b; simp [FiniteDigraph.Arc, outStar, thirdEdge, branchingStar, fromLists, or_assoc]
  exact .branch outStar thirdEdge branchingStar 0 .plus 1 0 starRooted
    (.edge thirdEdge 0 3 .plus one) am

example (D : FiniteDigraph Nat) (free : ¬ Nonempty (Embedding branchingStar D)) :
    D.arcs.length ≤ 2 * D.vertices.length := by
  simpa [branchingStar, fromLists] using antidirected_density branchingRooted D free

example : IsAntidirectedTree outStar := ⟨0, .plus, 1, starRooted⟩
example : Antidirected outStar := starRooted.antidirected
example : outStar.vertices.length = 3 := starRooted.vertex_count

example (D : FiniteDigraph Nat) (free : ¬ Nonempty (Embedding outStar D)) :
    D.arcs.length ≤ D.vertices.length := by
  simpa [outStar, fromLists] using antidirected_density starRooted D free

example : Nonempty (Embedding outStar completeThree) :=
  antidirected_contains_tree starRooted completeThree (by decide)

example : M mutualPair .plus = 2 := by
  rw [population_normalization]; rfl
example : M mutualPair .minus = 2 := by
  rw [population_normalization]; rfl
example : Q mutualPair = 2 := by rw [order_normalization]; rfl
example : M emptyHost .plus = 0 := by rw [population_normalization]; rfl
example : Q emptyHost = 1 := by rw [order_normalization]; rfl

example (D : FiniteDigraph Nat) : R leftEdge D 0 .plus ≤ R outStar D 2 .minus + Q D :=
  signed_leaf_count leftEdge outStar D 0 2 .minus starLeaf

example (D : FiniteDigraph Nat) : R leftEdge D 0 .plus + R rightEdge D 0 .plus ≤
    M D .plus + Q D + R outStar D 0 .plus :=
  signed_branch_count leftEdge rightEdge outStar D 0 .plus starAmalgam

/-- A mixed vertex cannot acquire an antidirected-tree certificate. -/
theorem path_not_antidirected : ¬ Antidirected directedPath := by
  rintro ⟨c, h⟩
  have first := (h 0 1 (by simp [FiniteDigraph.Arc, directedPath, fromLists])).2
  have second := (h 1 2 (by simp [FiniteDigraph.Arc, directedPath, fromLists])).1
  have impossible : Sign.plus = Sign.minus := second.symm.trans first
  cases impossible

example : ¬ IsAntidirectedTree directedPath :=
  fun h => path_not_antidirected (isAntidirectedTree_antidirected directedPath h)

end Digraph.Tests

namespace Digraph.Tests

theorem walk_preserves {E : Nat → Nat → Prop} {a b : Nat} (h : Reach E a b)
    (P : Nat → Prop) (start : P a) (closed : ∀ x y, P x → E x y → P y) : P b := by
  induction h with
  | refl => exact start
  | tail _ edge ih => exact closed _ _ ih edge

theorem star_acyclic (G : FiniteDigraph Nat) (r : Nat)
    (shape : ∀ a b, G.UAdj a b → a = r ∨ b = r) : UnderlyingAcyclic G := by
  intro a b edge path
  have ne := uadj_ne G edge
  rcases shape a b edge with ar | br
  · subst a
    have inv : ∀ x y, x ≠ b → WithoutEdge G r b x y → y ≠ b := by
      intro x y _ h eq
      rcases shape x y h.1 with xr | yr
      · exact h.2 (Or.inl ⟨xr,eq⟩)
      · exact ne (yr.symm.trans eq)
    exact (walk_preserves path (fun x => x ≠ b) ne inv) rfl
  · subst b
    have inv : ∀ x y, x = a → WithoutEdge G a r x y → y = a := by
      intro x y xa h
      rcases shape x y h.1 with xr | yr
      · exact False.elim (ne (xa.symm.trans xr))
      · exact False.elim (h.2 (Or.inl ⟨xa,yr⟩))
    exact ne (walk_preserves path (fun x => x = a) rfl inv).symm

theorem consecutive_acyclic (G : FiniteDigraph Nat)
    (shape : ∀ a b, G.UAdj a b → a+1=b ∨ b+1=a) : UnderlyingAcyclic G := by
  intro a b edge path
  rcases shape a b edge with ab | ba
  · have inv : ∀ x y, x ≤ a → WithoutEdge G a b x y → y ≤ a := by
      intro x y hx h
      have step := shape x y h.1
      by_cases hy : y ≤ a
      · exact hy
      · have xa : x = a := by omega
        have yb : y = b := by omega
        exact False.elim (h.2 (Or.inl ⟨xa,yb⟩))
    have result := walk_preserves path (fun x => x ≤ a) (Nat.le_refl _) inv
    omega
  · have inv : ∀ x y, b < x → WithoutEdge G a b x y → b < y := by
      intro x y hx h
      have step := shape x y h.1
      by_cases hy : b < y
      · exact hy
      · have xa : x = a := by omega
        have yb : y = b := by omega
        exact False.elim (h.2 (Or.inl ⟨xa,yb⟩))
    have result := walk_preserves path (fun x => b < x) (by omega) inv
    omega

def starColor (x : Nat) : Sign := if x = 0 then .plus else .minus

theorem outStarColor : ∀ a b, outStar.Arc a b → starColor a = .plus ∧ starColor b = .minus := by
  intro a b h
  simp only [FiniteDigraph.Arc, outStar, fromLists, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

/-- This certificate uses only the literal graph, walks, and cycle exclusion. -/
theorem outStarConventional : ConventionalTree outStar := by
  refine ⟨by decide, ⟨starColor,outStarColor⟩, ?_, ?_⟩
  · have paths : ∀ x, x ∈ outStar.vertices → Reach outStar.UAdj 0 x := by
      intro x hx
      simp [outStar,fromLists] at hx
      rcases hx with rfl | rfl | rfl
      · exact .refl _
      · exact .tail (.refl _) (by decide)
      · exact .tail (.refl _) (by decide)
    intro a ha b hb
    exact ((paths a ha).symm (fun _ _ h => uadj_symm _ h)).trans (paths b hb)
  · apply star_acyclic outStar 0
    intro a b h
    simp [FiniteDigraph.UAdj, FiniteDigraph.Arc, outStar, fromLists] at h
    omega

def alternatingPath := fromLists [0,1,2,3] [(0,1),(2,1),(2,3)] (by decide) (by decide)
  (by simp) (by simp)
def pathColor (x : Nat) : Sign := if x % 2 = 0 then .plus else .minus

theorem alternatingColor : ∀ a b, alternatingPath.Arc a b → pathColor a = .plus ∧ pathColor b = .minus := by
  intro a b h
  simp only [FiniteDigraph.Arc, alternatingPath, fromLists, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

theorem alternatingConventional : ConventionalTree alternatingPath := by
  refine ⟨by decide,⟨pathColor,alternatingColor⟩,?_,?_⟩
  · have e01 : alternatingPath.UAdj 0 1 := by decide
    have e12 : alternatingPath.UAdj 1 2 := by decide
    have e23 : alternatingPath.UAdj 2 3 := by decide
    have paths : ∀ x, x ∈ alternatingPath.vertices → Reach alternatingPath.UAdj 0 x := by
      intro x hx
      simp [alternatingPath,fromLists] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact .refl _
      · exact .tail (.refl _) e01
      · exact .tail (.tail (.refl _) e01) e12
      · exact .tail (.tail (.tail (.refl _) e01) e12) e23
    intro a ha b hb
    exact ((paths a ha).symm (fun _ _ h => uadj_symm _ h)).trans (paths b hb)
  · apply consecutive_acyclic
    intro a b h
    simp [FiniteDigraph.UAdj, FiniteDigraph.Arc, alternatingPath, fromLists] at h
    omega

theorem conventionalInternalSink : ∃ k, RootedTree alternatingPath 1 .minus k := by
  simpa [pathColor] using conventional_rooted alternatingPath pathColor alternatingColor
    alternatingConventional.connected alternatingConventional.acyclic (by decide) 1 (by decide)

theorem conventionalLeafSource : ∃ k, RootedTree alternatingPath 0 .plus k := by
  simpa [pathColor] using conventional_rooted alternatingPath pathColor alternatingColor
    alternatingConventional.connected alternatingConventional.acyclic (by decide) 0 (by decide)

theorem conventionalBound (D : FiniteDigraph Nat) (free : ¬ Nonempty (Embedding alternatingPath D)) :
    D.arcs.length ≤ 2 * D.vertices.length := by
  simpa [alternatingPath,fromLists] using
    addarioBerry_bound_of_no_simple_cycle alternatingPath D (by decide)
      alternatingConventional.antidirected alternatingConventional.connected
      ((acyclic_iff_no_simple_cycle _).mp alternatingConventional.acyclic) free

theorem conventionalDenseCopy : Nonempty (Embedding outStar completeThree) :=
  addarioBerry_contains_of_connected_acyclic outStar completeThree outStarConventional (by decide)

example : emptyHost.arcs.length ≤ (alternatingPath.vertices.length - 2) * emptyHost.vertices.length := by
  exact addarioBerry_bound_of_connected_acyclic alternatingPath emptyHost alternatingConventional (by
    rintro ⟨f⟩
    have bad := f.maps_vertices 0 (by decide)
    simp [emptyHost,fromLists] at bad)

def alternatingSquare := fromLists [0,1,2,3] [(0,1),(2,1),(2,3),(0,3)] (by decide) (by decide)
  (by simp) (by simp)

theorem squareHasCycle : HasSimpleCycle alternatingSquare := by
  have path : SimplePath alternatingSquare.UAdj 0 3 [0,1,2,3] :=
    .tail (.tail (.tail (.refl 0) (by decide) (by decide)) (by decide) (by decide)) (by decide) (by decide)
  exact ⟨0,3,[0,1,2,3],path,by decide,by decide⟩

theorem squareNotConventional : ¬ ConventionalTree alternatingSquare :=
  fun h => (acyclic_iff_no_simple_cycle _).mp h.acyclic squareHasCycle

def disconnectedPair := fromLists [0,1,2,3] [(0,1),(2,3)] (by decide) (by decide)
  (by simp) (by simp)

theorem disconnectedNotConnected : ¬ UnderlyingConnected disconnectedPair := by
  intro conn
  have path := conn 0 (by decide) 3 (by decide)
  have result := walk_preserves path (fun x => x ≤ 1) (by decide) (by
    intro x y hx edge
    simp [FiniteDigraph.UAdj, FiniteDigraph.Arc, disconnectedPair, fromLists] at edge
    omega)
  omega

end Digraph.Tests
