
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Manifold
open Filter
open scoped Topology
#check mem_closure_iff
#check closure_prod_eq

open Filter
variable {X : Type*} [TopologicalSpace X]
variable (A : Set X)
example : IsOpen (interior A) := by
  unfold interior
  apply isOpen_sUnion
  intro g hg
  apply hg.1

lemma setinsideclosure : A ⊆ closure A := by
  intro x hx
  unfold closure
  intro t ht
  apply ht.2
  exact hx

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by
    simp
  sets_of_superset := by
    rintro t1 t2 h1 h2
    exact Set.Subset.trans h1 h2
  inter_sets := by
    intro t1 t2 ht1 ht2 x hx
    exact ⟨ht1 hx, ht2 hx⟩

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ Tendsto f F G :=
  Iff.rfl



theorem isClosed_sInter' {α : Type*} [TopologicalSpace α]
  (S : Set (Set α))
  (hS : ∀ s ∈ S, IsClosed s) :
  IsClosed (⋂₀ S) := by
  rw [← isOpen_compl_iff]
  have : (⋂₀ S)ᶜ = ⋃₀ (Set.image compl S) := by
    ext x
    simp [Set.mem_sInter, Set.mem_image]
  rw [this]
  exact isOpen_sUnion (by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := hs
    exact (hS s' hs').isOpen_compl)

lemma closed_prod {X : Type*} [TopologicalSpace X]
    (A : Set X) (B : Set X)
    (hA : IsClosed A)
    (hB : IsClosed B) :
    IsClosed (A ×ˢ B) := by
    have hAB : IsClosed (A ×ˢ B) := by
      exact hA.prod hB
    exact hAB

theorem closure_smallest {X : Type*} [TopologicalSpace X]
    (A C : Set X)
    (hC : IsClosed C)
    (hAC : A ⊆ C) :
    closure A ⊆ C := by
    have h1 : closure A ⊆ C := by
      exact closure_minimal hAC hC
    exact h1


example (A B : Set X) : closure (A ×ˢ B) = closure A ×ˢ closure B := by
  have hclosed : IsClosed (closure A ×ˢ closure B) := by
    apply closed_prod
    · apply isClosed_closure
    · apply isClosed_closure
  have hsubset : A ×ˢ B ⊆ closure A ×ˢ closure B := by
    intro x hx
    exact ⟨subset_closure hx.1, subset_closure hx.2⟩
  have h₁ : closure (A ×ˢ B) ⊆ closure A ×ˢ closure B := by
    exact closure_smallest
      (A ×ˢ B)
      (closure A ×ˢ closure B)
      hclosed
      hsubset
  have h₂ : closure A ×ˢ closure B ⊆ closure (A ×ˢ B) := by
    simp [← closure_prod_eq]
  exact subset_antisymm h₁ h₂

example
    {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    {V : Set Y}
    (hf : Continuous f)
    (hV : IsOpen V) :
    IsOpen (f ⁻¹' V) := by
  have hpre : IsOpen (f ⁻¹' V) := by
    exact hf.isOpen_preimage V hV
  exact hpre



example
    {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {u : ℕ → X}
    {x : X}
    {f : X → Y}
    (hf : Continuous f)
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by

  have h1 : Tendsto f (𝓝 x) (𝓝 (f x)) := by
    exact hf.continuousAt.tendsto

  have h2 :
      Tendsto (fun n => f (u n))
        atTop
        (𝓝 (f x)) := by
    exact h1.comp hu

  exact h2

universe u
structure MyManifold (M : Type u) [TopologicalSpace M] (n : ℕ) where
  local_homeomorph :
    ∀ x : M,
      ∃ U : Set M,
        IsOpen U ∧
        x ∈ U ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧
          Nonempty (U ≃ₜ V)



noncomputable section


abbrev ModelSpace (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

variable
  (n : ℕ)
  (M : Type*)

variable
  [TopologicalSpace M]
  [ChartedSpace (ModelSpace n) M]

example (x : M) :
    x ∈ (chartAt (ModelSpace n) x).source := by
  exact mem_chart_source (H := ModelSpace n) x



noncomputable section

structure Point where
  x : ℝ
  y : ℝ

def HyperbolicPlane : Type :=
  { p : Point // p.x ^ 2 + p.y ^ 2 < 1 }

example (p : HyperbolicPlane) :
    p.1.x ^ 2 + p.1.y ^ 2 < 1 := by
  exact p.2

axiom hyperbolicDist :
  HyperbolicPlane → HyperbolicPlane → ℝ

/-- Distance from a point to itself is zero. -/
axiom hyperbolicDist_self
    (x : HyperbolicPlane) :
    hyperbolicDist x x = 0

/-- Distance is symmetric. -/
axiom hyperbolicDist_comm
    (x y : HyperbolicPlane) :
    hyperbolicDist x y =
    hyperbolicDist y x

/-- Triangle inequality. -/
axiom hyperbolicDist_triangle
    (x y z : HyperbolicPlane) :
    hyperbolicDist x z ≤
      hyperbolicDist x y +
      hyperbolicDist y z

/-- Distance is always nonnegative. -/
axiom hyperbolicDist_nonneg
    (x y : HyperbolicPlane) :
    0 ≤ hyperbolicDist x y

/-- Zero distance implies equality. -/
axiom hyperbolicDist_eq_zero
    {x y : HyperbolicPlane} :
    hyperbolicDist x y = 0 →
    x = y

instance : MetricSpace HyperbolicPlane where
  dist := hyperbolicDist
  dist_self := hyperbolicDist_self
  dist_comm := hyperbolicDist_comm
  dist_triangle := hyperbolicDist_triangle
  eq_of_dist_eq_zero := hyperbolicDist_eq_zero



def hyperbolicDisc (p : HyperbolicPlane) (r : ℝ) : Set HyperbolicPlane :=
  { q : HyperbolicPlane | hyperbolicDist p q < r }

axiom eq_of_hyperbolicDist_eq_zero :
  ∀ {p q : HyperbolicPlane},
    hyperbolicDist p q = 0 → p = q

instance : MetricSpace HyperbolicPlane where
  dist := hyperbolicDist
  dist_self := hyperbolicDist_self
  dist_comm := hyperbolicDist_comm
  dist_triangle := hyperbolicDist_triangle
  eq_of_dist_eq_zero := by
    intro p q h
    exact eq_of_hyperbolicDist_eq_zero h

set_option linter.style.whitespace false

structure RiemannianMetric
    (X : Type*)
    [TopologicalSpace X]
    (TangentSpace : X → Type*)
    [∀ p, AddCommGroup (TangentSpace p)]
    [∀ p, Module ℝ (TangentSpace p)] where

  g :
    ∀ p,
      TangentSpace p → TangentSpace p → ℝ

  add_left :
    ∀ p u v w,
      g p (u + v) w =
      g p u w + g p v w

  smul_left :
    ∀ p a u w,
      g p (a • u) w =
      a * g p u w

  add_right :
    ∀ p u v w,
      g p u (v + w) =
      g p u v + g p u w

  smul_right :
    ∀ p a u v,
      g p u (a • v) =
      a * g p u v

  symmetric :
    ∀ p u v,
      g p u v = g p v u

  positive :
    ∀ p v,
      v ≠ 0 →
      0 < g p v v
