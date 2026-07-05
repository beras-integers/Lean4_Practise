
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Set.Operations


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  ring

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  rw [h', h]
  ring

example (a b c : ℝ) : Real.exp (a + b + c) = Real.exp a * Real.exp b * Real.exp c := by
  rw [Real.exp_add, Real.exp_add]

variable {α : Type*}
variable (s t u a b : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example : s ∩ t ⊆ s := by
  intro x hx
  exact hx.1

example : s ∩ t ⊆ s := by
  rw [Set.subset_def, Set.inter_def]
  intro x hx
  simp only [Set.mem_setOf] at hx
  exact hx.1

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · constructor
    · exact xs
    · intro xt
      exact xntu (Or.inl xt)
  · intro xu
    exact xntu (Or.inr xu)

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  exact ⟨⟨xs, fun xt => xntu (Or.inl xt)⟩, fun xu => xntu (Or.inr xu)⟩

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  refine ⟨⟨xs, fun xt => xntu (Or.inl xt)⟩, fun xu => xntu (Or.inr xu)⟩
