/-
Copyright (c) 2026 Jaehyeon Seo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaehyeon Seo
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.Data.Real.Basic
public import LorentzianPolynomial.MConvex

/-!
# Lorentzian polynomials

This file defines Lorentzian polynomials and an equivalent recursive characterization based on
partial derivatives.

## Main declarations

* `MvPolynomial.CoeffNonneg`: coefficientwise nonnegativity.
* `MvPolynomial.IsLorentzian`: the definition using iterated partial derivatives.
* `MvPolynomial.IsLorentzianRec`: the recursive definition.
* `MvPolynomial.isLorentzian_iff_isLorentzianRec`: equivalence of the two definitions.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ R : Type*}

/-- Apply the partial derivatives indexed by `l`, from right to left. -/
def iterPDeriv [CommSemiring R] (l : List σ) (p : MvPolynomial σ R) :=
  l.foldr (fun i q ↦ pderiv i q) p

/-- A multivariate polynomial has nonnegative coefficients. -/
def CoeffNonneg [CommSemiring R] [PartialOrder R] (p : MvPolynomial σ R) : Prop :=
  ∀ m, 0 ≤ coeff m p

/-- The Hessian matrix of a multivariate polynomial evaluated at zero. -/
def hessianAtZero [CommSemiring R] (p : MvPolynomial σ R) : Matrix σ σ R :=
  fun i j ↦ constantCoeff (pderiv i (pderiv j p))

section Definitions

variable [Fintype σ] [DecidableEq σ]

/-- A real matrix has at most one positive eigenvalue, expressed through its quadratic form. -/
def HasAtMostOnePositiveEigenvalue (A : Matrix σ σ ℝ) : Prop :=
  sigPos A.toQuadraticForm' ≤ 1

/-- A homogeneous polynomial is Lorentzian when it has nonnegative coefficients, M-convex support,
and every iterated partial derivative of order `d - 2` has Hessian with at most one positive
eigenvalue. -/
def IsLorentzian (p : MvPolynomial σ ℝ) (d : ℕ) : Prop :=
  p.IsHomogeneous d ∧
  CoeffNonneg p ∧
  Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
  ∀ l : List σ, l.length = d - 2 →
    HasAtMostOnePositiveEigenvalue (hessianAtZero (iterPDeriv l p))

/-- The recursive characterization of Lorentzian polynomials by their first partial derivatives. -/
def IsLorentzianRec :
    MvPolynomial σ ℝ → ℕ → Prop
  | p, 0 =>
      p.IsHomogeneous 0 ∧ CoeffNonneg p
  | p, 1 =>
      p.IsHomogeneous 1 ∧ CoeffNonneg p
  | p, 2 =>
      p.IsHomogeneous 2 ∧ CoeffNonneg p ∧ Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
        HasAtMostOnePositiveEigenvalue (hessianAtZero p)
  | p, d + 3 =>
      p.IsHomogeneous (d + 3) ∧ CoeffNonneg p ∧ Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
        ∀ i, IsLorentzianRec (pderiv i p) (d + 2)

end Definitions

/-! ### Auxiliary lemmas -/

/-- A monomial occurs in a partial derivative exactly when its translate in the
differentiated direction occurs in the original polynomial. -/
private lemma mem_support_pderiv_iff (p : MvPolynomial σ ℝ) (i : σ) (m : σ →₀ ℕ) :
    m ∈ (pderiv i p).support ↔ m + Finsupp.single i 1 ∈ p.support := by
  rw [mem_support_iff, mem_support_iff, coeff_pderiv]
  constructor
  · intro h hc
    exact h (by simp [hc])
  · intro h
    exact mul_ne_zero h (by positivity)

/-- Partial differentiation preserves coefficientwise nonnegativity. -/
private lemma CoeffNonneg.pderiv {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (i : σ) :
    CoeffNonneg (pderiv i p) := by
  intro m
  rw [coeff_pderiv]
  apply mul_nonneg (hp _)
  positivity

/-- The support of a partial derivative of a polynomial with M-convex support is M-convex. -/
private lemma Set.MConvex.pderiv_support {p : MvPolynomial σ ℝ}
    (hp : Set.MConvex (p.support : Set (σ →₀ ℕ))) (i : σ) :
    Set.MConvex ((pderiv i p).support : Set (σ →₀ ℕ)) := by
  intro x hx y hy k hk
  let e : σ →₀ ℕ := Finsupp.single i 1
  have hxSupport : x + e ∈ p.support :=
    (mem_support_pderiv_iff p i x).mp hx
  have hySupport : y + e ∈ p.support :=
    (mem_support_pderiv_iff p i y).mp hy
  have hkSupport : y k + e k < x k + e k := Nat.add_lt_add_right hk _
  obtain ⟨j, hjSupport, hxExchange, hyExchange⟩ := hp hxSupport hySupport k (by
    simpa only [Finsupp.add_apply] using hkSupport)
  have hj : x j < y j := by
    have : x j + e j < y j + e j := by
      simpa only [Finsupp.add_apply] using hjSupport
    exact Nat.lt_of_add_lt_add_right this
  refine ⟨j, hj, (mem_support_pderiv_iff p i _).mpr ?_,
    (mem_support_pderiv_iff p i _).mpr ?_⟩
  · have hxk : x k ≠ 0 := by omega
    rw [add_assoc, add_comm (Finsupp.single j 1), ← add_assoc]
    rw [Finsupp.sub_single_one_add hxk]
    simpa [e] using hxExchange
  · have hyj : y j ≠ 0 := by omega
    rw [add_assoc, add_comm (Finsupp.single k 1), ← add_assoc]
    rw [Finsupp.sub_single_one_add hyj]
    simpa [e] using hyExchange

/-- The support of a homogeneous polynomial of degree at most one is M-convex. -/
private lemma mConvex_support_of_isHomogeneous_of_le_one {p : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : p.IsHomogeneous d) (hd : d ≤ 1) :
    Set.MConvex (p.support : Set (σ →₀ ℕ)) := by
  classical
  intro x hx y hy i hi
  have hxdeg : x.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hhom (mem_support_iff.mp hx)
  have hydeg : y.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hhom (mem_support_iff.mp hy)
  have hd1 : d = 1 := by
    have := Finsupp.le_degree i x
    omega
  have hxrange : x ∈ Set.range (fun i : σ ↦ Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hxdeg.trans hd1
  have hyrange : y ∈ Set.range (fun i : σ ↦ Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hydeg.trans hd1
  obtain ⟨a, rfl⟩ := hxrange
  obtain ⟨b, rfl⟩ := hyrange
  have hai : a = i := by
    by_contra hai
    simp [Finsupp.single_apply, hai] at hi
  have hbi : b ≠ i := by
    intro hbi
    simp [hbi, hai] at hi
  subst i
  refine ⟨b, ?_, ?_, ?_⟩
  · simp [hbi.symm]
  · simpa using hy
  · simpa using hx

/-- The Hessian at zero of a homogeneous polynomial of degree at most one vanishes. -/
private lemma hessianAtZero_eq_zero_of_isHomogeneous_of_le_one
    {p : MvPolynomial σ ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hd : d ≤ 1) :
    hessianAtZero p = 0 := by
  ext i j
  have hhom' : (pderiv j p).IsHomogeneous 0 := by
    convert hhom.pderiv (i := j) using 1
    omega
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hhom'
  change constantCoeff (pderiv i (pderiv j p)) = (0 : ℝ)
  rw [hhom', pderiv_C, map_zero]

/-- Appending one index to an iterated partial derivative differentiates the polynomial first
in that index. -/
private lemma iterPDeriv_append_singleton (l : List σ) (i : σ) (p : MvPolynomial σ ℝ) :
    iterPDeriv (l ++ [i]) p = iterPDeriv l (pderiv i p) := by
  simp [iterPDeriv]

/-! ### Recursive characterization -/

section RecursiveCharacterization

variable [Fintype σ] [DecidableEq σ]

/-- The zero matrix has at most one positive eigenvalue in the sense used here. -/
private lemma hasAtMostOnePositiveEigenvalue_zero :
    HasAtMostOnePositiveEigenvalue (0 : Matrix σ σ ℝ) := by
  unfold HasAtMostOnePositiveEigenvalue
  have hzero : Matrix.toQuadraticForm' (0 : Matrix σ σ ℝ) =
      QuadraticMap.weightedSumSquares ℝ (fun _ : σ ↦ (0 : ℝ)) := by
    ext x
    simp [Matrix.toQuadraticForm', QuadraticMap.weightedSumSquares_apply]
  rw [hzero, QuadraticForm.sigPos_weightedSumSquares]
  simp

/-- A homogeneous polynomial of degree at most one with nonnegative coefficients is Lorentzian. -/
private lemma isLorentzian_of_isHomogeneous_of_le_one {p : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : p.IsHomogeneous d) (hcoeff : CoeffNonneg p) (hd : d ≤ 1) :
    p.IsLorentzian d := by
  refine ⟨hhom, hcoeff, mConvex_support_of_isHomogeneous_of_le_one hhom hd, ?_⟩
  intro l hl
  have hlen : l.length = 0 := by omega
  have : l = [] := by simpa using hlen
  subst l
  rw [show hessianAtZero (iterPDeriv [] p) = 0 by
    simpa [iterPDeriv] using hessianAtZero_eq_zero_of_isHomogeneous_of_le_one hhom hd]
  exact hasAtMostOnePositiveEigenvalue_zero

/-- The definition of a Lorentzian polynomial using all iterated partial derivatives is
equivalent to the recursive definition using one partial derivative at a time. -/
theorem isLorentzian_iff_isLorentzianRec (p : MvPolynomial σ ℝ) (d : ℕ) :
    p.IsLorentzian d ↔ p.IsLorentzianRec d := by
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
    match d with
    | 0 | 1 =>
        constructor
        · rintro ⟨hhom, hcoeff, _, _⟩
          exact ⟨hhom, hcoeff⟩
        · rintro ⟨hhom, hcoeff⟩
          exact isLorentzian_of_isHomogeneous_of_le_one hhom hcoeff (by omega)
    | 2 =>
        simp [IsLorentzian, IsLorentzianRec, HasAtMostOnePositiveEigenvalue, iterPDeriv]
    | n + 3 =>
        constructor
        · rintro ⟨hhom, hcoeff, hconvex, hsignature⟩
          refine ⟨hhom, hcoeff, hconvex, fun i ↦ (ih (n + 2) (by omega) _).mp ?_⟩
          refine ⟨?_, hcoeff.pderiv i, Set.MConvex.pderiv_support hconvex i, ?_⟩
          · convert hhom.pderiv (i := i) using 1
            omega
          · intro l hl
            rw [← iterPDeriv_append_singleton]
            exact hsignature (l ++ [i]) (by simp [hl])
        · rintro ⟨hhom, hcoeff, hconvex, hrec⟩
          refine ⟨hhom, hcoeff, hconvex, ?_⟩
          intro l hl
          have hlne : l ≠ [] := by grind
          let i := l.getLast hlne
          obtain ⟨_, _, _, hsignature⟩ := (ih (n + 2) (by omega) _).mpr (hrec i)
          have hdrop : l.dropLast.length = (n + 2) - 2 := by
            simp only [List.length_dropLast]
            omega
          have hsignatureDrop := hsignature l.dropLast hdrop
          rw [← List.dropLast_append_getLast hlne, iterPDeriv_append_singleton]
          exact hsignatureDrop

end RecursiveCharacterization

end MvPolynomial
