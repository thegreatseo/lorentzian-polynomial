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

@[expose] public section

-- open scoped Classical
noncomputable section

namespace MvPolynomial

variable {σ R : Type*}

def iterPDeriv [CommSemiring R] (l : List σ) (p : MvPolynomial σ R) :=
  l.foldr (fun i q ↦ pderiv i q) p

def CoeffNonneg [CommSemiring R] [PartialOrder R] (p : MvPolynomial σ R) : Prop :=
  ∀ m, 0 ≤ coeff m p

def hessianAtZero [CommSemiring R] (p : MvPolynomial σ R) : Matrix σ σ R :=
  fun i j ↦ constantCoeff (pderiv i (pderiv j p))


variable [Fintype σ] [DecidableEq σ]

def HasAtMostOnePositiveEigenvalue
    (A : Matrix σ σ ℝ) : Prop :=
  sigPos A.toQuadraticForm' ≤ 1

def IsLorentzian
    (p : MvPolynomial σ ℝ) (d : ℕ) : Prop :=
  p.IsHomogeneous d ∧
  CoeffNonneg p ∧
  Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
  ∀ l : List σ, l.length = d - 2 →
    HasAtMostOnePositiveEigenvalue
      (hessianAtZero (iterPDeriv l p))

def IsLorentzianRec :
    MvPolynomial σ ℝ → ℕ → Prop
  | p, 0 =>
      p.IsHomogeneous 0 ∧ CoeffNonneg p
  | p, 1 =>
      p.IsHomogeneous 1 ∧ CoeffNonneg p
  | p, 2 =>
      p.IsHomogeneous 2 ∧ CoeffNonneg p ∧ Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
        sigPos (hessianAtZero p).toQuadraticForm' ≤ 1
  | p, d + 3 =>
      p.IsHomogeneous (d + 3) ∧ CoeffNonneg p ∧ Set.MConvex (p.support : Set (σ →₀ ℕ)) ∧
        ∀ i, IsLorentzianRec (pderiv i p) (d + 2)

omit [Fintype σ] [DecidableEq σ] in
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

omit [Fintype σ] [DecidableEq σ] in
/-- Partial differentiation preserves coefficientwise nonnegativity. -/
private lemma CoeffNonneg.pderiv {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (i : σ) :
    CoeffNonneg (pderiv i p) := by
  intro m
  rw [coeff_pderiv]
  apply mul_nonneg (hp _)
  positivity

omit [Fintype σ] [DecidableEq σ] in
/-- The support of a partial derivative of a polynomial with M-convex support is M-convex. -/
private lemma Set.MConvex.pderiv_support {p : MvPolynomial σ ℝ}
    (hp : Set.MConvex (p.support : Set (σ →₀ ℕ))) (i : σ) :
    Set.MConvex ((pderiv i p).support : Set (σ →₀ ℕ)) := by
  intro x hx y hy k hk
  let e : σ →₀ ℕ := Finsupp.single i 1
  have hx' : x + e ∈ p.support :=
    (mem_support_pderiv_iff p i x).mp hx
  have hy' : y + e ∈ p.support :=
    (mem_support_pderiv_iff p i y).mp hy
  have hk' : y k + e k < x k + e k := Nat.add_lt_add_right hk _
  obtain ⟨j, hj, hxj, hyj⟩ := hp hx' hy' k (by
    simpa only [Finsupp.add_apply] using hk')
  have hj' : x j < y j := by
    have hj' : x j + e j < y j + e j := by
      simpa only [Finsupp.add_apply] using hj
    exact Nat.lt_of_add_lt_add_right hj'
  refine ⟨j, hj', (mem_support_pderiv_iff p i _).mpr ?_,
    (mem_support_pderiv_iff p i _).mpr ?_⟩
  · have hk0 : x k ≠ 0 := by omega
    rw [add_assoc, add_comm (Finsupp.single j 1), ← add_assoc]
    rw [Finsupp.sub_single_one_add hk0]
    simpa [e] using hxj
  · have hj0 : y j ≠ 0 := by omega
    rw [add_assoc, add_comm (Finsupp.single k 1), ← add_assoc]
    rw [Finsupp.sub_single_one_add hj0]
    simpa [e] using hyj

omit [Fintype σ] in
/-- The support of a homogeneous polynomial of degree at most one is M-convex. -/
private lemma mConvex_support_of_isHomogeneous_of_le_one {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : d ≤ 1) :
    Set.MConvex (p.support : Set (σ →₀ ℕ)) := by
  intro x hx y hy i hi
  have hxdeg : x.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hx)
  have hydeg : y.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hy)
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

omit [Fintype σ] [DecidableEq σ] in
/-- The Hessian at zero of a homogeneous polynomial of degree at most one vanishes. -/
private lemma hessianAtZero_eq_zero_of_isHomogeneous_of_le_one
    {p : MvPolynomial σ ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (hd : d ≤ 1) :
    hessianAtZero p = 0 := by
  ext i j
  have hp' : (pderiv j p).IsHomogeneous 0 := by
    convert hp.pderiv (i := j) using 1
    omega
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp'
  change constantCoeff (pderiv i (pderiv j p)) = (0 : ℝ)
  rw [hp', pderiv_C, map_zero]

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
    (hp : p.IsHomogeneous d) (hnonneg : CoeffNonneg p) (hd : d ≤ 1) :
    p.IsLorentzian d := by
  refine ⟨hp, hnonneg, mConvex_support_of_isHomogeneous_of_le_one hp hd, ?_⟩
  intro l hl
  have hlen : l.length = 0 := by omega
  have : l = [] := by simpa using hlen
  subst l
  rw [show hessianAtZero (iterPDeriv [] p) = 0 by
    simpa [iterPDeriv] using hessianAtZero_eq_zero_of_isHomogeneous_of_le_one hp hd]
  exact hasAtMostOnePositiveEigenvalue_zero

omit [Fintype σ] [DecidableEq σ] in
/-- Appending one index to an iterated partial derivative differentiates the polynomial first
in that index. -/
private lemma iterPDeriv_append_singleton (l : List σ) (i : σ) (p : MvPolynomial σ ℝ) :
    iterPDeriv (l ++ [i]) p = iterPDeriv l (pderiv i p) := by
  simp [iterPDeriv]

/-- The definition of a Lorentzian polynomial using all iterated partial derivatives is
equivalent to the recursive definition using one partial derivative at a time. -/
theorem isLorentzian_iff_isLorentzianRec (p : MvPolynomial σ ℝ) (d : ℕ) :
    p.IsLorentzian d ↔ p.IsLorentzianRec d := by
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
    match d with
    | 0 | 1 =>
        constructor
        · exact fun h ↦ ⟨h.1, h.2.1⟩
        · rintro ⟨hp, hnonneg⟩
          exact isLorentzian_of_isHomogeneous_of_le_one hp hnonneg (by omega)
    | 2 =>
        simp [IsLorentzian, IsLorentzianRec, HasAtMostOnePositiveEigenvalue, iterPDeriv]
    | n + 3 =>
        constructor
        · rintro ⟨hp, hnonneg, hmconvex, hsignature⟩
          refine ⟨hp, hnonneg, hmconvex, fun i ↦ (ih (n + 2) (by omega) _).mp ?_⟩
          refine ⟨?_, hnonneg.pderiv i, Set.MConvex.pderiv_support hmconvex i, ?_⟩
          · convert hp.pderiv (i := i) using 1
            omega
          · intro l hl
            rw [← iterPDeriv_append_singleton]
            exact hsignature (l ++ [i]) (by simp [hl])
        · rintro ⟨hp, hnonneg, hmconvex, hrec⟩
          refine ⟨hp, hnonneg, hmconvex, ?_⟩
          intro l hl
          have hlne : l ≠ [] := by grind
          let i := l.getLast hlne
          have hdirect : IsLorentzian (pderiv i p) (n + 2) :=
            (ih (n + 2) (by omega) _).mpr (hrec i)
          have hdrop : l.dropLast.length = (n + 2) - 2 := by
            simp only [List.length_dropLast]
            omega
          have hsignature' := hdirect.2.2.2 l.dropLast hdrop
          rw [← List.dropLast_append_getLast hlne, iterPDeriv_append_singleton]
          exact hsignature'

end MvPolynomial
