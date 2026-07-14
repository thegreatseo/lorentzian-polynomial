/-
Copyright (c) 2026 Jaehyeon Seo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jaehyeon Seo
-/
module

public import LorentzianPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Closure properties of Lorentzian polynomials

This file proves that Lorentzian polynomials are preserved by elementary splitting: replacing one
variable by the sum of that variable and a fresh variable.

## Main result

* `MvPolynomial.IsLorentzian.elementary_splitting`
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ : Type*}

private def collapseIndex (i : σ) : Option σ → σ
  | none => i
  | some j => j

/-! ### Coefficientwise nonnegativity -/

private lemma CoeffNonneg.C {r : ℝ} (hr : 0 ≤ r) :
    CoeffNonneg (C r : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [coeff_C]
  split_ifs <;> positivity

private lemma CoeffNonneg.add {p q : MvPolynomial σ ℝ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p + q) := by
  intro m
  rw [coeff_add]
  exact add_nonneg (hp m) (hq m)

private lemma CoeffNonneg.mul {p q : MvPolynomial σ ℝ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p * q) := by
  classical
  intro m
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x.1) (hq x.2)

private lemma CoeffNonneg.pow {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (n : ℕ) :
    CoeffNonneg (p ^ n) := by
  induction n with
  | zero => simpa using CoeffNonneg.C (σ := σ) zero_le_one
  | succ n hn => simpa [pow_succ] using hn.mul hp

private lemma CoeffNonneg.sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (p i)) : CoeffNonneg (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.C (σ := σ) le_rfl
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hp i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

private lemma CoeffNonneg.prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (p i)) : CoeffNonneg (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.C (σ := σ) zero_le_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

/-! ### Basic properties of elementary splitting -/

section BasicProperties

variable [DecidableEq σ]

private def splitVariable (i j : σ) : MvPolynomial (Option σ) ℝ :=
  X (some j) + if j = i then X none else 0

private def elementarySplitting (i : σ) :
    MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial (Option σ) ℝ :=
  bind₁ (splitVariable i)

@[simp] private lemma elementarySplitting_X (i j : σ) :
    elementarySplitting i (X j) = splitVariable i j := by
  simp [elementarySplitting]

private lemma CoeffNonneg.elementarySplitting {f : MvPolynomial σ ℝ}
    (hf : CoeffNonneg f) (i : σ) : CoeffNonneg (elementarySplitting i f) := by
  rw [f.as_sum, map_sum]
  apply CoeffNonneg.sum
  intro m hm
  rw [MvPolynomial.elementarySplitting, bind₁_monomial]
  apply CoeffNonneg.mul (CoeffNonneg.C (hf m))
  apply CoeffNonneg.prod
  intro j _
  apply CoeffNonneg.pow
  intro m
  rw [splitVariable, coeff_add]
  split_ifs <;> simp only [coeff_X, coeff_zero, add_zero] <;> positivity

private lemma IsHomogeneous.elementarySplitting {f : MvPolynomial σ ℝ} {d : ℕ}
    (hf : f.IsHomogeneous d) (i : σ) : (elementarySplitting i f).IsHomogeneous d := by
  unfold MvPolynomial.elementarySplitting bind₁
  have h := hf.aeval
    (splitVariable i)
    (fun j ↦ by
      unfold splitVariable
      apply IsHomogeneous.add (isHomogeneous_X ℝ (some j))
      split_ifs
      · exact isHomogeneous_X ℝ none
      · exact isHomogeneous_zero (Option σ) ℝ 1)
  convert h using 1
  omega

private lemma pderiv_splitVariable (i : σ) (k : Option σ) (j : σ) :
    pderiv k (splitVariable i j) = if collapseIndex i k = j then 1 else 0 := by
  cases k with
  | none =>
      by_cases hji : j = i
      · subst j
        simp [splitVariable, collapseIndex]
      · simp [splitVariable, collapseIndex, hji, Ne.symm hji]
  | some k =>
      by_cases hji : j = i
      · subst j
        by_cases hik : i = k
        · subst k
          simp [splitVariable, collapseIndex]
        · simp [splitVariable, collapseIndex, hik, Ne.symm hik]
      · by_cases hjk : j = k
        · subst k
          simp [splitVariable, collapseIndex, hji]
        · simp [splitVariable, collapseIndex, hji, hjk, Ne.symm hjk]

private lemma pderiv_elementarySplitting (f : MvPolynomial σ ℝ) (i : σ) (k : Option σ) :
    pderiv k (elementarySplitting i f) =
      elementarySplitting i (pderiv (collapseIndex i k) f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [elementarySplitting]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, elementarySplitting_X, pderiv_mul, hp,
        pderiv_splitVariable, map_add]
      by_cases hkj : collapseIndex i k = j
      · subst j; simp
      · simp [hkj]

end BasicProperties

/-! ### M-convex support -/

private def collapseExponent (i : σ) (m : Option σ →₀ ℕ) : σ →₀ ℕ :=
  m.some + Finsupp.single i (m none)

@[simp] private lemma collapseExponent_add (i : σ) (x y : Option σ →₀ ℕ) :
    collapseExponent i (x + y) = collapseExponent i x + collapseExponent i y := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [collapseExponent]
    omega
  · simp [collapseExponent, hji]

@[simp] private lemma collapseExponent_single (i : σ) (k : Option σ) (n : ℕ) :
    collapseExponent i (Finsupp.single k n) = Finsupp.single (collapseIndex i k) n := by
  classical
  ext j
  cases k with
  | none => simp [collapseExponent, collapseIndex, Finsupp.single_apply]
  | some a =>
      by_cases hai : a = i
      · subst a; simp [collapseExponent, collapseIndex]
      · simp [collapseExponent, collapseIndex, Finsupp.single_apply]

private lemma collapseExponent_exchange (i : σ) (x : Option σ →₀ ℕ) (k l : Option σ)
    (hk : x k ≠ 0) :
    collapseExponent i (x - Finsupp.single k 1 + Finsupp.single l 1) =
      collapseExponent i x - Finsupp.single (collapseIndex i k) 1 +
        Finsupp.single (collapseIndex i l) 1 := by
  classical
  have hx := congrArg (collapseExponent i) (Finsupp.sub_add_single_one_cancel hk)
  rw [collapseExponent_add, collapseExponent_single] at hx
  have hsub : collapseExponent i (x - Finsupp.single k 1) =
      collapseExponent i x - Finsupp.single (collapseIndex i k) 1 := by
    ext j
    have hxj := congrArg (fun z : σ →₀ ℕ ↦ z j) hx
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hxj ⊢
    omega
  rw [collapseExponent_add, hsub, collapseExponent_single]

private lemma exists_lt_of_collapseExponent_lt (i : σ) (x y : Option σ →₀ ℕ) (j : σ)
    (h : collapseExponent i x j < collapseExponent i y j) :
    ∃ k, collapseIndex i k = j ∧ x k < y k := by
  classical
  by_cases hji : j = i
  · subst j
    by_cases hnone : x none < y none
    · exact ⟨none, rfl, hnone⟩
    · refine ⟨some i, rfl, ?_⟩
      simp [collapseExponent] at h
      omega
  · refine ⟨some j, rfl, ?_⟩
    simpa [collapseExponent, hji] using h

private lemma exists_lt_same_collapseIndex (i : σ) (x y : Option σ →₀ ℕ)
    (k : Option σ) (hk : y k < x k)
    (h : ¬collapseExponent i y (collapseIndex i k) <
      collapseExponent i x (collapseIndex i k)) :
    ∃ l, collapseIndex i l = collapseIndex i k ∧ x l < y l := by
  classical
  cases k with
  | none =>
      refine ⟨some i, rfl, ?_⟩
      simp [collapseExponent, collapseIndex] at h
      omega
  | some j =>
      by_cases hji : j = i
      · subst j
        refine ⟨none, rfl, ?_⟩
        simp [collapseExponent, collapseIndex] at h
        omega
      · exfalso
        apply h
        simpa [collapseExponent, collapseIndex, hji] using hk

private lemma collapseExponent_apply_ne_zero (i : σ) (x : Option σ →₀ ℕ)
    (k : Option σ) (hk : x k ≠ 0) : collapseExponent i x (collapseIndex i k) ≠ 0 := by
  classical
  cases k with
  | none =>
      simp [collapseExponent, collapseIndex] at hk ⊢
      omega
  | some j =>
      by_cases hji : j = i
      · subst j
        simp [collapseExponent, collapseIndex] at hk ⊢
        omega
      · simpa [collapseExponent, collapseIndex, hji] using hk

private lemma mem_support_pderiv_iff' (p : MvPolynomial σ ℝ) (i : σ) (m : σ →₀ ℕ) :
    m ∈ (pderiv i p).support ↔ m + Finsupp.single i 1 ∈ p.support := by
  rw [mem_support_iff, mem_support_iff, coeff_pderiv]
  constructor
  · intro h hc
    exact h (by simp [hc])
  · intro h
    exact mul_ne_zero h (by positivity)

section Support

variable [DecidableEq σ]

private lemma eval_zero_optionEquivLeft_elementarySplitting (f : MvPolynomial σ ℝ) (i : σ) :
    Polynomial.eval 0 (optionEquivLeft ℝ σ (elementarySplitting i f)) = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [elementarySplitting]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, elementarySplitting_X, map_mul, Polynomial.eval_mul, hp]
      by_cases hji : j = i <;> simp [splitVariable, hji]

private lemma mem_support_elementarySplitting_iff (f : MvPolynomial σ ℝ) (i : σ)
    (m : Option σ →₀ ℕ) :
    m ∈ (elementarySplitting i f).support ↔ collapseExponent i m ∈ f.support := by
  induction hmn : m none generalizing f m with
  | zero =>
      rw [mem_support_iff, mem_support_iff,
        ← optionEquivLeft_coeff_some_coeff_none ℝ σ m (elementarySplitting i f), hmn,
        Polynomial.coeff_zero_eq_eval_zero, eval_zero_optionEquivLeft_elementarySplitting]
      simp [collapseExponent, hmn]
  | succ n ih =>
      let m' := m - Finsupp.single none 1
      have hmnone : m none ≠ 0 := by omega
      have hm'none : m' none = n := by simp [m', hmn]
      have hmadd : m' + Finsupp.single none 1 = m :=
        Finsupp.sub_add_single_one_cancel hmnone
      have hcollapse : collapseExponent i m' + Finsupp.single i 1 =
          collapseExponent i m := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [collapseExponent, m', hmn]
          omega
        · simp [collapseExponent, m', hji]
      conv_lhs => rw [← hmadd]
      rw [← mem_support_pderiv_iff', pderiv_elementarySplitting,
        show collapseIndex i none = i by rfl,
        ih (pderiv i f) m' hm'none, mem_support_pderiv_iff', hcollapse]

private lemma Set.MConvex.elementarySplitting_support {f : MvPolynomial σ ℝ}
    (hf : Set.MConvex (f.support : Set (σ →₀ ℕ))) (i : σ) :
    Set.MConvex ((elementarySplitting i f).support : Set (Option σ →₀ ℕ)) := by
  intro x hx y hy k hk
  have hxCollapse : collapseExponent i x ∈ f.support :=
    (mem_support_elementarySplitting_iff f i x).mp hx
  have hyCollapse : collapseExponent i y ∈ f.support :=
    (mem_support_elementarySplitting_iff f i y).mp hy
  by_cases hkCollapse :
      collapseExponent i y (collapseIndex i k) < collapseExponent i x (collapseIndex i k)
  · obtain ⟨j, hj, hxj, hyj⟩ := hf hxCollapse hyCollapse (collapseIndex i k) hkCollapse
    obtain ⟨l, hlj, hl⟩ := exists_lt_of_collapseExponent_lt i x y j hj
    have hxk : x k ≠ 0 := by omega
    have hyl : y l ≠ 0 := by omega
    refine ⟨l, hl, (mem_support_elementarySplitting_iff f i _).mpr ?_,
      (mem_support_elementarySplitting_iff f i _).mpr ?_⟩
    · rw [collapseExponent_exchange i x k l hxk, hlj]
      exact hxj
    · rw [collapseExponent_exchange i y l k hyl, hlj]
      exact hyj
  · obtain ⟨l, hlCollapse, hl⟩ :=
      exists_lt_same_collapseIndex i x y k hk hkCollapse
    have hxk : x k ≠ 0 := by omega
    have hyl : y l ≠ 0 := by omega
    have hyCollapseNe : collapseExponent i y (collapseIndex i k) ≠ 0 := by
      rw [← hlCollapse]
      exact collapseExponent_apply_ne_zero i y l hyl
    refine ⟨l, hl, (mem_support_elementarySplitting_iff f i _).mpr ?_,
      (mem_support_elementarySplitting_iff f i _).mpr ?_⟩
    · rw [collapseExponent_exchange i x k l hxk, hlCollapse,
        Finsupp.sub_add_single_one_cancel
          (collapseExponent_apply_ne_zero i x k hxk)]
      exact hxCollapse
    · rw [collapseExponent_exchange i y l k hyl, hlCollapse,
        Finsupp.sub_add_single_one_cancel
          hyCollapseNe]
      exact hyCollapse

end Support

/-! ### Hessian signature -/

private lemma sigPos_comp_le [Finite σ] (Q : QuadraticForm ℝ (σ → ℝ))
    (L : (Option σ → ℝ) →ₗ[ℝ] (σ → ℝ)) :
    sigPos (Q.comp L) ≤ sigPos Q := by
  letI := Fintype.ofFinite σ
  obtain ⟨V, hVrank, hVpos⟩ :=
    exists_finrank_eq_sigPos_and_posDef (Q.comp L)
  let LOnV : V →ₗ[ℝ] (σ → ℝ) := L.comp V.subtype
  have hLOnVInjective : Function.Injective LOnV := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hpos := hVpos (x - y) hne
    change L (x : Option σ → ℝ) = L (y : Option σ → ℝ) at hxy
    simp [hxy] at hpos
  have hRangePos : (Q.restrict (LinearMap.range LOnV)).PosDef := by
    rintro ⟨_, ⟨v, rfl⟩⟩ hv
    have hv0 : v ≠ 0 := by
      intro hv0
      apply hv
      subst v
      simp
    simpa [LOnV] using hVpos v hv0
  calc
    sigPos (Q.comp L) = Module.finrank ℝ V := hVrank.symm
    _ = Module.finrank ℝ (LinearMap.range LOnV) :=
      (LinearMap.finrank_range_of_inj hLOnVInjective).symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q hRangePos

section HessianSignature

variable [DecidableEq σ]

private def splitLinearMap (i : σ) : (Option σ → ℝ) →ₗ[ℝ] (σ → ℝ) where
  toFun x j := x (some j) + if j = i then x none else 0
  map_add' x y := by
    ext j
    by_cases hji : j = i
    · simp [hji]
      ring
    · simp [hji]
  map_smul' r x := by
    ext j
    by_cases hji : j = i
    · simp [hji]
      ring
    · simp [hji]

private lemma sum_collapseIndex [Fintype σ] (i : σ) (x : Option σ → ℝ) (F : σ → ℝ) :
    ∑ k, x k * F (collapseIndex i k) = ∑ j, splitLinearMap i x j * F j := by
  rw [Fintype.sum_option]
  simp only [splitLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_add_distrib,
    add_mul, collapseIndex]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

private lemma constantCoeff_elementarySplitting (f : MvPolynomial σ ℝ) (i : σ) :
    constantCoeff (elementarySplitting i f) = constantCoeff f := by
  rw [constantCoeff_eq, constantCoeff_eq,
    ← optionEquivLeft_coeff_some_coeff_none ℝ σ (0 : Option σ →₀ ℕ)
      (elementarySplitting i f)]
  simp only [Finsupp.some_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_zero_optionEquivLeft_elementarySplitting]

private lemma hessianAtZero_elementarySplitting_apply (f : MvPolynomial σ ℝ) (i : σ)
    (k l : Option σ) :
    hessianAtZero (elementarySplitting i f) k l =
      hessianAtZero f (collapseIndex i k) (collapseIndex i l) := by
  simp [hessianAtZero, pderiv_elementarySplitting, constantCoeff_elementarySplitting]

private lemma hessianAtZero_toQuadraticForm_elementarySplitting
    [Fintype σ] (f : MvPolynomial σ ℝ) (i : σ) :
    (hessianAtZero (elementarySplitting i f)).toQuadraticForm' =
      (hessianAtZero f).toQuadraticForm'.comp (splitLinearMap i) := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, QuadraticMap.comp_apply, smul_eq_mul,
    hessianAtZero_elementarySplitting_apply]
  calc
    (∑ k, ∑ l, x k * (x l * hessianAtZero f (collapseIndex i k) (collapseIndex i l))) =
        ∑ k, x k * ∑ l, x l * hessianAtZero f (collapseIndex i k) (collapseIndex i l) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ k, x k * ∑ l, splitLinearMap i x l *
        hessianAtZero f (collapseIndex i k) l := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sum_collapseIndex]
    _ = ∑ k, splitLinearMap i x k * ∑ l, splitLinearMap i x l *
        hessianAtZero f k l := by
      exact sum_collapseIndex i x
        (fun k ↦ ∑ l, splitLinearMap i x l * hessianAtZero f k l)
    _ = ∑ k, ∑ l, splitLinearMap i x k *
        (splitLinearMap i x l * hessianAtZero f k l) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]

private lemma HasAtMostOnePositiveEigenvalue.elementarySplitting
    [Fintype σ] (f : MvPolynomial σ ℝ) (i : σ)
    (hf : HasAtMostOnePositiveEigenvalue (hessianAtZero f)) :
    HasAtMostOnePositiveEigenvalue (hessianAtZero (elementarySplitting i f)) := by
  unfold HasAtMostOnePositiveEigenvalue at hf ⊢
  rw [hessianAtZero_toQuadraticForm_elementarySplitting]
  exact (sigPos_comp_le (hessianAtZero f).toQuadraticForm' (splitLinearMap i)).trans hf

/-! ### Main theorem -/

/-- Replacing one variable of a Lorentzian polynomial by the sum of that variable and a fresh
variable preserves the Lorentzian property. The fresh variable is indexed by `none : Option σ`.
-/
theorem IsLorentzian.elementary_splitting [Fintype σ] {f : MvPolynomial σ ℝ} {d : ℕ}
    (hf : f.IsLorentzian d) (i : σ) :
    (bind₁ (fun j ↦ X (some j) + if j = i then X none else 0) f).IsLorentzian d := by
  change (elementarySplitting i f).IsLorentzian d
  rw [isLorentzian_iff_isLorentzianRec] at hf ⊢
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
      match d with
      | 0 | 1 =>
          obtain ⟨hhom, hcoeff⟩ := hf
          exact ⟨hhom.elementarySplitting i, hcoeff.elementarySplitting i⟩
      | 2 =>
          obtain ⟨hhom, hcoeff, hconvex, hsignature⟩ := hf
          exact ⟨hhom.elementarySplitting i, hcoeff.elementarySplitting i,
            Set.MConvex.elementarySplitting_support hconvex i,
            HasAtMostOnePositiveEigenvalue.elementarySplitting f i hsignature⟩
      | n + 3 =>
          obtain ⟨hhom, hcoeff, hconvex, hderiv⟩ := hf
          refine ⟨hhom.elementarySplitting i, hcoeff.elementarySplitting i,
            Set.MConvex.elementarySplitting_support hconvex i, ?_⟩
          intro k
          rw [pderiv_elementarySplitting]
          exact ih (n + 2) (by omega) (hderiv (collapseIndex i k))

end HessianSignature

end MvPolynomial
