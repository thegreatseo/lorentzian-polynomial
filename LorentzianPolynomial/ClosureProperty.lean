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

This file states closure properties of Lorentzian polynomials.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ : Type*} [DecidableEq σ]

private def splitVariable (i j : σ) : MvPolynomial (Option σ) ℝ :=
  X (some j) + if j = i then X none else 0

private def elementarySplitting (i : σ) :
    MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial (Option σ) ℝ :=
  bind₁ (splitVariable i)

@[simp] private lemma elementarySplitting_X (i j : σ) :
    elementarySplitting i (X j) = splitVariable i j := by
  simp [elementarySplitting]

omit [DecidableEq σ] in
private lemma CoeffNonneg.C {r : ℝ} (hr : 0 ≤ r) :
    CoeffNonneg (C r : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [coeff_C]
  split_ifs <;> positivity

omit [DecidableEq σ] in
private lemma CoeffNonneg.X (i : σ) : CoeffNonneg (X i : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [coeff_X]
  split_ifs <;> positivity

omit [DecidableEq σ] in
private lemma CoeffNonneg.add {p q : MvPolynomial σ ℝ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p + q) := by
  intro m
  rw [coeff_add]
  exact add_nonneg (hp m) (hq m)

omit [DecidableEq σ] in
private lemma CoeffNonneg.mul {p q : MvPolynomial σ ℝ}
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p * q) := by
  classical
  intro m
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x.1) (hq x.2)

omit [DecidableEq σ] in
private lemma CoeffNonneg.pow {p : MvPolynomial σ ℝ} (hp : CoeffNonneg p) (n : ℕ) :
    CoeffNonneg (p ^ n) := by
  induction n with
  | zero => simpa using CoeffNonneg.C (σ := σ) zero_le_one
  | succ n hn => simpa [pow_succ] using hn.mul hp

omit [DecidableEq σ] in
private lemma CoeffNonneg.sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (p i)) : CoeffNonneg (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.C (σ := σ) le_rfl
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hp i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

omit [DecidableEq σ] in
private lemma CoeffNonneg.prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i ∈ s, CoeffNonneg (p i)) : CoeffNonneg (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffNonneg.C (σ := σ) zero_le_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

private lemma CoeffNonneg.elementarySplitting {f : MvPolynomial σ ℝ}
    (hf : CoeffNonneg f) (i : σ) : CoeffNonneg (elementarySplitting i f) := by
  rw [f.as_sum, map_sum]
  apply CoeffNonneg.sum
  intro m hm
  rw [MvPolynomial.elementarySplitting, bind₁_monomial]
  apply CoeffNonneg.mul (CoeffNonneg.C (hf m))
  apply CoeffNonneg.prod
  intro j hj
  apply CoeffNonneg.pow
  apply CoeffNonneg.add (CoeffNonneg.X (some j))
  split_ifs
  · exact CoeffNonneg.X none
  · simpa using CoeffNonneg.C (σ := Option σ) le_rfl

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

private lemma pderiv_splitVariable_some (i j k : σ) :
    pderiv (some j) (splitVariable i k) = if k = j then 1 else 0 := by
  by_cases hki : k = i
  · subst k
    by_cases hij : i = j
    · subst j; simp [splitVariable]
    · simp [splitVariable, hij]
  · by_cases hkj : k = j
    · subst k; simp [splitVariable, hki]
    · simp [splitVariable, hki, hkj]

private lemma pderiv_splitVariable_none (i j : σ) :
    pderiv none (splitVariable i j) = if j = i then 1 else 0 := by
  by_cases hji : j = i <;> simp [splitVariable, hji]

private lemma pderiv_elementarySplitting_some (f : MvPolynomial σ ℝ) (i j : σ) :
    pderiv (some j) (elementarySplitting i f) = elementarySplitting i (pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [elementarySplitting]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      simp only [map_mul, elementarySplitting_X, pderiv_mul, hp,
        pderiv_splitVariable_some, map_add]
      by_cases hkj : k = j
      · subst k; simp
      · simp [hkj]

private lemma pderiv_elementarySplitting_none (f : MvPolynomial σ ℝ) (i : σ) :
    pderiv none (elementarySplitting i f) = elementarySplitting i (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [elementarySplitting]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, elementarySplitting_X, pderiv_mul, hp,
        pderiv_splitVariable_none, map_add]
      by_cases hji : j = i
      · subst j; simp
      · simp [hji]

private def splitCollapse (i : σ) (m : Option σ →₀ ℕ) : σ →₀ ℕ :=
  m.some + Finsupp.single i (m none)

private def collapseIndex (i : σ) : Option σ → σ
  | none => i
  | some j => j

omit [DecidableEq σ] in
@[simp] private lemma splitCollapse_add (i : σ) (x y : Option σ →₀ ℕ) :
    splitCollapse i (x + y) = splitCollapse i x + splitCollapse i y := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [splitCollapse]
    omega
  · simp [splitCollapse, hji]

omit [DecidableEq σ] in
@[simp] private lemma splitCollapse_single (i : σ) (k : Option σ) (n : ℕ) :
    splitCollapse i (Finsupp.single k n) = Finsupp.single (collapseIndex i k) n := by
  classical
  ext j
  cases k with
  | none => simp [splitCollapse, collapseIndex, Finsupp.single_apply]
  | some a =>
      by_cases hai : a = i
      · subst a; simp [splitCollapse, collapseIndex]
      · simp [splitCollapse, collapseIndex, Finsupp.single_apply]

omit [DecidableEq σ] in
private lemma splitCollapse_exchange (i : σ) (x : Option σ →₀ ℕ) (k l : Option σ)
    (hk : x k ≠ 0) :
    splitCollapse i (x - Finsupp.single k 1 + Finsupp.single l 1) =
      splitCollapse i x - Finsupp.single (collapseIndex i k) 1 +
        Finsupp.single (collapseIndex i l) 1 := by
  classical
  have hx := congrArg (splitCollapse i) (Finsupp.sub_add_single_one_cancel hk)
  rw [splitCollapse_add, splitCollapse_single] at hx
  have hsub : splitCollapse i (x - Finsupp.single k 1) =
      splitCollapse i x - Finsupp.single (collapseIndex i k) 1 := by
    ext j
    have hxj := congrArg (fun z : σ →₀ ℕ ↦ z j) hx
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hxj ⊢
    omega
  rw [splitCollapse_add, hsub, splitCollapse_single]

omit [DecidableEq σ] in
private lemma exists_lt_of_splitCollapse_lt (i : σ) (x y : Option σ →₀ ℕ) (j : σ)
    (h : splitCollapse i x j < splitCollapse i y j) :
    ∃ k, collapseIndex i k = j ∧ x k < y k := by
  classical
  by_cases hji : j = i
  · subst j
    by_cases hnone : x none < y none
    · exact ⟨none, rfl, hnone⟩
    · refine ⟨some i, rfl, ?_⟩
      simp [splitCollapse] at h
      omega
  · refine ⟨some j, rfl, ?_⟩
    simpa [splitCollapse, hji] using h

omit [DecidableEq σ] in
private lemma exists_same_collapseIndex_lt (i : σ) (x y : Option σ →₀ ℕ)
    (k : Option σ) (hk : y k < x k)
    (h : ¬splitCollapse i y (collapseIndex i k) < splitCollapse i x (collapseIndex i k)) :
    ∃ l, collapseIndex i l = collapseIndex i k ∧ x l < y l := by
  classical
  cases k with
  | none =>
      refine ⟨some i, rfl, ?_⟩
      simp [splitCollapse, collapseIndex] at h
      omega
  | some j =>
      by_cases hji : j = i
      · subst j
        refine ⟨none, rfl, ?_⟩
        simp [splitCollapse, collapseIndex] at h
        omega
      · exfalso
        apply h
        simpa [splitCollapse, collapseIndex, hji] using hk

omit [DecidableEq σ] in
private lemma splitCollapse_collapseIndex_ne_zero (i : σ) (x : Option σ →₀ ℕ)
    (k : Option σ) (hk : x k ≠ 0) : splitCollapse i x (collapseIndex i k) ≠ 0 := by
  classical
  cases k with
  | none =>
      simp [splitCollapse, collapseIndex] at hk ⊢
      omega
  | some j =>
      by_cases hji : j = i
      · subst j
        simp [splitCollapse, collapseIndex] at hk ⊢
        omega
      · simpa [splitCollapse, collapseIndex, hji] using hk

private lemma eval_zero_optionEquivLeft_elementarySplitting (f : MvPolynomial σ ℝ) (i : σ) :
    Polynomial.eval 0 (optionEquivLeft ℝ σ (elementarySplitting i f)) = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [elementarySplitting]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [map_mul, elementarySplitting_X, map_mul, Polynomial.eval_mul, hp]
      by_cases hji : j = i <;> simp [splitVariable, hji]

omit [DecidableEq σ] in
private lemma mem_support_pderiv_iff' (p : MvPolynomial σ ℝ) (i : σ) (m : σ →₀ ℕ) :
    m ∈ (pderiv i p).support ↔ m + Finsupp.single i 1 ∈ p.support := by
  rw [mem_support_iff, mem_support_iff, coeff_pderiv]
  constructor
  · intro h hc
    exact h (by simp [hc])
  · intro h
    exact mul_ne_zero h (by positivity)

private lemma mem_support_elementarySplitting_iff (f : MvPolynomial σ ℝ) (i : σ)
    (m : Option σ →₀ ℕ) :
    m ∈ (elementarySplitting i f).support ↔ splitCollapse i m ∈ f.support := by
  induction hmn : m none generalizing f m with
  | zero =>
      rw [mem_support_iff, mem_support_iff,
        ← optionEquivLeft_coeff_some_coeff_none ℝ σ m (elementarySplitting i f), hmn,
        Polynomial.coeff_zero_eq_eval_zero, eval_zero_optionEquivLeft_elementarySplitting]
      simp [splitCollapse, hmn]
  | succ n ih =>
      let m' := m - Finsupp.single none 1
      have hmnone : m none ≠ 0 := by omega
      have hm'none : m' none = n := by simp [m', hmn]
      have hmadd : m' + Finsupp.single none 1 = m :=
        Finsupp.sub_add_single_one_cancel hmnone
      have hcollapse : splitCollapse i m' + Finsupp.single i 1 = splitCollapse i m := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [splitCollapse, m', hmn]
          omega
        · simp [splitCollapse, m', hji]
      conv_lhs => rw [← hmadd]
      rw [← mem_support_pderiv_iff', pderiv_elementarySplitting_none,
        ih (pderiv i f) m' hm'none, mem_support_pderiv_iff', hcollapse]

private lemma Set.MConvex.elementarySplitting_support {f : MvPolynomial σ ℝ}
    (hf : Set.MConvex (f.support : Set (σ →₀ ℕ))) (i : σ) :
    Set.MConvex ((elementarySplitting i f).support : Set (Option σ →₀ ℕ)) := by
  intro x hx y hy k hk
  have hx' : splitCollapse i x ∈ f.support :=
    (mem_support_elementarySplitting_iff f i x).mp hx
  have hy' : splitCollapse i y ∈ f.support :=
    (mem_support_elementarySplitting_iff f i y).mp hy
  by_cases hcollapse :
      splitCollapse i y (collapseIndex i k) < splitCollapse i x (collapseIndex i k)
  · obtain ⟨b, hb, hxb, hyb⟩ := hf hx' hy' (collapseIndex i k) hcollapse
    obtain ⟨l, hbl, hl⟩ := exists_lt_of_splitCollapse_lt i x y b hb
    have hxk : x k ≠ 0 := by omega
    have hyl : y l ≠ 0 := by omega
    refine ⟨l, hl, (mem_support_elementarySplitting_iff f i _).mpr ?_,
      (mem_support_elementarySplitting_iff f i _).mpr ?_⟩
    · rw [splitCollapse_exchange i x k l hxk, hbl]
      exact hxb
    · rw [splitCollapse_exchange i y l k hyl, hbl]
      exact hyb
  · obtain ⟨l, hlbase, hl⟩ :=
      exists_same_collapseIndex_lt i x y k hk hcollapse
    have hxk : x k ≠ 0 := by omega
    have hyl : y l ≠ 0 := by omega
    have hybase : splitCollapse i y (collapseIndex i k) ≠ 0 := by
      rw [← hlbase]
      exact splitCollapse_collapseIndex_ne_zero i y l hyl
    refine ⟨l, hl, (mem_support_elementarySplitting_iff f i _).mpr ?_,
      (mem_support_elementarySplitting_iff f i _).mpr ?_⟩
    · rw [splitCollapse_exchange i x k l hxk, hlbase,
        Finsupp.sub_add_single_one_cancel
          (splitCollapse_collapseIndex_ne_zero i x k hxk)]
      exact hx'
    · rw [splitCollapse_exchange i y l k hyl, hlbase,
        Finsupp.sub_add_single_one_cancel
          hybase]
      exact hy'

omit [DecidableEq σ] in
private lemma sigPos_comp_le [Finite σ] (Q : QuadraticForm ℝ (σ → ℝ))
    (L : (Option σ → ℝ) →ₗ[ℝ] (σ → ℝ)) :
    sigPos (Q.comp L) ≤ sigPos Q := by
  letI := Fintype.ofFinite σ
  obtain ⟨V, hVrank, hVpos⟩ :=
    exists_finrank_eq_sigPos_and_posDef (Q.comp L)
  let LV : V →ₗ[ℝ] (σ → ℝ) := L.comp V.subtype
  have hLVinj : Function.Injective LV := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hpos := hVpos (x - y) hne
    change L (x : Option σ → ℝ) = L (y : Option σ → ℝ) at hxy
    simp [hxy] at hpos
  have hRangePos : (Q.restrict (LinearMap.range LV)).PosDef := by
    rintro ⟨_, ⟨v, rfl⟩⟩ hv
    have hv0 : v ≠ 0 := by
      intro hv0
      apply hv
      subst v
      simp
    simpa [LV] using hVpos v hv0
  calc
    sigPos (Q.comp L) = Module.finrank ℝ V := hVrank.symm
    _ = Module.finrank ℝ (LinearMap.range LV) :=
      (LinearMap.finrank_range_of_inj hLVinj).symm
    _ ≤ sigPos Q := le_sigPos_of_posDef Q hRangePos

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
  have hi : (∑ j : σ, if j = i then x none * F j else 0) = x none * F i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [hi]
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
  cases k with
  | none =>
      cases l with
      | none =>
          simp [hessianAtZero, pderiv_elementarySplitting_none,
            constantCoeff_elementarySplitting, collapseIndex]
      | some l =>
          simp [hessianAtZero, pderiv_elementarySplitting_none,
            pderiv_elementarySplitting_some, constantCoeff_elementarySplitting, collapseIndex]
  | some k =>
      cases l with
      | none =>
          simp [hessianAtZero, pderiv_elementarySplitting_none,
            pderiv_elementarySplitting_some, constantCoeff_elementarySplitting, collapseIndex]
      | some l =>
          simp [hessianAtZero, pderiv_elementarySplitting_some,
            constantCoeff_elementarySplitting, collapseIndex]

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
      | 0 =>
          exact ⟨hf.1.elementarySplitting i, hf.2.elementarySplitting i⟩
      | 1 =>
          exact ⟨hf.1.elementarySplitting i, hf.2.elementarySplitting i⟩
      | 2 =>
          exact ⟨hf.1.elementarySplitting i, hf.2.1.elementarySplitting i,
            Set.MConvex.elementarySplitting_support hf.2.2.1 i,
            HasAtMostOnePositiveEigenvalue.elementarySplitting f i hf.2.2.2⟩
      | n + 3 =>
          refine ⟨hf.1.elementarySplitting i, hf.2.1.elementarySplitting i,
            Set.MConvex.elementarySplitting_support hf.2.2.1 i, ?_⟩
          intro k
          cases k with
          | none =>
              rw [pderiv_elementarySplitting_none]
              exact ih (n + 2) (by omega) (hf.2.2.2 i)
          | some j =>
              rw [pderiv_elementarySplitting_some]
              exact ih (n + 2) (by omega) (hf.2.2.2 j)

end MvPolynomial
