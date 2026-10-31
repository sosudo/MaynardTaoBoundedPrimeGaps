/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math, Michael Stoll, Mathlib contributors

This file includes the Mathlib v4.33.1 LogDirichlet section and compatibility
lemmas backported to Lean 4.32, followed by the Axiom Math prime-zeta estimates.
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import PrimeGapsTheory.ForMathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section
open Complex Filter Nat Topology EulerProduct DirichletCharacter
open scoped LSeries.notation
namespace Complex
lemma hasSum_taylorSeries_neg_log' {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ (n + 1) / (n + 1)) (-log (1 - z)) := by
  rw_mod_cast [hasSum_nat_add_iff 1 (f := fun n ↦ z ^ n / n) (g := -log (1 - z))]
  simpa using hasSum_taylorSeries_neg_log hz
end Complex
lemma LSeries_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) :
    LSeries f s = ∑' n, f n / (n ^ s) := by
  simp [LSeries, LSeries.term_def₀ hf, cpow_neg, div_eq_mul_inv]
open Nat.Primes in
theorem tsum_primes_pow_eq {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T0Space α] {f : ℕ → α}
    (hf : Summable fun n : {n // IsPrimePow n} ↦ f n.1) :
    ∑' (p : Nat.Primes) (n : ℕ), f (p ^ (n + 1)) = ∑' n : {n : ℕ // IsPrimePow n}, f n := calc
  _ = ∑' p : Nat.Primes × ℕ, f (prodNatEquiv p) := by
    simpa using (hf.comp_injective prodNatEquiv.injective).tsum_prod.symm
  _ = _ := by rw [← Equiv.tsum_eq prodNatEquiv]
section LogDirichlet

open Real hiding log exp_nat_mul exp_add
open ArithmeticFunction Primes Summable

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- For `1 < s.re`, the sum over primes of `-log (1 - χ p * p ^ (-s))` — the logarithm of the Euler
product — equals the `L`-series of `n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n ↦ χ n * Λ n / Real.log n) s := by
  have hpow_le (p : Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p ↦ (hasSum_taylorSeries_neg_log' (hpow_le p)).tsum_eq.symm),
    LSeries_def₀ (by simp)]
  let f : ℕ → ℂ := fun n ↦ χ n * Λ n / Real.log n * ((n : ℂ) ^ (-s))
  calc
    _ = ∑' (p : Primes) (k : ℕ), (χ (p ^ (k + 1)) * ((p ^ (k + 1) : ℕ) : ℂ) ^ (-s)) *
          Λ (p ^ (k + 1)) / Real.log (p ^ (k + 1)) := by
      refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
      have : Complex.log p ≠ 0 := mod_cast p.prop.log_ne_zero
      simp [mul_pow, ← cpow_nat_mul, ← natCast_cpow_natCast_mul, vonMangoldt_apply_pow,
        vonMangoldt_apply_prime p.2, field]
    _ = ∑' n : {n : ℕ // IsPrimePow n}, f n := by
      rw [← tsum_primes_pow_eq]
      · exact tsum_congr fun p ↦ tsum_congr fun k ↦ (by unfold f; simp; ring)
      · apply comp_injective _ Subtype.coe_injective (f := f)
        apply of_norm_bounded_eventually_nat (g := (↑· ^ (-s.re)))
        · simp [hs]
        · filter_upwards [eventually_gt_atTop 1] with n hn
          simp only [f, norm_mul, norm_div, norm_real, norm_eq_abs]
          grw [norm_le_one, vonMangoldt_le_log]
          have := log_pos (x := n) (mod_cast hn)
          field_simp
          rw [← ofReal_natCast n, norm_cpow_eq_rpow_re_of_nonneg (by simp) (by simp; grind)]
          simp
    _ = _ := by
      simp only [div_eq_mul_inv _ (_ ^ _), ← cpow_neg]
      suffices (Function.support f) ⊆ {n | IsPrimePow n} from
        tsum_subtype_eq_of_support_subset this
      intro n hn
      contrapose! hn
      simp [f, vonMangoldt_eq_zero_iff.mpr hn]

/-- For `1 < s.re`, the Dirichlet L-function is the exponential of the `L`-series of
`n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ χ n * Λ n / Real.log n) s) = L ↗χ s := by
  rw [← eulerProduct_log_eq_LSeries χ hs, LSeries_eulerProduct_exp_log χ hs]

theorem riemannZeta_eq_exp_LSeries {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ Λ n / Real.log n) s) = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter ℂ 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/-- For real `s > 1`, the logarithm of the (real) Riemann zeta function equals
`∑' n, Λ n / (n ^ s * Real.log n)`, where `Λ` is the von Mangoldt function.
-/
theorem log_riemannZeta_eq {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re = ∑' n, Λ n / (n ^ s * Real.log n) := by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs), LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

end LogDirichlet

open Set Nat
namespace Nat.Primes
lemma tsum_eq_tsum_ite {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (f : ℕ → α) :
    ∑' p : Nat.Primes, f p = ∑' n : ℕ, if Nat.Prime n then f n else 0 := by
  classical
  change (∑' p : ↥({n : ℕ | Nat.Prime n} : Set ℕ), f p.1) = _
  simpa only [Nat.Primes, Set.indicator_apply, Set.mem_setOf_eq] using (tsum_subtype {n : ℕ | n.Prime} f)
lemma summable_iff_summable_ite {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (f : ℕ → α) :
    Summable (fun p : Nat.Primes ↦ f p) ↔ Summable (fun n : ℕ ↦ if Nat.Prime n then f n else 0) := by
  classical
  change Summable (f ∘ (Subtype.val : ↥({n : ℕ | Nat.Prime n} : Set ℕ) → ℕ)) ↔ _
  rw [summable_subtype_iff_indicator]
  have heq : ({n : ℕ | n.Prime} : Set ℕ).indicator f = (fun n ↦ if n.Prime then f n else 0) := by
    funext n
    simp [Set.indicator_apply]
  rw [heq]
end Nat.Primes

@[expose] public section

open Real Complex Finset Nat
open ArithmeticFunction

theorem hasSum_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) (riemannZeta s) := by
  convert (summable_one_div_nat_cpow.mpr hs).hasSum
  exact zeta_eq_tsum_one_div_nat_cpow hs

theorem hasSum_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ σ) (riemannZeta σ).re := by
  convert hasSum_re <| hasSum_riemannZeta (s := σ) (by simpa) with n
  rw [← ofReal_natCast, ← ofReal_cpow (by positivity), ← ofReal_one, ← ofReal_div, ofReal_re]

theorem re_riemannZeta_eq_tsum_one_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re = ∑' n : ℕ, 1 / (n : ℝ) ^ σ :=
  (hasSum_re_riemannZeta hσ).tsum_eq.symm

theorem one_lt_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) : 1 < (riemannZeta σ).re := by
  have hrange : (1 : ℝ) < ∑ n ∈ range 3, 1 / (n : ℝ) ^ σ := by
    simpa [sum_range_succ, zero_rpow (by positivity : σ ≠ 0)] using
      lt_add_of_pos_right (1 : ℝ) (one_div_pos.mpr <| rpow_pos_of_pos two_pos σ)
  exact hrange.trans_le <| sum_le_hasSum _
    (fun _ _ ↦ one_div_nonneg.mpr <| rpow_nonneg (by positivity) _) (hasSum_re_riemannZeta hσ)

theorem summable_vonMangoldt_div_pow_mul_log {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n ↦ Λ n / (n ^ σ * Real.log n) := by
  refine .of_tsum_ne_zero <| ne_of_gt ?_
  rw [← log_riemannZeta_eq hσ]
  exact log_pos <| one_lt_re_riemannZeta hσ

theorem re_riemannZeta_le_div_sub_one {σ : ℝ} (hσ : 1 < σ) : (riemannZeta σ).re ≤ σ / (σ - 1) := by
  have hintegrable := integrableOn_Ioi_rpow_of_lt (neg_lt_neg hσ) one_pos
  have hcomp := AntitoneOn.tsum_comp_add_le_integral 1 ((antitoneOn_rpow_Ioi_of_exponent_nonpos
    (neg_nonpos.mpr (by positivity))).mono (Set.Ici_subset_Ioi.mpr (by positivity)))
    (by norm_cast) fun _ _ ↦ rpow_nonneg (by grind) _
  rw [re_riemannZeta_eq_tsum_one_div_rpow hσ,
    ← Summable.sum_add_tsum_nat_add 2 (summable_one_div_nat_rpow.mpr hσ)]
  simp_rw [← inv_eq_one_div, ← rpow_neg (Nat.cast_nonneg _)]
  grw [hcomp, integral_Ioi_rpow_of_lt (by grind) (by positivity)]
  suffices 1 + -1 / (-σ + 1) = σ / (σ - 1) by
    simp [sum_range_succ, zero_rpow (by grind : -σ ≠ 0), this]
  grind

theorem log_re_riemannZeta_le_log_sub_log_sub_one {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re.log ≤ σ.log - (σ - 1).log := by
  grw [re_riemannZeta_le_div_sub_one hσ, log_div (by positivity) (by positivity)]
  · exact riemannZeta_re_pos_of_one_lt hσ

theorem Real.summable_one_div_prime_rpow {σ : ℝ} :
    Summable (fun p : Primes ↦ 1 / (p : ℝ) ^ σ) ↔ 1 < σ := by
  by_cases! hσ : 1 < σ
  · simp only [hσ, iff_true]
    exact (summable_one_div_nat_rpow.mpr hσ).subtype Nat.Prime
  · simp only [hσ.not_gt, iff_false]
    exact fun H ↦ Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity)
      fun p ↦ one_div_le_one_div_of_le (by positivity [p.2.ne_zero]) <|
        rpow_le_self_of_one_le (by simpa using p.2.one_le) hσ

theorem Complex.summable_one_div_prime_cpow {s : ℂ} :
    Summable (fun p : Primes ↦ 1 / (p : ℂ) ^ s) ↔ 1 < s.re := by
  rw [← summable_one_div_prime_rpow, ← summable_norm_iff]
  simp [norm_cpow_eq_rpow_re_of_pos, ← ofReal_natCast,
    show ∀ p : Primes, 0 < (p : ℝ) by simpa using fun p ↦ p.2.pos]

theorem tsum_prime_rpow_le_log_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : Primes, (1 / p ^ σ : ℝ) ≤ (riemannZeta σ).re.log := by
  rw [Primes.tsum_eq_tsum_ite fun n : ℕ ↦ 1 / (n : ℝ) ^ σ, log_riemannZeta_eq hσ]
  refine Summable.tsum_le_tsum (fun p ↦ ?_)
    ((Primes.summable_iff_summable_ite _).mp <| summable_one_div_prime_rpow.mpr hσ)
    (summable_vonMangoldt_div_pow_mul_log hσ)
  split_ifs with hp
  · rw [vonMangoldt_apply_prime hp, ← inv_eq_one_div,
      div_mul_cancel_right₀ ( _root_.ne_of_gt <| log_pos <| by simp [hp.one_lt])]
  · positivity

