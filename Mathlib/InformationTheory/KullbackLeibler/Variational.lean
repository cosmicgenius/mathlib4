/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
todo

-/

open ENNReal MeasureTheory Real Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

-- Stupid coe lemma that I use multiple times but I thought was nontrivial
lemma finite_ennreal_coe_real_coe_ereal_eq_coe_ereal
  (x : ENNReal) (hx : x < ∞) : (x.toReal : EReal) = (x : EReal) := by
  calc
    (x.toReal : EReal)
      = (ENNReal.ofReal x.toReal : EReal) := by
          simp only [EReal.coe_ennreal_ofReal, toReal_nonneg, sup_of_le_left]
    _ = (x : EReal)                       := by
          rw [ENNReal.ofReal_toReal_eq_iff.mpr (lt_top_iff_ne_top.mp hx)]

noncomputable def lintegralPosPart (μ : Measure α) (f : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x) ∂μ
noncomputable def lintegralNegPart (μ : Measure α) (f : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-f x) ∂μ

/-!
Integral of a real function that takes values in the extended reals.
Note that ⊤ - ⊤ = ⊥, so an undefined integral is set to ⊥.
-/
noncomputable def integralEReal (μ : Measure α) (f : α → ℝ) : EReal :=
  lintegralPosPart μ f - lintegralNegPart μ f

/--
If f is integrable, then its extended real valued integral is the same as the Bochner integral.
-/
lemma integralEReal_is_bochner_if_integrable (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) :
    integralEReal μ f = (∫ x, f x ∂μ).toEReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  unfold integralEReal
  simp only [EReal.coe_sub]

  have hpos_finite : ∫⁻ (x : α), ENNReal.ofReal (f x) ∂μ < ∞ := by
    apply lt_of_le_of_lt _ hf.hasFiniteIntegral
    apply lintegral_mono
    intro x
    exact ofReal_le_enorm (f x)

  have hneg_finite : ∫⁻ (x : α), ENNReal.ofReal (-f x) ∂μ < ∞ := by
    apply lt_of_le_of_lt _ hf.hasFiniteIntegral
    apply lintegral_mono
    intro x
    simp
    rw [← enorm_neg]
    exact ofReal_le_enorm (-f x)

  rw [finite_ennreal_coe_real_coe_ereal_eq_coe_ereal _ hpos_finite,
      finite_ennreal_coe_real_coe_ereal_eq_coe_ereal _ hneg_finite]
  rfl

/--
A function f is integrable iff the lower Lebesgue integrals of the positive and negative parts
are both finite. This is because the L1 norm of f is just the sum of the aforementioned
lower Lebesgue integrals.
-/
lemma integral_pos_neg_ennreal_finite_iff_integrable (μ : Measure α) (f : α → ℝ)
  (hf : Measurable f) :
    lintegralPosPart μ f < ∞ ∧ lintegralNegPart μ f < ∞ ↔ Integrable f μ := by
  unfold lintegralPosPart lintegralNegPart Integrable HasFiniteIntegral
  simp [hf.aestronglyMeasurable]

  have h_pos_plus_neg_eq_norm_ptwise : ∀ x, ENNReal.ofReal (f x) + ENNReal.ofReal (-f x)
      = ‖f x‖ₑ := by
    intro x
    by_cases h_sign : 0 ≤ f x
    · have h_sign_negation : - f x ≤ 0 := by linarith
      simp only [ENNReal.ofReal, Real.toNNReal_of_nonneg h_sign,
        Real.toNNReal_of_nonpos h_sign_negation, coe_zero, add_zero]
      exact (NNReal.enorm_eq ⟨f x, h_sign⟩).symm
    · push_neg at h_sign
      have h_sign : 0 ≤ -f x := by linarith
      have h_sign_negation : f x ≤ 0 := by linarith
      simp only [ENNReal.ofReal, Real.toNNReal_of_nonpos h_sign_negation, coe_zero,
        Real.toNNReal_of_nonneg h_sign, zero_add]
      rw [← enorm_neg]
      refine (NNReal.enorm_eq ⟨-f x, h_sign⟩).symm

  have h_pos_plus_neg_eq_norm : ∫⁻ x, ENNReal.ofReal (f x) ∂μ + ∫⁻ x, ENNReal.ofReal (-f x) ∂μ =
      ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [← lintegral_add_left]
    · exact lintegral_congr h_pos_plus_neg_eq_norm_ptwise
    · exact ENNReal.measurable_ofReal.comp hf

  rw [← h_pos_plus_neg_eq_norm]
  exact add_lt_top.symm

/--
The above implies that f is integrable iff its extended real valued integral is finite.
-/
lemma integralEReal_is_finite_iff_integrable (μ : Measure α) (f : α → ℝ) (hf : Measurable f) :
    integralEReal μ f < ⊤ ∧ integralEReal μ f > ⊥ ↔ Integrable f μ := by
  unfold integralEReal
  rw [← integral_pos_neg_ennreal_finite_iff_integrable μ f hf]
  simp only [lt_top_iff_ne_top, ne_eq, EReal.sub_coe_ennreal_eq_top_iff, not_and, Decidable.not_not,
    gt_iff_lt, bot_lt_iff_ne_bot, EReal.sub_coe_ennreal_eq_bot_iff, and_congr_left_iff]
  tauto

def expIntegrableRealFunctions (ν : Measure α) : Set (α → ℝ) :=
  { f | Measurable f ∧ Integrable (exp ∘ f) ν }

/--
The integral of the negative part of the log-likelihood ratio `llr μ ν` with respect to
`μ` is always finite, and bounded by `1/e`. Importantly, it is finite
(`lintegral_neg_part_llr_lt_top`), so the extended real valued integral of the log-likelihood ratio
is nonnegative even in the extended reals.
-/
lemma lintegral_neg_part_llr_le_one_div_e [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    lintegralNegPart μ (llr μ ν) ≤ ENNReal.ofReal (exp (-1)) * ν Set.univ := by

  have h_pointwise_bound : ∀ᵐ x ∂ν, μ.rnDeriv ν x * ENNReal.ofReal (-llr μ ν x) ≤
      ENNReal.ofReal (exp (-1)) := by
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    let d := μ.rnDeriv ν x
    calc
      μ.rnDeriv ν x * ENNReal.ofReal (-llr μ ν x)
      _ = d * ENNReal.ofReal (-log d.toReal) := by rfl
      _ = ENNReal.ofReal (d.toReal * -log d.toReal) := by
            convert (ofReal_mul toReal_nonneg).symm
            exact (ofReal_toReal_eq_iff.mpr (lt_top_iff_ne_top.mp hx)).symm
      _ ≤ ENNReal.ofReal (exp (-1)) := by
            gcongr 1
            convert isMaxOn_iff.mp Real.isMaxOn_negMulLog d.toReal toReal_nonneg using 1
            · unfold negMulLog
              simp only [mul_neg, neg_mul]
            · unfold negMulLog
              simp only [log_exp, mul_neg, mul_one, neg_neg]

  calc
    lintegralNegPart μ (llr μ ν)
      = ∫⁻ x, ENNReal.ofReal (-llr μ ν x) ∂μ := by rfl
    _ = ∫⁻ x, μ.rnDeriv ν x * ENNReal.ofReal (-llr μ ν x) ∂ν := by
          refine (lintegral_rnDeriv_mul hμν ?_).symm
          apply Measurable.aemeasurable
          exact (MeasureTheory.measurable_llr μ ν).neg.ennreal_ofReal
    _ ≤ ∫⁻ x, ENNReal.ofReal (exp (-1)) ∂ν := lintegral_mono_ae h_pointwise_bound
    _ = ENNReal.ofReal (exp (-1)) * ν Set.univ := lintegral_const _

lemma lintegral_neg_part_llr_lt_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    lintegralNegPart μ (llr μ ν) < ∞ := by
  have := lintegral_neg_part_llr_le_one_div_e h_ac
  refine lt_of_le_of_lt this ?_
  rw [mul_comm]
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (measure_ne_top ν Set.univ))
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)


open Classical in
/--
The extended real-valued integral of the log-likelihood ratio `llr μ ν` with respect to `μ`
is given by the standard Bochner integral if it is integrable, and is `⊤` otherwise.
-/
lemma integralEReal_llr_eq_ite [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    integralEReal μ (llr μ ν) =
      if Integrable (llr μ ν) μ then ↑(∫ x, llr μ ν x ∂μ) else ⊤ := by
  split_ifs with h_integrable
  · exact integralEReal_is_bochner_if_integrable μ (llr μ ν) h_integrable
  · have lintegral_neg_part_llr_finite := lintegral_neg_part_llr_lt_top h_ac
    rw [← integral_pos_neg_ennreal_finite_iff_integrable μ (llr μ ν) (measurable_llr μ ν)]
      at h_integrable
    simp only [lintegral_neg_part_llr_finite, and_true, not_lt, top_le_iff] at h_integrable

    unfold integralEReal

    rw [EReal.sub_coe_ennreal_eq_top_iff]
    exact ⟨h_integrable, lt_top_iff_ne_top.mp lintegral_neg_part_llr_finite⟩

-- Another dumb lemma
lemma const_indicator_integrable_if_support_finite (S : Set α) (hS_measurable : MeasurableSet S)
  (hS_finite : μ S < ∞) (c : ℝ) : Integrable (S.indicator fun _ => c) μ := by
  rw [integrable_indicator_iff hS_measurable, integrableOn_const_iff]
  right; exact hS_finite

noncomputable def donskerVaradhanFunctional
  (μ : Measure α) (ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (f : expIntegrableRealFunctions ν) : EReal :=
    integralEReal μ f.1 - log (∫ x, exp (f.1 x) ∂ν)

/--
If μ is not absolutely continuous wrt ν, then we can construct f such that the Donsker-Varadhan
functional is arbitrarily large.
-/
lemma donsker_varadhan_not_absCont_infinite_sup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ¬ μ ≪ ν) : ∀ b < ∞, ∃ f : expIntegrableRealFunctions ν,
    (b : EReal) ≤ donskerVaradhanFunctional μ ν f := by

  -- Find some measurable t such that μ t > 0 but ν t = 0.
  unfold Measure.AbsolutelyContinuous at hμν
  push_neg at hμν
  obtain ⟨s, hνs, hμs⟩ := hμν
  obtain ⟨t, hst, ht_measurable, hμts, hνts⟩ := exists_measurable_superset₂ μ ν s

  let c := (μ t).toReal

  have hμt : μ t ≠ 0 ∧ μ t ≠ ∞ := by
    rw [hμts]
    exact ⟨hμs, measure_ne_top μ s⟩

  have hc : c > 0 := by
    unfold c
    rw [gt_iff_lt, ENNReal.toReal_pos_iff]
    exact ⟨Ne.bot_lt hμt.1, Ne.lt_top hμt.2⟩

  have hνt : ν t = 0 := by rw [hνts]; exact hνs

  intro b hb
  -- Use the indicator c / d * 1_t
  let f : α → ℝ := t.indicator fun _ => b.toReal / c

  have h_f_measurable : Measurable f :=
    Measurable.indicator (measurable_const (a := b.toReal / c)) ht_measurable

  have h_f_exp_one_ν_ae : exp ∘ f =ᵐ[ν] fun _ => 1 := by
    filter_upwards [compl_mem_ae_iff.mpr hνt]
    simp [f]
    tauto

  have h_f_exp_ν_integrable : Integrable (exp ∘ f) ν :=
    Integrable.congr (integrable_const 1) h_f_exp_one_ν_ae.symm

  use ⟨f, ⟨h_f_measurable, h_f_exp_ν_integrable⟩⟩

  have h_f_nonneg : b.toReal / c ≥ 0 := div_nonneg toReal_nonneg (le_of_lt hc)

  have h_f_μ_integrable : Integrable f μ := const_indicator_integrable_if_support_finite
    t ht_measurable (measure_lt_top μ t) (b.toReal / c)

  unfold donskerVaradhanFunctional
  rw [integralEReal_is_bochner_if_integrable μ f h_f_μ_integrable]
  simp_rw [← Function.comp_apply (f := exp) (g := f),
    integral_congr_ae h_f_exp_one_ν_ae, f, integral_indicator ht_measurable,
    setIntegral_const, integral_const]
  unfold c
  simp only [smul_eq_mul, measureReal_univ_eq_one, mul_one, log_one, EReal.coe_zero,
    sub_zero]
  unfold Measure.real
  field_simp [(ne_of_gt hc : (μ t).toReal ≠ 0)]

  rw [finite_ennreal_coe_real_coe_ereal_eq_coe_ereal _ hb]

/--
Under the conditions μ ≪ ν and Integrable (llr μ ν) μ, the equality klDiv μ ν =
donskerVaradhanFunctional μ ν g is achieved at the log-likelihood ratio g = llr μ ν.

There is an annoying issue that this only holds true for the extended real value log-likelihood
ratio which is -∞ on the set where the Radon-Nikodym derivative μ.rnDeriv ν is zero (which can
have nonzero measure wrt ν). But log 0 = 0, so it is not. Thus, we must instead consider
the family of functions where llr μ ν is modified to be arbitrarily small on that set.
-/
lemma donsker_varadhan_modified_llr_approaches_equality
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_llr_μ_integrable : Integrable (llr μ ν) μ) : ∀ b : ℝ,
    (b : EReal) < ↑(klDiv μ ν) → ∃ g : expIntegrableRealFunctions ν,
    (b : EReal) < donskerVaradhanFunctional μ ν g := by
  intro b h_b_lt_kl
  let f := llr μ ν

  let klReal := ∫ x, f x ∂μ

  -- Some basic facts about klReal since klDiv < ∞.
  have h_klReal_nonneg : 0 ≤ klReal := by
    convert integral_llr_add_sub_measure_univ_nonneg hμν h_llr_μ_integrable using 1
    simp only [measureReal_univ_eq_one, add_sub_cancel_right]
    rfl

  have h_klDiv_eq_coe_klReal: klDiv μ ν = ENNReal.ofReal klReal := by
    rw [klDiv_of_ac_of_integrable hμν h_llr_μ_integrable]
    simp only [measureReal_univ_eq_one, add_sub_cancel_right]
    rfl

  have h_klReal_coe_eq_klDiv_coe : (klReal : EReal) = ↑(klDiv μ ν) := by
    calc
      (klReal : EReal)
        = (ENNReal.ofReal klReal : EReal) := by
          simp only [EReal.coe_ennreal_ofReal, EReal.coe_eq_coe_iff, left_eq_sup]
          exact h_klReal_nonneg
      _ = ↑(klDiv μ ν) := by
          rw [h_klDiv_eq_coe_klReal]

  rw [← h_klReal_coe_eq_klDiv_coe] at h_b_lt_kl

  let ε := (klReal - b) / 2
  have hε : ε > 0 := by
    unfold ε
    simp only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right, sub_pos]
    unfold klReal
    exact EReal.coe_lt_coe_iff.mp h_b_lt_kl

  let rn_deriv_zero_set : Set α := { x : α | μ.rnDeriv ν x = 0}
  let c := log (ν.real rn_deriv_zero_set) - log ε
  let f_fixed := f - rn_deriv_zero_set.indicator fun _ => c

  have h_f_fixed_on_rn_deriv_zero_set : ∀ x : rn_deriv_zero_set, f_fixed x = - c := by
    intro ⟨x, hx⟩
    unfold f_fixed f llr
    simp only [Pi.sub_apply, hx, indicator_of_mem, sub_eq_neg_self, log_eq_zero]
    rw [hx]
    left
    exact toReal_zero

  have h_fixed_on_comp_rn_deriv_zero_set : ∀ x : (rn_deriv_zero_setᶜ : Set α),
      f_fixed x = f x := by
    intro x
    unfold f_fixed
    simp only [Pi.sub_apply, sub_eq_self, indicator_apply_eq_zero]
    intro hx
    exfalso
    exact absurd hx x.2

  have h_rn_deriv_zero_set_measurable : MeasurableSet rn_deriv_zero_set :=
    measurableSet_eq_fun' (Measure.measurable_rnDeriv μ ν) measurable_const

  have h_f_fixed_measurable : Measurable f_fixed := Measurable.sub_stronglyMeasurable
    (measurable_llr μ ν) (StronglyMeasurable.indicator stronglyMeasurable_const
    h_rn_deriv_zero_set_measurable)

  have h_rn_deriv_zero_set_μ_null : μ rn_deriv_zero_set = 0 := by
    unfold rn_deriv_zero_set
    have h_rn_deriv_pos := Measure.rnDeriv_pos hμν
    rw [ae_iff] at h_rn_deriv_pos
    convert h_rn_deriv_pos using 2
    ext x
    simp only [mem_setOf_eq, not_lt, nonpos_iff_eq_zero]

  have h_f_fixed_eq_f_ae_μ : f_fixed =ᵐ[μ] f := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h_rn_deriv_zero_set_μ_null] with x hx
    simp only [Pi.sub_apply, Set.indicator_of_notMem hx, sub_zero, f_fixed]

  have h_f_fixed_μ_integrable : Integrable f_fixed μ :=
    (integrable_congr (id (Filter.EventuallyEq.symm h_f_fixed_eq_f_ae_μ))).mp h_llr_μ_integrable

  have h_indicator_integrable : Integrable (rn_deriv_zero_set.indicator (fun _ ↦ c)) μ :=
    const_indicator_integrable_if_support_finite rn_deriv_zero_set
      h_rn_deriv_zero_set_measurable (measure_lt_top μ rn_deriv_zero_set) c

  have h_f_fixed_μ_integral : (↑(∫ x, f_fixed x ∂μ) : EReal) = ↑(∫ x, f x ∂ μ) := by
    congr 1
    exact integral_congr_ae h_f_fixed_eq_f_ae_μ

  -- On rn_deriv_zero_set, plug in f_fixed x = -c. We can evaluate the integral directly.
  have h_integral_f_fixed_on_rn_deriv_zero_set : ∫ x in rn_deriv_zero_set, exp (f_fixed x) ∂ν
      = ν.real rn_deriv_zero_set * exp (-c) := by
    have : ∀ x : α, x ∈ rn_deriv_zero_set → exp (f_fixed x) = exp (-c) := by
      intro x hx
      congr
      exact h_f_fixed_on_rn_deriv_zero_set ⟨x, hx⟩

    rw [setIntegral_congr_fun h_rn_deriv_zero_set_measurable this]
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      smul_eq_mul]

  -- On rn_deriv_zero_setᶜ, plug in f_fixed x = f x = llr μ ν x.
  -- We can evaluate the integral directly.
  have h_integral_f_fixed_on_rn_deriv_zero_set_compl :
      ∫ x in rn_deriv_zero_setᶜ, exp (f_fixed x) ∂ν = 1 := by
    have : ∀ᵐ x ∂ν, x ∈ rn_deriv_zero_setᶜ → exp (f_fixed x) = (μ.rnDeriv ν x).toReal := by
      filter_upwards [exp_llr μ ν] with x h_exp_llr hx
      unfold rn_deriv_zero_set at hx
      have hx' : μ.rnDeriv ν x ≠ 0 := hx
      rw [if_neg hx'] at h_exp_llr
      rw [h_fixed_on_comp_rn_deriv_zero_set ⟨x, hx⟩]
      exact h_exp_llr

    rw [setIntegral_congr_ae h_rn_deriv_zero_set_measurable.compl this,
      Measure.setIntegral_toReal_rnDeriv hμν]
    unfold Measure.real
    rw [toReal_eq_one_iff, MeasureTheory.measure_compl h_rn_deriv_zero_set_measurable,
      measure_univ, h_rn_deriv_zero_set_μ_null]
    · simp only [tsub_zero]
    · rw [h_rn_deriv_zero_set_μ_null]
      exact zero_ne_top

  have h_f_fixed_exp_ν_integrable : Integrable (exp ∘ f_fixed) ν := by
    by_cases h_rn_deriv_zero_set_ν_measure : ν rn_deriv_zero_set = 0
    · -- If rn_deriv_zero_set is a ν-null set, then f = f_fixed ν-ae,
      -- so the exponential of the latter is integrable.
      have h_integrand_ae_eq : ∀ᵐ x ∂ν, (exp ∘ f) x = (exp ∘ f_fixed) x := by
        unfold f_fixed
        by_cases hc : c = 0
        · filter_upwards
          intro x
          simp only [Function.comp_apply, hc, indicator_zero, Pi.sub_apply, sub_zero]
        · rw [ae_iff]
          convert h_rn_deriv_zero_set_ν_measure using 2
          ext x
          simp only [Function.comp_apply, Pi.sub_apply, exp_eq_exp, mem_setOf_eq,
            eq_sub_iff_add_eq, add_eq_left, indicator_apply_eq_zero, Classical.not_imp,
            and_iff_left_iff_imp]
          tauto

      have h_llr_exp_ν_integrable : Integrable (exp ∘ llr μ ν) ν :=
        MeasureTheory.integrable_exp_llr_of_finite μ ν

      exact Integrable.congr h_llr_exp_ν_integrable h_integrand_ae_eq
    · -- If not, then exp ∘ f_fixed is integrable on each rn_deriv_zero_set and rn_deriv_zero_setᶜ
      -- since its Bochner integral is nonzero.
      have h_integrable_on_rn_deriv_zero_set : IntegrableOn (exp ∘ f_fixed) rn_deriv_zero_set
          ν := by
        apply Integrable.of_integral_ne_zero
        simp only [Function.comp_apply, h_integral_f_fixed_on_rn_deriv_zero_set, ne_eq,
          mul_eq_zero, exp_ne_zero, or_false]
        rw [measureReal_eq_zero_iff]
        exact h_rn_deriv_zero_set_ν_measure

      have h_integrable_on_rn_deriv_zero_set_compl : IntegrableOn (exp ∘ f_fixed)
          rn_deriv_zero_setᶜ ν := by
        apply Integrable.of_integral_ne_zero
        simp only [Function.comp_apply, h_integral_f_fixed_on_rn_deriv_zero_set_compl, ne_eq,
          one_ne_zero, not_false_eq_true]

      -- Integrable on parts implies integrable on union
      have h_integrable_on_union := h_integrable_on_rn_deriv_zero_set.union
        h_integrable_on_rn_deriv_zero_set_compl
      rw [union_compl_self, integrableOn_univ] at h_integrable_on_union
      exact h_integrable_on_union

  use ⟨f_fixed, ⟨h_f_fixed_measurable, h_f_fixed_exp_ν_integrable⟩⟩

  have h_integral_exp_f_fixed_ν : ∫ x, exp (f_fixed x) ∂ν =
      1 + ν.real rn_deriv_zero_set * exp (-c) := by
    simp_rw [← Function.comp_apply (f := exp) (g := f_fixed),
      ← integral_add_compl h_rn_deriv_zero_set_measurable h_f_fixed_exp_ν_integrable,
      Function.comp_apply]

    rw [h_integral_f_fixed_on_rn_deriv_zero_set, h_integral_f_fixed_on_rn_deriv_zero_set_compl]
    linarith

  have h_donsker_varadhan_functional_eq : donskerVaradhanFunctional μ ν
      ⟨f_fixed, ⟨h_f_fixed_measurable, h_f_fixed_exp_ν_integrable⟩⟩ =
      klDiv μ ν - log (1 + ν.real rn_deriv_zero_set * exp (-c)) := by
    unfold donskerVaradhanFunctional

    rw [integralEReal_is_bochner_if_integrable μ f_fixed h_f_fixed_μ_integrable,
      ← h_klReal_coe_eq_klDiv_coe, h_f_fixed_μ_integral, h_integral_exp_f_fixed_ν]

  rw [h_donsker_varadhan_functional_eq]

  by_cases h_ν_rn_deriv_zero_set : ν.real rn_deriv_zero_set = 0
  · rw [h_ν_rn_deriv_zero_set, ← h_klReal_coe_eq_klDiv_coe]
    simp only [zero_mul, add_zero, log_one, EReal.coe_zero, sub_zero]
    gcongr
  · unfold c
    have : 0 < ν.real rn_deriv_zero_set :=
      lt_of_le_of_ne' (toReal_nonneg (a := ν rn_deriv_zero_set)) h_ν_rn_deriv_zero_set
    rw [neg_sub, exp_sub, exp_log hε, exp_log this, mul_div_cancel₀ ε h_ν_rn_deriv_zero_set,
        ← h_klReal_coe_eq_klDiv_coe,  ← EReal.coe_sub]
    gcongr
    calc
      b < b + ε := by exact lt_add_of_pos_right b hε
      _ = klReal - ε := by ring
      _ ≤ klReal - log (1 + ε) := by
            linarith [log_le_sub_one_of_pos (x := 1 + ε) (by linarith [hε])]
    -- induction hw : w using EReal.rec with
    -- | bot =>
    --   rw [← h_klReal, ← EReal.coe_sub]
    --   exact EReal.bot_lt_coe _
    -- | top =>
    --   exfalso
    --   rw [hw] at h_w_lt_kl
    --   exact not_top_lt h_w_lt_kl
    -- | coe wReal' =>
    --   have h_wReal' : wReal = wReal' := by
    --     unfold wReal
    --     rw [hw]
    --     exact EReal.toReal_coe _

    --   rw [← h_klReal, ← EReal.coe_sub, ← h_wReal']
    --   apply EReal.coe_strictMono
    --   calc
    --     wReal < wReal + ε := by exact lt_add_of_pos_right wReal hε
    --         _ = klReal - ε := by ring
    --         _ ≤ klReal - log (1 + ε) := by
    --               linarith [log_le_sub_one_of_pos (x := 1 + ε) (by linarith [hε])]


/-- **Donsker-Varadhan Variational Formula**
Let μ, ν be finite measures on α. Then the KL
divergence D_KL(μ || ν) is the supremum over all f : α → ℝ
with exp ∘ f is integrable wrt ν of ∫ f dμ - log ∫ exp ∘ f dν
-/
theorem donsker_varadhan_variational_formula
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (klDiv μ ν : EReal) = ⨆ f : expIntegrableRealFunctions ν, donskerVaradhanFunctional μ ν f
      := by

  -- If ¬ μ ≪ ν, by definition, the KL divergence is ∞.
  -- In addition, we can make f large on a set that has nonzero wrt μ
  -- but is a null set wrt ν to show that the supremum is ∞.
  by_cases hμν : μ ≪ ν; swap;
  · have hsup_infinite : ⨆ f : expIntegrableRealFunctions ν,
        donskerVaradhanFunctional μ ν f = ⊤ := by
      rw [iSup_eq_top]
      intro b hb
      let bpos := max b.toReal 0
      let succ_bpos := 1 + bpos
      have hsucc_bpos_ge_0 : succ_bpos ≥ 0 := by
        calc
          1 + bpos ≥ bpos := by simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le_one]
                 _ ≥ 0    := by unfold bpos; simp only [ge_iff_le, le_sup_right]

      obtain ⟨f, hf⟩ := donsker_varadhan_not_absCont_infinite_sup hμν
        (ENNReal.ofReal succ_bpos) ofReal_lt_top
      use f

      refine lt_of_lt_of_le ?_ hf
      calc
        b ≤ (b.toReal : EReal)         := EReal.le_coe_toReal (lt_top_iff_ne_top.mp hb)
        _ ≤ (max b.toReal 0 : EReal)   := by simp only [le_sup_left]
        _ = (bpos : EReal)             := by rfl
        _ < (succ_bpos : EReal)        := by rw [EReal.coe_lt_coe_iff]; unfold succ_bpos; simp
        _ = (ENNReal.ofReal succ_bpos) := by simp only [EReal.coe_ennreal_ofReal,
          EReal.coe_eq_coe_iff, left_eq_sup, hsucc_bpos_ge_0]

    rw [klDiv_of_not_ac hμν, hsup_infinite]
    exact EReal.coe_ennreal_top

  -- Let f be the llr between μ and ν. We'll try to plug f into the functional.
  let f := llr μ ν

  have h_f_exp_ν_integrable : Integrable (exp ∘ f) ν :=
    MeasureTheory.integrable_exp_llr_of_finite μ ν

  have h_f_measurable := measurable_llr μ ν
  let f_ν_exp_integrable : expIntegrableRealFunctions ν :=
    ⟨f, ⟨h_f_measurable, h_f_exp_ν_integrable⟩⟩

  -- If the llr f is not integrable wrt μ, then by definition, the KL divergence is ∞.
  -- In addition, plugging in f to the supremum gives ∞.
  by_cases h_f_μ_integrable : Integrable f μ; swap;
  · have hsup_infinite : ⨆ f : expIntegrableRealFunctions ν,
        donskerVaradhanFunctional μ ν f = ⊤ := by
      rw [iSup_eq_top]
      intro b hb
      use f_ν_exp_integrable

      unfold donskerVaradhanFunctional f_ν_exp_integrable
      unfold f at h_f_μ_integrable
      rw [integralEReal_llr_eq_ite hμν, if_neg h_f_μ_integrable]
      simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.top_sub]
      exact hb

    rw [klDiv_of_not_integrable h_f_μ_integrable, hsup_infinite]
    rfl

  -- Now split the finite case into showing ≤ and ≥
  haveI : Nonempty (expIntegrableRealFunctions ν) := ⟨f_ν_exp_integrable⟩
  refine (iSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_).symm
  · -- We'll prove that for any g, the expression inside the supremum ≤ the KL divergence.
    intro ⟨g, ⟨hg_measurable, hg_exp_ν_integrable⟩⟩
    unfold donskerVaradhanFunctional

    -- The g tilted measure is important
    have hμν_tilted : μ ≪ ν.tilted g :=
      Measure.AbsolutelyContinuous.trans hμν (absolutelyContinuous_tilted hg_exp_ν_integrable)
    haveI : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hg_exp_ν_integrable

    -- Take cases on the value of the integral of g wrt μ.
    induction h_integral_μg_val : integralEReal μ g using EReal.rec with
    | bot =>
      -- If it is ⊥, then the inequality is trivial true.
      simp only [EReal.bot_sub, bot_le]
    | top =>
      -- We'll show that it cannot be ⊤. It suffices to show that the positive part has
      -- finite integral. We can bound it pointwise using basically the same decomposition
      -- as "Main computation" below.
      -- TODO(Anthony Wang): See if we can combine this with "Main computation".
      exfalso
      have h_g_decomp : g =ᵐ[μ] llr μ ν - llr μ (ν.tilted g) +
          fun x => log (∫ x, exp (g x) ∂ν) := by
        filter_upwards [llr_tilted_right hμν hg_exp_ν_integrable] with x hx
        simp [hx]

      have h_g_decomp_pos : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
          ENNReal.ofReal (llr μ ν x) + ENNReal.ofReal (- llr μ (ν.tilted g) x) +
          ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) := by
        filter_upwards [h_g_decomp] with x hx
        calc
          ENNReal.ofReal (g x)
            = ENNReal.ofReal (llr μ ν x - llr μ (ν.tilted g) x + log (∫ x, exp (g x) ∂ν)) := by
                rw [hx]
                rfl
          _ ≤ ENNReal.ofReal (llr μ ν x - llr μ (ν.tilted g) x) +
              ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) := ofReal_add_le
          _ ≤ ENNReal.ofReal (llr μ ν x) + ENNReal.ofReal (- llr μ (ν.tilted g) x) +
              ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) := by
                gcongr
                exact ofReal_add_le

      -- h_g_decomp_pos decompses the intgeral into 3 terms. Each term's integral is finite.
      have h1_finite : ∫⁻ (x : α), ENNReal.ofReal (llr μ ν x) ∂μ < ∞ :=
        ((integral_pos_neg_ennreal_finite_iff_integrable μ f h_f_measurable).mpr
          h_f_μ_integrable).1

      have h2_finite : ∫⁻ x, ENNReal.ofReal (- llr μ (ν.tilted g) x) ∂μ < ∞ :=
        lintegral_neg_part_llr_lt_top hμν_tilted

      have h3_finite : ∫⁻ x, ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) ∂μ < ∞ := by
        simp only [lintegral_const, measure_univ, mul_one, ofReal_lt_top]

      have h_integral_pos_finite : lintegralPosPart μ g < ∞ := by
        unfold lintegralPosPart
        calc
          ∫⁻ x, ENNReal.ofReal (g x) ∂μ
            ≤ ∫⁻ x, ENNReal.ofReal (llr μ ν x) + ENNReal.ofReal (- llr μ (ν.tilted g) x) +
              ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) ∂μ := lintegral_mono_ae h_g_decomp_pos
          _ = ∫⁻ x, ENNReal.ofReal (llr μ ν x) ∂μ +
              ∫⁻ x, ENNReal.ofReal (- llr μ (ν.tilted g) x) ∂μ +
              ∫⁻ x, ENNReal.ofReal (log (∫ x, exp (g x) ∂ν)) ∂μ := by
                -- Do it in this order to make the functions simpler to prove measurability for
                rw [lintegral_add_right, lintegral_add_left]
                · exact ENNReal.measurable_ofReal.comp h_f_measurable
                · exact measurable_const
          _ < ∞ := by
                rw [add_lt_top, add_lt_top]
                exact ⟨⟨h1_finite, h2_finite⟩, h3_finite⟩

      unfold integralEReal at h_integral_μg_val
      have h_integral_pos_infinite := (EReal.sub_coe_ennreal_eq_top_iff.mp h_integral_μg_val).1
      exact (ne_of_lt h_integral_pos_finite) h_integral_pos_infinite

    | coe =>
      -- Otherwise, integralEReal μ g is finite
      have h_gμ_integral_finite : integralEReal μ g < ⊤ ∧ integralEReal μ g > ⊥ := by
        rw [h_integral_μg_val]
        exact ⟨EReal.coe_lt_top _, EReal.bot_lt_coe _⟩
      have h_gμ_integrable : Integrable g μ :=
        (integralEReal_is_finite_iff_integrable μ g hg_measurable).mp h_gμ_integral_finite

      rw [← h_integral_μg_val]

      -- Main computation. We can write the Donsker Varadhan functional as a difference
      -- klDiv μ ν - kl μ (v.tilted g) which is ≤ klDiv μ ν by nonnegativity.
      calc
        integralEReal μ g - log (∫ x, exp (g x) ∂ν)
          = ∫ x, g x ∂μ - log (∫ x, exp (g x) ∂ν) := by
            rw [integralEReal_is_bochner_if_integrable μ g h_gμ_integrable]
        _ = ∫ x, llr μ ν x ∂μ - ∫ x, llr μ (ν.tilted g) x ∂μ := by
            rw [MeasureTheory.integral_llr_tilted_right hμν h_gμ_integrable
              hg_exp_ν_integrable h_f_μ_integrable, ← EReal.coe_sub, ← EReal.coe_sub]
            ring_nf
        _ ≤ ∫ x, llr μ ν x ∂μ + (ν.tilted g).real univ - μ.real univ := by
            rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
            have := integrable_llr_tilted_right hμν h_gμ_integrable h_f_μ_integrable
              hg_exp_ν_integrable
            linarith [integral_llr_add_sub_measure_univ_nonneg hμν_tilted this]
        _ = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
            simp only [measureReal_univ_eq_one, EReal.coe_one]
        _ = klDiv μ ν := by
            rw [← EReal.coe_add, ← EReal.coe_sub, klDiv_of_ac_of_integrable hμν h_f_μ_integrable,
              EReal.coe_ennreal_ofReal, EReal.coe_eq_coe_iff, left_eq_sup]
            exact integral_llr_add_sub_measure_univ_nonneg hμν h_f_μ_integrable

  · -- See docstring
    intro b h_b_lt_klDiv
    induction hb : b using EReal.rec with
    | bot =>
      -- Vacuous, just need to pick any witness. We'll use -1
      have : ↑(-1) < (klDiv μ ν : EReal) := by
        calc
          (-1 : EReal) < (0 : EReal) := by simp only [EReal.neg_lt_zero, zero_lt_one]
                     _ ≤ (klDiv μ ν : EReal) := by exact EReal.coe_ennreal_nonneg _

      obtain ⟨g, hg⟩ := donsker_varadhan_modified_llr_approaches_equality
        hμν h_f_μ_integrable (-1) this
      use g
      exact bot_lt_of_lt hg
    | top =>
      -- Not possible due to h_b_lt_klDiv : b < ↑(klDiv μ ν)
      exfalso
      rw [hb] at h_b_lt_klDiv
      exact not_top_lt h_b_lt_klDiv
    | coe bReal =>
      -- Key case. Use the lemma donsker_varadhan_modified_llr_approaches_equality.
      rw [hb] at h_b_lt_klDiv
      exact donsker_varadhan_modified_llr_approaches_equality
        hμν h_f_μ_integrable bReal h_b_lt_klDiv


end InformationTheory
