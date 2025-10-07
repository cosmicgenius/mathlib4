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

lemma integralEReal_is_finite_iff_integrable (μ : Measure α) (f : α → ℝ) (hf : Measurable f) :
    integralEReal μ f < ⊤ ∧ integralEReal μ f > ⊥ ↔ Integrable f μ := by
  unfold integralEReal
  rw [← integral_pos_neg_ennreal_finite_iff_integrable μ f hf]
  simp only [lt_top_iff_ne_top, ne_eq, EReal.sub_coe_ennreal_eq_top_iff, not_and, Decidable.not_not,
    gt_iff_lt, bot_lt_iff_ne_bot, EReal.sub_coe_ennreal_eq_bot_iff, and_congr_left_iff]
  tauto

def expIntegrableRealFunctions (ν : Measure α) : Set (α → ℝ) :=
  { f | Measurable f ∧ Integrable (exp ∘ f) ν }

-- lemma donsker_varadhan_key_lemma [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
--   (hμν : μ ≪ ν) (hllr_μν_integrable : Integrable (llr μ ν) μ)
--   (f : α → ℝ) (hf_measurable : Measurable f) (hf_exp_integrable : Integrable (exp ∘ f) ν) :
--     (Integrable (llr μ (ν.tilted f)) μ) →
--     (klDiv μ ν).toReal - (klDiv μ (ν.tilted f)).toReal = ∫ x, f x ∂μ -
--   log (∫ x, exp (f x) ∂ν) := by
--   let νf := ν.tilted f

--   have htilted_absCont : νf ≪ ν := tilted_absolutelyContinuous ν f
--   have habsCont_tilted : ν ≪ νf := absolutelyContinuous_tilted hf_exp_integrable

--   have hνf_prob : IsProbabilityMeasure νf := isProbabilityMeasure_tilted hf_exp_integrable

--   have hμ_νf_absCont : μ ≪ νf := Measure.AbsolutelyContinuous.trans hμν habsCont_tilted

--   have h_rnDeriv_mul : ∀ᵐ x ∂μ, μ.rnDeriv ν x = μ.rnDeriv νf x * νf.rnDeriv ν x :=
--     (Measure.AbsolutelyContinuous.ae_eq hμν (Measure.rnDeriv_mul_rnDeriv hμ_νf_absCont)).symm

--   have h_llr_sub : ∀ᵐ x ∂μ, llr μ ν x - llr μ νf x = llr νf ν x := by
--     unfold llr
--     rw [← ENNReal.toReal_sub_of_le, hx, ENNReal.toReal_mul, Real.log_mul]

--   intro hllr_μνf_integrable
--   calc
--     (klDiv μ ν).toReal - (klDiv μ νf).toReal
--       = ∫ x, llr μ ν x ∂μ - ∫ x, llr μ νf x ∂μ := by
--         rw [toReal_klDiv hμν hllr_μν_integrable, toReal_klDiv hμ_νf_absCont hllr_μνf_integrable]
--         rw [measureReal_univ_eq_one (μ := ν), measureReal_univ_eq_one (μ := νf)]
--         ring
--     _ = ∫ x, llr μ ν x - llr μ νf x ∂μ := by
--         rw [integral_sub hllr_μν_integrable hllr_μνf_integrable]
--     _ = ∫ x, llr νf ν x ∂μ := by

--     _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
--         sorry

/-- The integral of the negative part of the log-likelihood ratio `llr μ ν` with respect to
`μ` is always finite, and bounded by `1/e`. This is the key insight to show that the
KL-divergence is always well-defined (either a non-negative real or `+∞`). -/
lemma lintegral_neg_part_llr_le_one_div_e [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    lintegralNegPart μ (llr μ ν) ≤ ENNReal.ofReal (exp (-1)) * ν Set.univ := by
  calc
    lintegralNegPart μ (llr μ ν)
      = ∫⁻ x, ENNReal.ofReal (-log (μ.rnDeriv ν x).toReal) ∂μ := by rfl
    _ ≤ ENNReal.ofReal (exp (-1)) * ν Set.univ := by sorry

  -- unverified from gemini
  -- let f x := llr μ ν x
  -- let g x := (μ.rnDeriv ν x).toReal
  -- have hg : ∀ x, f x = Real.log (g x) := fun x  => by rfl
  -- -- Change of measure from μ to ν
  -- rw [lintegral_congr_ae (llr_ae_eq_log_rnDeriv h_ac),
  --     lintegral_mul_rnDeriv_eq_lintegral μ h_ac]
  -- let integrand ν x := ENNReal.ofReal (negPart (Real.log (g x))) * (μ.rnDeriv ν x)
  -- apply lintegral_le_of_le_ae
  -- -- We show the integrand is bounded pointwise by 1/e
  -- filter_upwards [h_ac.ae_le (μ.rnDeriv ν).prop] with x hx
  -- -- The integrand involves negPart, which is max(0, -f). It's non-zero only if f < 0.
  -- by_cases hf_neg : Real.log (g x) < 0
  -- · have hg_pos : 0 < g x := Real.log_pos_iff.mp (by linarith)
  --   simp only [integrand, negPart_of_neg hf_neg, hg, mul_eq_mul_left_iff, ofReal_eq_zero,
  --     ofReal_mul, Real.toNNReal_of_nonneg (le_of_lt hg_pos)]
  --   rw [ENNReal.ofReal_toReal (μ.rnDeriv ν x)]
  --   apply ENNReal.ofReal_le_ofReal
  --   -- This is the crucial mathematical inequality: -y * log y ≤ 1/e for y ∈ (0, 1)
  --   convert Real.neg_mul_log_le_one_div_e (g x)
  --   rw [neg_mul, mul_comm]
  -- · simp only [integrand, negPart_of_nonneg (not_lt.mp hf_neg), ofReal_zero, zero_mul]
  --   exact zero_le _

/-- The `lintegral` of the negative part of `llr μ ν` w.r.t. `μ` is finite. -/
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

lemma const_indicator_integrable_iff_support_finite (S : Set α) (hS : MeasurableSet S) (c : ℝ) :
    Integrable (S.indicator fun _ => c) μ ↔ μ S < ∞ := by
  sorry



noncomputable def donskerVaradhanFunctional
  (μ : Measure α) (ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (f : expIntegrableRealFunctions ν) : EReal :=
    integralEReal μ f.1 - log (∫ x, exp (f.1 x) ∂ν)

lemma donsker_varadhan_not_absCont_infinite_sup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hnot_absCont : ¬ μ ≪ ν) : ∀ b < ∞, ∃ f : expIntegrableRealFunctions ν,
    (b : EReal) ≤ donskerVaradhanFunctional μ ν f := by

  -- Find some measurable t such that μ t > 0 but ν t = 0.
  unfold Measure.AbsolutelyContinuous at hnot_absCont
  push_neg at hnot_absCont
  obtain ⟨s, hνs, hμs⟩ := hnot_absCont
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

  have hf_measurable : Measurable f :=
    Measurable.indicator (measurable_const (a := b.toReal / c)) ht_measurable

  have hf_exp_one_ν_ae : exp ∘ f =ᵐ[ν] fun _ => 1 := by
    filter_upwards [compl_mem_ae_iff.mpr hνt]
    simp [f]
    tauto

  have hf_exp_ν_integrable : Integrable (exp ∘ f) ν :=
    Integrable.congr (integrable_const 1) hf_exp_one_ν_ae.symm

  use ⟨f, ⟨hf_measurable, hf_exp_ν_integrable⟩⟩

  have hf_nonneg : b.toReal / c ≥ 0 := div_nonneg toReal_nonneg (le_of_lt hc)

  have hf_μ_integrable : Integrable f μ :=
    (const_indicator_integrable_iff_support_finite t ht_measurable (b.toReal / c)).mpr
    (measure_lt_top μ t)
    -- rw [← memLp_one_iff_integrable]
    -- apply memLp_of_bounded (a := 0) (b := b.toReal / c)
    -- · filter_upwards
    --   intro x
    --   simp only [f]
    --   by_cases hxt : x ∈ t
    --   · simp [hxt]
    --     exact div_nonneg toReal_nonneg (le_of_lt hc)
    --   · simp [hxt]
    --     exact div_nonneg toReal_nonneg (le_of_lt hc)
    -- · exact hf_measurable.aestronglyMeasurable

  unfold donskerVaradhanFunctional
  rw [integralEReal_is_bochner_if_integrable μ f hf_μ_integrable]
  simp_rw [← Function.comp_apply (f := exp) (g := f),
    integral_congr_ae hf_exp_one_ν_ae, f, integral_indicator ht_measurable,
    setIntegral_const, integral_const]
  unfold c
  simp only [smul_eq_mul, measureReal_univ_eq_one, mul_one, log_one, EReal.coe_zero,
    sub_zero]
  unfold Measure.real
  field_simp [(ne_of_gt hc : (μ t).toReal ≠ 0)]

  rw [finite_ennreal_coe_real_coe_ereal_eq_coe_ereal _ hb]

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

  -- Let f be the llr between μ and ν.
  let f := llr μ ν
  have hf_exp_ν_integrable : Integrable (exp ∘ f) ν := by
    -- exp ∘ f = μ.rnDeriv ν, so should follow from hμν : μ ≪ ν
    sorry

  have h_f_measurable := measurable_llr μ ν
  let f_ν_exp_integrable : expIntegrableRealFunctions ν := ⟨f, ⟨h_f_measurable, hf_exp_ν_integrable⟩⟩

  -- If the llr f is not integrable wrt μ, then by definition, the KL divergence is ∞.
  -- In addition, plugging in f to the supremum gives ∞.
  by_cases hfμ_integrable : Integrable f μ; swap;
  · have hsup_infinite : ⨆ f : expIntegrableRealFunctions ν,
        donskerVaradhanFunctional μ ν f = ⊤ := by
      rw [iSup_eq_top]
      intro b hb
      use f_ν_exp_integrable

      unfold donskerVaradhanFunctional f_ν_exp_integrable
      unfold f at hfμ_integrable
      rw [integralEReal_llr_eq_ite hμν, if_neg hfμ_integrable]
      simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, EReal.top_sub]
      exact hb

    rw [klDiv_of_not_integrable hfμ_integrable, hsup_infinite]
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

      -- Each term's integral is finite.
      have h1_finite : ∫⁻ (x : α), ENNReal.ofReal (llr μ ν x) ∂μ < ∞ :=
        ((integral_pos_neg_ennreal_finite_iff_integrable μ f h_f_measurable).mpr
          hfμ_integrable).1

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
    -- by_cases hgμ_integrable : Integrable g μ; swap;
    -- . have hgμ_ereal_integral_is_bot : integralEReal μ g = ⊥ := by
    --     rw [← not_bot_lt_iff]
    --     have hgμ_ereal_integral_infinite :=
    --       mt (integralEReal_isFinite_iff_integrable μ g).mp hgμ_integrable
    --     rw [And.comm] at hgμ_ereal_integral_infinite
    --     apply not_and'.mp hgμ_ereal_integral_infinite
    --     exact hgμ_ereal_integral_not_top

    --   rw [hgμ_ereal_integral_is_bot]
    --   simp only [EReal.bot_sub, bot_le]

      -- Main computation. We can write the Donsker Varadhan functional as a difference
      -- klDiv μ ν - kl μ (v.tilted g) which is ≤ klDiv μ ν by nonnegativity.
      calc
        integralEReal μ g - log (∫ x, exp (g x) ∂ν)
          = ∫ x, g x ∂μ - log (∫ x, exp (g x) ∂ν) := by
            rw [integralEReal_is_bochner_if_integrable μ g h_gμ_integrable]
        _ = ∫ x, llr μ ν x ∂μ - ∫ x, llr μ (ν.tilted g) x ∂μ := by
            rw [MeasureTheory.integral_llr_tilted_right hμν h_gμ_integrable
              hg_exp_ν_integrable hfμ_integrable, ← EReal.coe_sub, ← EReal.coe_sub]
            ring_nf
        _ ≤ ∫ x, llr μ ν x ∂μ + (ν.tilted g).real univ - μ.real univ := by
            rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
            linarith [integral_llr_add_sub_measure_univ_nonneg hμν_tilted
              (integrable_llr_tilted_right hμν h_gμ_integrable hfμ_integrable hg_exp_ν_integrable)]
        _ = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
            simp only [measureReal_univ_eq_one, EReal.coe_one]
        _ = klDiv μ ν := by
            rw [← EReal.coe_add, ← EReal.coe_sub, klDiv_of_ac_of_integrable hμν hfμ_integrable,
              EReal.coe_ennreal_ofReal, EReal.coe_eq_coe_iff, left_eq_sup]
            exact integral_llr_add_sub_measure_univ_nonneg hμν hfμ_integrable
  · -- To show ≤, we claim for the same f = llr μ ν,
    -- donskerVaradhanFunctional μ ν f = the KL divergence.
    -- Annoying detail here, we need to modify f to be arbitrarily small on the set
    -- where dμ / dν = 0 since f is currently not (log 0 = 0, not -∞).

    intro w hw

    by_cases h_w_bot : w > ⊥
    swap; sorry

    let ε := (↑(klDiv μ ν) - w).toReal / 2
    have hε : w + ε < klDiv μ ν ∧ ε > 0 := by
      sorry

    let c := 1 / ε
    let rn_deriv_zero_set : Set α := { x : α | μ.rnDeriv ν x = 0}
    let f_fixed := f - rn_deriv_zero_set.indicator fun _ => c

    have h_f_fixed_on_rn_deriv_zero_set : ∀ x : rn_deriv_zero_set, f_fixed x = f x - c := by
      intro x
      unfold f_fixed
      simp only [Pi.sub_apply, Subtype.coe_prop, indicator_of_mem]

    have h_fixed_on_comp_rn_deriv_zero_set : ∀ x : (rn_deriv_zero_setᶜ : Set α),
        f_fixed x = f x := by
      intro x
      unfold f_fixed
      simp only [Pi.sub_apply, sub_eq_self, indicator_apply_eq_zero]
      intro hx
      exfalso
      exact absurd hx x.2

    have h_rn_deriv_zero_set_measurable : MeasurableSet rn_deriv_zero_set := by sorry

    have h_rn_deriv_zero_μ_null : μ.real rn_deriv_zero_set = 0 := by
      rw [measureReal_eq_zero_iff]
      unfold rn_deriv_zero_set
      have h_rn_deriv_pos := Measure.rnDeriv_pos hμν
      rw [ae_iff] at h_rn_deriv_pos
      convert h_rn_deriv_pos using 2
      ext x
      simp only [Set.mem_setOf, not_lt, nonpos_iff_eq_zero]

    have h_f_fixed_measurable : Measurable f_fixed := by
      -- rw [Measurable.indicator (measurable_const) h_rn_deriv_zero_set_measurable]
      sorry

    have h_f_fixed_exp_ν_integrable : Integrable (exp ∘ f_fixed) ν := by
      -- Integrable.congr (integrable_const 1) hf_exp_one_ν_ae.symm
      sorry

    have h_f_fixed_eq_f_ae_μ : f_fixed =ᵐ[μ] f := by
      sorry

    have h_f_fixed_μ_integrable : Integrable f_fixed μ :=
      (integrable_congr (id (Filter.EventuallyEq.symm h_f_fixed_eq_f_ae_μ))).mp hfμ_integrable

    have h_indicator_integrable : Integrable (rn_deriv_zero_set.indicator (fun _ ↦ c)) μ :=
      (const_indicator_integrable_iff_support_finite rn_deriv_zero_set h_rn_deriv_zero_set_measurable c).mpr
      (measure_lt_top μ rn_deriv_zero_set)

    have h_f_fixed_μ_integral : (↑(∫ x, f_fixed x ∂μ) : EReal) = ↑(∫ x, f x ∂ μ) := by
      congr 1
      unfold f_fixed
      simp_rw [Pi.sub_apply, integral_sub hfμ_integrable h_indicator_integrable,
        integral_indicator h_rn_deriv_zero_set_measurable, setIntegral_const,
        h_rn_deriv_zero_μ_null]
      simp only [smul_eq_mul, zero_mul, sub_zero]

    use ⟨f_fixed, ⟨h_f_fixed_measurable, h_f_fixed_exp_ν_integrable⟩⟩

    have h_kl_div_eq_int_llr : (klDiv μ ν : EReal) = ↑(∫ x, llr μ ν x ∂μ) := by
      calc
        (klDiv μ ν : EReal)
          = ↑(ENNReal.ofReal (∫ x, llr μ ν x ∂μ)) := by
            rw [klDiv_of_ac_of_integrable hμν hfμ_integrable]
            simp only [measureReal_univ_eq_one, add_sub_cancel_right]
        _ = ↑(∫ x, llr μ ν x ∂μ) := by
            simp only [EReal.coe_ennreal_ofReal, EReal.coe_eq_coe_iff, sup_eq_left]
            convert integral_llr_add_sub_measure_univ_nonneg hμν hfμ_integrable using 1
            simp only [measureReal_univ_eq_one, add_sub_cancel_right]

    have : ∫ x, exp (f_fixed x) ∂ν = 1 + exp (-c) * ν.real rn_deriv_zero_set := by
      simp_rw [← Function.comp_apply (f := exp) (g := f_fixed),
        ← integral_add_compl h_rn_deriv_zero_set_measurable h_f_fixed_exp_ν_integrable]

      -- have : ∫ x in rn_deriv_zero_set, exp (f_fixed x) ∂μ = ℝ

      -- On rn_deriv_zero_set, f_fixed x = -c
      have h1 : ∫ x in rn_deriv_zero_set, exp (f_fixed x) ∂ν = exp (-c) * ν.real rn_deriv_zero_set := by
        sorry

      sorry


    have h_donsker_varadhan_functional_eq : donskerVaradhanFunctional μ ν
        ⟨f_fixed, ⟨h_f_fixed_measurable, h_f_fixed_exp_ν_integrable⟩⟩ =
        klDiv μ ν - exp (-c) * ν (rn_deriv_zero_set) := by
      unfold donskerVaradhanFunctional
      rw [integralEReal_is_bochner_if_integrable μ f_fixed h_f_fixed_μ_integrable]
      rw [h_kl_div_eq_int_llr]
      rw [h_f_fixed_μ_integral]


      sorry

    sorry



    -- refine le_iSup_of_le f_ν_exp_integrable ?_
    -- apply le_of_eq
    -- unfold donskerVaradhanFunctional

    -- rw [integralEReal_llr_eq_ite hμν, if_pos hfμ_integrable]

    -- have h_int_exp_f_eq_1 : ∫ x, exp (f x) ∂ν = 1 := by
    --   unfold f
    --   have h_exp_llr_eq_rn_deriv := exp_llr μ ν
    --   rw [integral_congr_ae (μ := ν) h_exp_llr_eq_rn_deriv]
    --   sorry
    --   -- haha its false because of log 0 = 0

    -- calc
    --   (klDiv μ ν : EReal)
    --     = ↑(ENNReal.ofReal (∫ x, llr μ ν x ∂μ)) := by
    --       rw [klDiv_of_ac_of_integrable hμν hfμ_integrable]
    --       simp only [measureReal_univ_eq_one, add_sub_cancel_right]
    --   _ = ↑(∫ x, llr μ ν x ∂μ) := by
    --       simp only [EReal.coe_ennreal_ofReal, EReal.coe_eq_coe_iff, sup_eq_left]
    --       convert integral_llr_add_sub_measure_univ_nonneg hμν hfμ_integrable using 1
    --       simp only [measureReal_univ_eq_one, add_sub_cancel_right]
    --   _ = ↑(∫ x, llr μ ν x ∂μ) - ↑(log (∫ x, exp (f x) ∂ν)) := by
    --     sorry

    -- apply iSup_eq_top

  --   -- by_cases μ ≪ ν ∧ Integrable f μ
  --   -- case pos hkl_finite =>
  --   --   rw [if_pos hkl_finite.2]
  --   --   sorry
  --     -- have h_rhs : ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν))
  --       -- = klDiv μ ν := by
  --       -- calc
  --       --   ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν))
  --       --     = ENNReal.ofReal (∫ x, llr μ ν x ∂μ - log (∫ x, (μ.rnDeriv ν x).toReal ∂ν)) := by
  --       --       simp only [f, llr, exp_log]

  --       --   _ =

  --   -- case neg hkl_infinite =>
  --   --   push_neg at hkl_infinite
  --   --   by_cases habsCont : μ ≪ ν
  --   --   · have hf_μ_nonintegrable := hkl_infinite habsCont

  --   --   .

  -- -- Prove that for any f, the expression inside the supremum ≤ the KL divergence.
  -- -- · apply iSup_le
  -- --   intro f
  -- --   let g := (f : α → ℝ)

  -- --   by_cases habs_cont : μ ≪ ν
  -- --   -- We can assume μ ≪ ν, since otherwise the inequality is trivially true.
  -- --   · let ν_tilted := ν.tilted g

  --     -- let dμν := rnDeriv μ ν
  --     -- let dv_tiltedν := rnDeriv ν ν_tilted

  --     -- have hν_tilted_absCont := tilted_absolutelyContinuous ν g

  --     -- have hg_measurable : Measurable g := f.2.1
  --     -- have hg_aemeasurable : AEMeasurable g ν := hg_measurable.aemeasurable (μ := ν)


  --     -- have h : ENNReal.ofReal ∘ exp ∘ g = ν_tilted.rnDeriv ν := by
  --     --   rw [← rnDeriv_tilted_left ν hg_aemeasurable]



  --     -- calc
  --     --  ∫ x, (f : α → ℝ) x ∂μ - log (∫ x, exp ((f : α → ℝ) x) ∂ν)

  --   --   sorry

  --   -- · rw [klDiv_of_not_ac habs_cont]
  --   --   exact le_top


-- def absolutelyContinuousFiniteMeasures (μ : Measure α) : Set (Measure α) :=
--   {ν | IsFiniteMeasure ν ∧ ν ≪ μ}

-- /-- **Gibbs variational formula**:
-- If h is a real-valued integrable random variable wrt
-- a finite measure μ, then we have
-- `log ∫ exp h ∂μ = sup_{ν ≪ μ} [∫ h ∂ν - D_KL (ν || μ)]`
-- -/
-- theorem gibbs
--   [IsFiniteMeasure μ] (h : α → ℝ) (hf_int : Integrable h μ) :
--     log (∫ x, exp (h x) ∂μ) =
--       ⨆ (ν : absolutelyContinuousFiniteMeasures μ),
--       ∫ x, h x ∂ν - (klDiv ν μ).toReal := by
--   sorry

end InformationTheory
