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


/-!
Integral of a real function that takes values in the extended reals.
Note that ⊤ - ⊤ = ⊥, so an undefined integral is set to ⊥.
-/
noncomputable def integralEReal (μ : Measure α) (f : α → ℝ) : EReal :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂μ : EReal) -
  (∫⁻ x, ENNReal.ofReal (-f x) ∂μ : EReal)

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
    ∫⁻ x, ENNReal.ofReal (-llr μ ν x) ∂μ ≤ ENNReal.ofReal (1 / exp 1) * ν Set.univ := by
  sorry

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
    ∫⁻ x, ENNReal.ofReal (-llr μ ν x) ∂μ < ⊤ := by
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
This formalizes the fact that the KL-divergence `D(μ || ν)` is either a non-negative real
number or `+∞`.
-/
lemma integralEReal_llr_eq_ite [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    integralEReal μ (llr μ ν) =
      if h : Integrable (llr μ ν) μ then ↑(∫ x, llr μ ν x ∂μ) else ⊤ := by
  let f := llr μ ν
  -- The integral of the negative part is finite. This is the main argument.
  have h_neg_finite : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ < ⊤ := by
    exact lintegral_neg_part_llr_lt_top h_ac

  -- The definition of integrability simplifies due to the negative part being finite.
  have integrable_iff : Integrable f μ ↔ ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ := by
    sorry
    -- simp [Integrable, h_neg_finite, and_true]

  split_ifs with h_integrable
  · -- Case 1: The function is integrable.
    -- The `integralEReal` is the difference of the `lintegral`s of the pos and neg parts.
    rw [integralEReal_eq_integral_of_integrable h_integrable]
  · -- Case 2: The function is not integrable.
    -- By our simplification, this means the `lintegral` of the positive part is `⊤`.
    have h_pos_infinite : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ⊤ := by
      rw [← not_lt]
      exact (mt integrable_iff.mpr) h_integrable
    -- The `integralEReal` is defined as a difference in `EReal`.
    simp [integralEReal, h_pos_infinite, EReal.top_sub_coe_of_lt_top h_neg_finite]

/--
The extended real-valued integral of the log-likelihood ratio is finite if and only if
the log-likelihood ratio is integrable with respect to `μ`.
-/
-- lemma integralEReal_llr_isFinite_iff_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (h_ac : μ ≪ ν) :
--     (integralEReal μ (llr μ ν)).isFinite ↔ Integrable (llr μ ν) μ := by
--   rw [integralEReal_llr_eq_ite h_ac]
--   split_ifs with h_integrable
--   · -- If integrable, the result is `↑(∫ ...)` which is finite.
--     simp [EReal.isFinite_coe]
--   · -- If not integrable, the result is `⊤`, which is not finite.
--     simp

noncomputable def donskerVaradhanFunctional
  (μ : Measure α) (ν : Measure α)  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
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

  have hf_μ_integrable : Integrable f μ := by
    rw [← memLp_one_iff_integrable]
    apply memLp_of_bounded (a := 0) (b := b.toReal / c)
    · filter_upwards
      intro x
      simp only [f]
      by_cases hxt : x ∈ t
      · simp [hxt]
        exact div_nonneg toReal_nonneg (le_of_lt hc)
      · simp [hxt]
        exact div_nonneg toReal_nonneg (le_of_lt hc)
    · exact hf_measurable.aestronglyMeasurable

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
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]:
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
    sorry

  let f_ν_exp_integrable : expIntegrableRealFunctions ν :=
    ⟨f, ⟨measurable_llr μ ν, hf_exp_ν_integrable⟩⟩

  -- If the llr f is not integrable wrt μ, then by definition, the KL divergence is ∞.
  -- In addition, plugging in f to the supremum gives ∞.
  by_cases hfμ_integrable : Integrable f μ; swap;
  · have hsup_infinite : ⨆ f : expIntegrableRealFunctions ν,
        donskerVaradhanFunctional μ ν f = ⊤ := by
      rw [iSup_eq_top]
      intro b hb
      use f_ν_exp_integrable

      unfold objective
      rw [if_neg hfμ_integrable]
      exact hb

    rw [klDiv_of_not_integrable hfμ_integrable, hsup_infinite]

  -- -- Now split the finite case into showing ≤ and ≥
  -- apply le_antisymm
  -- · -- We claim that objective f ≥ the KL divergence
  --   refine le_iSup_of_le f_ν_exp_integrable ?_
  --   rw [if_pos hfμ_integrable]
  --   sorry
  -- · -- Prove that for any g, the expression inside the supremum ≤ the KL divergence.
  --   apply iSup_le
  --   intro ⟨g, ⟨hg_measurable, hg_exp_ν_integrable⟩⟩

  --   -- first show that g is μ integrable

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


def absolutelyContinuousFiniteMeasures (μ : Measure α) : Set (Measure α) :=
  {ν | IsFiniteMeasure ν ∧ ν ≪ μ}

/-- **Gibbs variational formula**:
If h is a real-valued integrable random variable wrt
a finite measure μ, then we have
`log ∫ exp h ∂μ = sup_{ν ≪ μ} [∫ h ∂ν - D_KL (ν || μ)]`
-/
theorem gibbs
  [IsFiniteMeasure μ] (h : α → ℝ) (hf_int : Integrable h μ) :
    log (∫ x, exp (h x) ∂μ) =
      ⨆ (ν : absolutelyContinuousFiniteMeasures μ),
      ∫ x, h x ∂ν - (klDiv ν μ).toReal := by
  sorry

end InformationTheory
