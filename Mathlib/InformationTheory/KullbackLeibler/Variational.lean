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

open Classical in
lemma donsker_varadhan_not_absCont_infinite_sup
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hnot_absCont : ¬ μ ≪ ν):
    ∀ b < ∞, ∃ f : expIntegrableRealFunctions ν,
      b ≤ if Integrable (f : α → ℝ) μ
        then ENNReal.ofReal (∫ x, (f : α → ℝ) x ∂μ - log (∫ x, exp ((f : α → ℝ) x) ∂ν))
        else ∞ := by

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
  let f_n : α → ℝ := t.indicator fun _ => b.toReal / c

  have hf_n_measurable : Measurable f_n :=
    Measurable.indicator (measurable_const (a := b.toReal / c)) ht_measurable

  have hf_n_exp_one_ν_ae : (exp ∘ f_n) =ᵐ[ν] fun _ => 1 := by
    filter_upwards [compl_mem_ae_iff.mpr hνt]
    simp [f_n]
    tauto

  have hf_n_exp_ν_integrable : Integrable (exp ∘ f_n) ν :=
    Integrable.congr (integrable_const 1) hf_n_exp_one_ν_ae.symm

  use ⟨f_n, ⟨hf_n_measurable, hf_n_exp_ν_integrable⟩⟩

  have hf_n_μ_integrable : Integrable f_n μ := by
    rw [← memLp_one_iff_integrable]
    apply memLp_of_bounded (a := 0) (b := b.toReal / c)
    · filter_upwards
      intro x
      simp only [f_n]
      by_cases hxt : x ∈ t
      · simp [hxt]
        exact div_nonneg toReal_nonneg (le_of_lt hc)
      · simp [hxt]
        exact div_nonneg toReal_nonneg (le_of_lt hc)
    · exact hf_n_measurable.aestronglyMeasurable

  simp_rw [if_pos hf_n_μ_integrable, ← Function.comp_apply (f := exp) (g := f_n),
    integral_congr_ae hf_n_exp_one_ν_ae, f_n, integral_indicator ht_measurable,
    setIntegral_const, integral_const]
  unfold c
  simp
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_toReal hμt.2,
    ENNReal.mul_div_cancel hμt.1 hμt.2, ofReal_toReal (lt_top_iff_ne_top.mp hb)]

open Classical in
/-- **Donsker-Varadhan Variational Formula**
Let μ, ν be finite measures on α. Then the KL
divergence D_KL(μ || ν) is the supremum over all f : α → ℝ
with exp ∘ f is integrable wrt ν of ∫ f dμ - log ∫ exp ∘ f dν
-/
theorem donsker_varadhan_variational_formula
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]:
    klDiv μ ν = ⨆ f : expIntegrableRealFunctions ν,
      if Integrable (f : α → ℝ) μ
        then ENNReal.ofReal (∫ x, (f : α → ℝ) x ∂μ - log (∫ x, exp ((f : α → ℝ) x) ∂ν))
        else ∞ := by

  let objective := fun f : expIntegrableRealFunctions ν =>
      if Integrable (f : α → ℝ) μ
        then ENNReal.ofReal (∫ x, (f : α → ℝ) x ∂μ - log (∫ x, exp ((f : α → ℝ) x) ∂ν))
        else ∞

  apply le_antisymm
  -- Prove that the supremum is attainable.
  · -- If ¬ μ ≪ ν, then we can make f large on a set that has nonzero wrt μ
    -- but is a null set wrt ν to show that the supremum is ∞.
    by_cases hμν : μ ≪ ν; swap;
    · have hsup_infinite : ⨆ f : expIntegrableRealFunctions ν, objective f = ∞ := by
        rw [iSup_eq_top]
        intro b hb
        obtain ⟨f, hf⟩ := donsker_varadhan_not_absCont_infinite_sup hμν (b + 1)
          (add_lt_top.mpr ⟨hb, one_lt_top⟩)
        use f
        exact lt_of_lt_of_le (ENNReal.lt_add_right (lt_top_iff_ne_top.mp hb) one_ne_zero) hf

      rw [hsup_infinite]
      exact le_top

    -- Otherwise, we just need to exhibit f such that objective f ≥ the KL divergence
    suffices ∃ f : expIntegrableRealFunctions ν, klDiv μ ν ≤ objective f by
      obtain ⟨f, hf⟩ := this
      exact le_iSup_of_le f hf

    -- We'll take f = log (dμ / dν)
    let f := llr μ ν
    have hf_exp_ν_integrable : Integrable (exp ∘ f) ν := by
      sorry

    use ⟨f, ⟨measurable_llr μ ν, hf_exp_ν_integrable⟩⟩

    -- If f is not integrable wrt μ, the RHS is ∞ (in fact, both sides are).
    by_cases hfμ_integrable : Integrable f μ; swap;
    · unfold objective
      rw [if_neg hfμ_integrable]
      exact le_top

    sorry

  · sorry
    -- by_cases μ ≪ ν ∧ Integrable f μ
    -- case pos hkl_finite =>
    --   rw [if_pos hkl_finite.2]
    --   sorry
      -- have h_rhs : ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν))
        -- = klDiv μ ν := by
        -- calc
        --   ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν))
        --     = ENNReal.ofReal (∫ x, llr μ ν x ∂μ - log (∫ x, (μ.rnDeriv ν x).toReal ∂ν)) := by
        --       simp only [f, llr, exp_log]

        --   _ =

    -- case neg hkl_infinite =>
    --   push_neg at hkl_infinite
    --   by_cases habsCont : μ ≪ ν
    --   · have hf_μ_nonintegrable := hkl_infinite habsCont

    --   .

  -- Prove that for any f, the expression inside the supremum ≤ the KL divergence.
  -- · apply iSup_le
  --   intro f
  --   let g := (f : α → ℝ)

  --   by_cases habs_cont : μ ≪ ν
  --   -- We can assume μ ≪ ν, since otherwise the inequality is trivially true.
  --   · let ν_tilted := ν.tilted g

      -- let dμν := rnDeriv μ ν
      -- let dv_tiltedν := rnDeriv ν ν_tilted

      -- have hν_tilted_absCont := tilted_absolutelyContinuous ν g

      -- have hg_measurable : Measurable g := f.2.1
      -- have hg_aemeasurable : AEMeasurable g ν := hg_measurable.aemeasurable (μ := ν)


      -- have h : ENNReal.ofReal ∘ exp ∘ g = ν_tilted.rnDeriv ν := by
      --   rw [← rnDeriv_tilted_left ν hg_aemeasurable]



      -- calc
      --  ∫ x, (f : α → ℝ) x ∂μ - log (∫ x, exp ((f : α → ℝ) x) ∂ν)

    --   sorry

    -- · rw [klDiv_of_not_ac habs_cont]
    --   exact le_top


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
