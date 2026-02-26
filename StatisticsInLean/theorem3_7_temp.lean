import Mathlib

universe u v u_1 u_2


open TopologicalSpace Filter MeasureTheory
open scoped NNReal ENNReal MeasureTheory Topology
namespace MeasureTheory
lemma univ_tendsto_one {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] {l : Filter ι} :
    Tendsto (fun (_ : ι) => p (Set.univ)) l (nhds 1) :=by
  simp only [MeasureTheory.measure_univ]
  exact tendsto_const_nhds
end MeasureTheory

open Filter MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal MeasureTheory Topology

def TendstoInProbability {Ω : Type u_1} [MeasurableSpace Ω] (θ : ℕ → Ω → ℝ)
    (P : Measure Ω) (θ₀ : ℝ):= TendstoInMeasure P θ atTop (fun _ => θ₀)

noncomputable def Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → ENNReal :=
  fun ω => ∏ i : Fin n, pdf (X 0) (f θ) μ (X i ω)

noncomputable def log_Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → EReal :=
  fun ω => ∑ (i : Fin n), ENNReal.log (pdf (X 0) (f θ) μ (X i ω))


-- theorem temp
--     {Ω : Type*} [MeasurableSpace Ω] {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
--     (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) (ω : Ω)
--     (a : ENNReal) (ha : 0 < a)
--     (h1: log_Likelihood f X θ₀ n μ ω > log_Likelihood f X (θ₀ + a.toReal) n μ ω)
--     (h2: log_Likelihood f X θ₀ n μ ω > log_Likelihood f X (θ₀ - a.toReal) n μ ω):
--   ∃ (θ : ℝ), edist θ θ₀ < a ∧ θ ∈ root_of_deriv (fun x => log_Likelihood f X x n μ ω) :=by
--   unfold root_of_deriv
--   simp only [Set.mem_setOf_eq]


lemma exists_IsMaxOn_strict_endpoints
    (g : ℝ → ℝ) (θ₀ : ℝ) (a : ℝ≥0∞)
    (ha : 0 < a) (ha_fin : a < ⊤)
    (hcont : ContinuousOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (h1 : g θ₀ > g (θ₀ + a.toReal))
    (h2 : g θ₀ > g (θ₀ - a.toReal)) :
    ∃ θ, edist θ θ₀ < a ∧ (IsMaxOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)) θ) := by

  set L : ℝ := θ₀ - a.toReal
  set U : ℝ := θ₀ + a.toReal

  have ha_Real := ENNReal.toReal_pos_iff.mpr ⟨ha, ha_fin⟩

  have hLU : L ≤ U := by
    dsimp [L, U]
    nlinarith

  have hne : (Set.Icc L U).Nonempty := by
    exact Set.nonempty_Icc.2 hLU

  obtain ⟨θ, hθIcc, hθmax'⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc L U)).exists_isMaxOn hne (by
      simpa [L, U] using hcont)

  have hθ_ge_θ0 : g θ ≥ g θ₀ := by
    have : g θ₀ ≤ g θ := by
      have hθ0Icc : θ₀ ∈ Set.Icc L U := by
        have hL : L ≤ θ₀ := by dsimp [L]; nlinarith
        have hU : θ₀ ≤ U := by dsimp [U]; nlinarith
        exact ⟨hL, hU⟩
      exact hθmax' hθ0Icc
    exact this

  have hθ_ne_U : θ ≠ U := by
    intro hEq
    have : g θ₀ ≤ g θ :=by exact hθ_ge_θ0
    have hU_le : g U ≤ g θ := hθmax' ⟨hLU, le_rfl⟩
    have : g θ₀ > g θ := by simpa [hEq, U] using h1
    refine (not_lt_of_ge (le_trans hθ_ge_θ0 (hθmax' hθIcc))).elim (by
      exact this)

  have hθ_ne_L : θ ≠ L := by
    intro hEq
    have hLIcc : L ∈ Set.Icc L U := by exact ⟨le_rfl, hLU⟩
    have hL_le : g L ≤ g θ := by
      exact hθmax' hLIcc
    have : g θ₀ ≤ g θ :=by
      refine le_trans (le_of_lt (lt_imp_lt_of_le_imp_le (fun a ↦ hθ_ge_θ0)
        (by simpa [hEq, L] using h2))) hL_le
    refine (not_lt_of_ge this) (by simpa [hEq, L] using h2)

  have hθIoo : θ ∈ Set.Ioo L U := by
    exact ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθ_ne_L), lt_of_le_of_ne hθIcc.2 hθ_ne_U⟩

  use θ
  simp only [edist_dist]
  rw [ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg (LT.lt.ne_top ha_fin)]

  refine ⟨?_, hθmax'⟩
  have h1' : θ₀ - a.toReal < θ := by simpa [L] using hθIoo.1
  have h2' : θ < θ₀ + a.toReal := by simpa [U] using hθIoo.2
  rw [Real.dist_eq]
  simp only [abs_lt]
  refine ⟨by linarith, by linarith⟩

open scoped BigOperators
open Finset

lemma EReal.toReal_lt_toReal
    {a : EReal} {b : EReal}
    (ha1 : a ≠ ⊥) (ha2 : a ≠ ⊤) (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) :
    a < b → a.toReal < b.toReal :=by
  intro h
  have hne: a.toReal ≠ b.toReal := by
    simp only [ne_eq]
    refine Ne.intro ?_
    intro h_eq_toReal
    rw [EReal.toReal_eq_toReal ha2 ha1 hb1 hb2] at h_eq_toReal
    exact ne_of_lt h h_eq_toReal
  exact lt_of_le_of_ne (EReal.toReal_le_toReal (le_of_lt h) ha1 hb1) hne

open scoped Topology
open Filter

lemma tendsto_measure_inter_of_tendsto_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s t : ℕ → Set Ω)
    (hs : Tendsto (fun n => P (s n)) atTop (𝓝 (1 : ℝ≥0∞)))
    (ht : Tendsto (fun n => P (t n)) atTop (𝓝 (1 : ℝ≥0∞)))
    (hms : ∀ n, MeasurableSet (s n))
    (hmt : ∀ n, MeasurableSet (t n)) :
    Tendsto (fun n => P (s n ∩ t n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
  -- We use order characterization of tendsto to 1 in ℝ≥0∞.
  refine tendsto_order.2 ?_
  constructor
  · -- show: ∀ a < 1, eventually a < P(s n ∩ t n)
    intro a ha
    -- pick a positive ε so that a < 1 - 2ε
    -- easiest is to take ε = (1 - a) / 4
    have hpos : 0 < (1 : ℝ≥0∞) - a := by
      -- in a linear order with `tsub`, `a < 1` implies `0 < 1 - a`
      simpa [tsub_pos_iff_lt] using ha
    let ε : ℝ≥0∞ := ((1 : ℝ≥0∞) - a) / 4
    have hεpos : 0 < ε := by
      simp only [ε]
      refine ENNReal.div_pos (Ne.symm (ne_of_lt hpos)) (Ne.symm ENNReal.top_ne_ofNat)
    have hε_lt : a < (1 : ℝ≥0∞) - (ε + ε) := by
      -- arithmetic: ε+ε = (1-a)/2, so RHS = 1 - (1-a)/2 = (1+a)/2 > a
      -- This is the only “algebra” step; the simp lemma below works well in mathlib.
      -- If it doesn’t in your environment, tell me the exact error and I’ll rewrite it.
      have : ε + ε = ((1 : ℝ≥0∞) - a) / 2 := by
        unfold ε
        rw [ENNReal.div_add_div_same]
        rw [← two_mul]
        rw [div_eq_mul_inv]
        rw [mul_assoc, mul_comm, mul_assoc]
        have h4_2 : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ :=by
          refine ENNReal.eq_inv_of_mul_eq_one_left ?_
          rw [mul_assoc]
          norm_num
          refine ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 4)) (Ne.symm ENNReal.top_ne_ofNat)

        rw [h4_2]
        rw [div_eq_mul_inv]
      -- now rewrite and finish with `by nlinarith` on `toReal` if needed
      -- (ENNReal arithmetic is easiest via `toReal` because everything is finite here.)
      -- We'll do a short toReal-based proof:
      have ha_fin : a < ⊤ := lt_of_lt_of_le ha (by simp)  -- since a < 1 ≤ ⊤
      have hε_fin : ε < ⊤ := by
        refine ENNReal.div_lt_top (ENNReal.sub_ne_top ENNReal.one_ne_top) (Ne.symm (NeZero.ne' 4))
      -- convert inequality to ℝ
      -- Note: `toReal` is monotone on finite values.
      have : a.toReal < ((1 : ℝ≥0∞) - (ε + ε)).toReal := by
        rw [this]
        have ha1: 1 - a ≤ 1 := by
          exact tsub_le_self
        have hεle1 : (ε + ε) ≤ 1 :=by
          rw [this]
          refine (ENNReal.div_le_iff (Ne.symm (NeZero.ne' 2)) (Ne.symm ENNReal.top_ne_ofNat)).mpr ?_
          simp only [one_mul]
          exact Std.IsPreorder.le_trans (1 - a) 1 2 tsub_le_self one_le_two

        have ha_fin' : a < (⊤ : ℝ≥0∞) := lt_of_lt_of_le ha (by simp only [le_top])
        have ha_fin : a ≠ (⊤ : ℝ≥0∞) := by exact LT.lt.ne_top (ha_fin')
        have hR_a : a.toReal < (1 : ℝ) := by
          -- `toReal` is strictly monotone on finite values
          -- (this lemma name is standard; if it doesn't resolve, tell me your imports)
          have := ENNReal.toReal_lt_toReal ha_fin ENNReal.one_ne_top
          simp only [ENNReal.toReal_one] at this
          rw [this]
          exact ha

        have hR_rhs :
            ((1 : ℝ≥0∞) - (ε + ε)).toReal = (1 : ℝ) - (ε + ε).toReal := by
          simpa using (ENNReal.toReal_sub_of_le hεle1)
        have hR_eps :
            (ε + ε).toReal = (((1 : ℝ≥0∞) - a) / 2).toReal := by
          rw [this]
        have hR_div :
            (((1 : ℝ≥0∞) - a) / 2).toReal = ((1 : ℝ) - a.toReal) / 2 := by
          -- uses `toReal_sub_of_le` with `a ≤ 1` and `toReal_div`
          -- The exact simp lemma set depends on imports; this is the standard pattern:
          have ha_le1 : a ≤ (1 : ℝ≥0∞) := le_of_lt ha
          -- first: toReal(1 - a) = 1 - a.toReal
          simp only [div_eq_mul_inv]  -- may need `ENNReal.toReal_mul` lemmas
          rw [ENNReal.toReal_mul]
          simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, mul_eq_mul_right_iff, inv_eq_zero,
            OfNat.ofNat_ne_zero, or_false]
          rw [ENNReal.toReal_sub_of_le ha_le1 ENNReal.one_ne_top]
          simp only [ENNReal.toReal_one]
        have hR_sub: (1 - (1 - a) / 2).toReal = (1: ENNReal).toReal - ((1 - a) / 2).toReal:=by
          refine ENNReal.toReal_sub_of_le ?_ ENNReal.one_ne_top
          rw [this] at hεle1
          exact hεle1
        rw [hR_sub]
        simp [hR_div]
        -- now it's a real inequality
        nlinarith [hR_a]
      rw [ENNReal.toReal_lt_toReal (LT.lt.ne_top ha)] at this
      · exact this
      · simp only [ne_eq, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top, ENNReal.add_eq_top, or_self,
        false_and, not_false_eq_true]


    -- From hs/ht, eventually P(s n) > 1 - ε and P(t n) > 1 - ε
    have hs' : ∀ᶠ n in atTop, (1 : ℝ≥0∞) - ε < P (s n) := by
      rw [tendsto_order] at hs
      exact (hs.1 (1 - ε))
        ((ENNReal.sub_lt_self_iff ENNReal.one_ne_top).mpr ⟨zero_lt_one' ℝ≥0∞, hεpos⟩)
    have ht' : ∀ᶠ n in atTop, (1 : ℝ≥0∞) - ε < P (t n) := by
      rw [tendsto_order] at ht
      exact (ht.1 (1 - ε))
        ((ENNReal.sub_lt_self_iff ENNReal.one_ne_top).mpr ⟨zero_lt_one' ℝ≥0∞, hεpos⟩)
    -- Now show eventually: a < P(s n ∩ t n)
    filter_upwards [hs', ht'] with n hs1 ht1
    -- bound complement via union, then subtract from 1
    have hcomplS : P ((s n)ᶜ) < ε := by
      -- P(sᶜ) = 1 - P(s) (probability measure)
      have hcompl : P ((s n)ᶜ) = (1 : ℝ≥0∞) - P (s n) := by
        simpa [measure_univ] using (prob_compl_eq_one_sub (hms n))
      -- from (1-ε) < P(s) we get (1-P(s)) < ε
      -- rearrangement in `ℝ≥0∞` is easiest via `tsub_lt_iff_right`
      -- or direct `by simpa [hcompl]` using ...

      simpa [hcompl] using (ENNReal.sub_lt_of_sub_lt (prob_le_one)
        (by left; exact ENNReal.one_ne_top) hs1)
    have hcomplT : P ((t n)ᶜ) < ε := by
      have hcompl : P ((t n)ᶜ) = (1 : ℝ≥0∞) - P (t n) := by
        simpa [measure_univ] using (prob_compl_eq_one_sub (hmt n))
      simpa [hcompl] using (ENNReal.sub_lt_of_sub_lt (prob_le_one)
        (by left; exact ENNReal.one_ne_top) ht1)

    -- Use De Morgan: (s∩t)ᶜ = sᶜ ∪ tᶜ
    have hcompl_inter :
        P ((s n ∩ t n)ᶜ) ≤ P ((s n)ᶜ) + P ((t n)ᶜ) := by
      -- measure of union ≤ sum
      -- and rewrite compl inter as union of compls\
      simpa [Set.compl_inter] using (measure_union_le ((s n)ᶜ) ((t n)ᶜ))

    -- Convert to a lower bound on P(s∩t) via complement formula
    have hinter :
         P (s n ∩ t n) = (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ):= by
      have h:= prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n)ᶜ)
        (MeasurableSet.compl_iff.mpr (MeasurableSet.inter (hms n) (hmt n)))
      simp only [compl_compl] at h
      exact h

    -- Now finish: P(s∩t) > 1 - (ε+ε) > a
    have : (1 : ℝ≥0∞) - (ε + ε) < P (s n ∩ t n) := by
      -- from P(complement) ≤ P(sᶜ)+P(tᶜ) < ε+ε
      have hlt : P ((s n ∩ t n)ᶜ) < ε + ε := by
        have hsum : P ((s n)ᶜ) + P ((t n)ᶜ) < ε + ε :=by
          exact ENNReal.add_lt_add hcomplS hcomplT
        exact lt_of_le_of_lt hcompl_inter hsum
      -- rewrite using `hinter`
      -- (1 - P(complement)) > (1 - (ε+ε))
      -- monotonicity of `tsub` in the second argument
      -- have hprob: P (s n ∩ t n)ᶜ = 1 - P (s n ∩ t n) := by
      --   exact prob_compl_eq_one_sub (MeasurableSet.inter (hms n) (hmt n))
      have : (1 : ℝ≥0∞) - (ε + ε) < (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ) := by
        -- Use ENNReal.sub_lt_of_sub_lt with:
        --   a := 1, b := (1 - P((s∩t)ᶜ)), c := (ε+ε)
        -- and h₁ := (1 - (1 - P((s∩t)ᶜ))) < ε+ε, which is `P((s∩t)ᶜ) < ε+ε`.
        have h₂ : (ε + ε) ≤ (1 : ℝ≥0∞) := by
          -- easiest: since `hlt` implies `P((s∩t)ᶜ) < 1`, hence `ε+ε ≤ 1` is not automatic,
          -- but in your construction ε=(1-a)/4 with a<1, so ε+ε ≤ 1. Use your existing lemma if you have it.
          -- If you already have `(ε+ε) < 1` earlier, replace with `le_of_lt`.
          -- Here I'll use the fact `ε ≤ 1/4` (derivable) ... but you likely already have `h₂` in your file.
          -- Put your earlier proof here:
          have : (ε + ε) < (1 : ℝ≥0∞) := by
            -- from `hε_lt : a < 1 - (ε+ε)` implies `ε+ε < 1`
            have : 0 < (1 : ℝ≥0∞) - (ε + ε) := by
              have ha0 : (0 : ℝ≥0∞) ≤ a := bot_le
              refine lt_of_le_of_lt ha0 hε_lt
            simpa [tsub_pos_iff_lt] using this
          exact le_of_lt this
        have h₃ : (1 : ℝ≥0∞) ≠ ⊤ ∨ (1 - P ((s n ∩ t n)ᶜ)) ≠ ⊤ := by
          left; simp
        have h₁ : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) < ε + ε := by
          -- simplify LHS: 1 - (1 - x) = x when x ≤ 1 (true for probabilities)
          -- We'll use `measure_le_one` to get x ≤ 1, and then `tsub_tsub_cancel_of_le`.
          have hxle : P ((s n ∩ t n)ᶜ) ≤ (1 : ℝ≥0∞) := by
            -- probability measure bound
            exact prob_le_one
          -- rewrite 1 - (1 - x) = x using `tsub_tsub_cancel_of_le`
          -- lemma: `tsub_tsub_cancel_of_le` works in `ENNReal`
          have : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) = P ((s n ∩ t n)ᶜ) := by
            rw [← hinter]
            exact id (Eq.symm (prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n))
              (MeasurableSet.inter (hms n) (hmt n))))
          -- now finish with hlt
          simpa [this] using hlt

        -- apply lemma
        -- h₁ : 1 - (1 - x) < ε+ε  ==> 1 - (ε+ε) < 1 - x
        exact ENNReal.sub_lt_of_sub_lt h₂ h₃ h₁
      simpa [hinter] using this

    exact lt_trans hε_lt this
  · -- show: ∀ b > 1, eventually P(s n ∩ t n) < b
    intro b hb
    rw [@eventually_atTop]
    use 0
    intro n _
    exact lt_of_le_of_lt (prob_le_one (μ := P) (s := s n ∩ t n)) hb


lemma Measurable_log_Likelihood
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (k : ℕ) :
    Measurable
    (fun ω : Ω => log_Likelihood f X θ₀ k μ ω) := by sorry


theorem exists_consistent_estimator_of_logLikelihood
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (f : ℝ → ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
  [IsProbabilityMeasure (f θ₀).1]
  (a : ENNReal) (ha : 0 < a) (ha_fin : a < ⊤)
  (hfs : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), log_Likelihood f X θ n μ ω ≠ ⊤)
  (hfl : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), ⊥ ≠ log_Likelihood f X θ n μ ω)
  (hcont : ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
    (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
  (htendsto : ∀ (θ : ℝ), Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
    log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1))
  (hfinite :
    ∀ (k : ℕ) (ω : Ω) (θ : ℝ),
      θ ∈ Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal) →
        log_Likelihood f X θ k μ ω ≠ ⊥ ∧ log_Likelihood f X θ k μ ω ≠ ⊤) :
  ∃ (θ_hat : ℕ → Ω → ℝ),
    Tendsto (fun i =>
      (f θ₀).1 { ω |
        (edist (θ_hat i ω) θ₀ < a) ∧
        (IsMaxOn (fun θ => (log_Likelihood f X θ i μ ω).toReal)
        (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)) (θ_hat i ω))})
      atTop (𝓝 1) := by

  set θU : ℝ := θ₀ + a.toReal
  set θL : ℝ := θ₀ - a.toReal

  let AU : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θU k μ ω}
  let AL : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θL k μ ω}
  let A : ℕ → Set Ω := fun k => AU k ∩ AL k

  set P := (f θ₀).1
  have hAU : Tendsto (fun k => P (AU k)) atTop (𝓝 1) := by
    simpa [P, θU, AU] using htendsto θU
  have hAL : Tendsto (fun k => P (AL k)) atTop (𝓝 1) := by
    simpa [P, θL, AL] using htendsto θL

  have hA : Tendsto (fun k => P (A k)) atTop (𝓝 1) := by
    unfold A
    have hmsU : ∀ k, MeasurableSet (AU k) := by
      intro k
      simpa [AU, gt_iff_lt] using
        (measurableSet_lt (Measurable_log_Likelihood f μ X θU k)
          (Measurable_log_Likelihood f μ X θ₀ k))
    have hmsL : ∀ k, MeasurableSet (AL k) := by
      intro k
      simpa [AL, gt_iff_lt] using
        (measurableSet_lt (Measurable_log_Likelihood f μ X θL k)
          (Measurable_log_Likelihood f μ X θ₀ k))
    simpa [A] using
      (tendsto_measure_inter_of_tendsto_measure (P := P) (s := AU) (t := AL)
        hAU hAL hmsU hmsL)

  set I : Set ℝ := Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)

  have hcontR :
      ∀ (k : ℕ) (ω : Ω),
        ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := by
    intro k ω
    have h' : Set.MapsTo (fun θ ↦ log_Likelihood f X θ k μ ω) I {⊥, ⊤}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact hfinite k ω x hx
    exact (ContinuousOn.comp EReal.continuousOn_toReal (hcont k ω)) h'

  let θ_hat := (fun k ω =>
      if h : (ω ∈ AU k) ∧ (ω ∈ AL k) then
        Classical.choose
          (exists_IsMaxOn_strict_endpoints
            (g := fun θ => (log_Likelihood f X θ k μ ω).toReal)
            (θ₀ := θ₀) (a := a)
            ha ha_fin
            (by
              have : ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := hcontR k ω
              simpa [I] using this)
            (by
              have : (log_Likelihood f X (θ₀ + a.toReal) k μ ω).toReal
                  < (log_Likelihood f X θ₀ k μ ω).toReal := by
                exact EReal.toReal_lt_toReal
                  (fun a_1 ↦ hfl k (θ₀ + a.toReal) ω (id (Eq.symm a_1)))
                  (hfs k (θ₀ + a.toReal) ω)
                  (hfs k θ₀ ω)
                  (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
                  (by simpa [AU, θU] using h.1)
              simpa [θU] using this)
            (by
              have : (log_Likelihood f X (θ₀ - a.toReal) k μ ω).toReal
                  < (log_Likelihood f X θ₀ k μ ω).toReal := by
                exact EReal.toReal_lt_toReal
                  (fun a_1 ↦ hfl k (θ₀ - a.toReal) ω (id (Eq.symm a_1)))
                  (hfs k (θ₀ - a.toReal) ω)
                  (hfs k θ₀ ω)
                  (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
                  (by simpa [AL, θL] using h.2)
              simpa [θL] using this))
      else θ₀)

  use θ_hat

  let T : ℕ → Set Ω := fun i =>
    {ω | edist (θ_hat i ω) θ₀ < a
    ∧ IsMaxOn (fun θ ↦ (log_Likelihood f X θ i μ ω).toReal) I (θ_hat i ω)}

  have hsubset : ∀ k, A k ⊆ T k := by
    intro k ω hω
    have h : ω ∈ AU k ∧ ω ∈ AL k := by simpa [A] using hω
    simp only [T, θ_hat, Set.mem_setOf_eq, h]
    simp only [and_self, ↓reduceDIte]
    set hs :=
      (Classical.choose_spec
        (exists_IsMaxOn_strict_endpoints
          (g := fun θ => (log_Likelihood f X θ k μ ω).toReal)
          (θ₀ := θ₀) (a := a)
          ha ha_fin
          (by
            have : ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := hcontR k ω
            simpa [I] using this)
          (by
            exact EReal.toReal_lt_toReal
              (fun a_1 ↦ hfl k (θ₀ + a.toReal) ω (id (Eq.symm a_1)))
              (hfs k (θ₀ + a.toReal) ω) (hfs k θ₀ ω)
              (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
              (by simpa [AU, θU] using h.1))
          (by
            exact EReal.toReal_lt_toReal
              (fun a_1 ↦ hfl k (θ₀ - a.toReal) ω (id (Eq.symm a_1)))
              (hfs k (θ₀ - a.toReal) ω) (hfs k θ₀ ω)
              (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
              (by simpa [AL, θL] using h.2))))
    have h1 := hs.1
    refine ⟨hs.1, hs.2⟩

  have hmono : ∀ k, P (A k) ≤ P (T k) := by
    intro k
    exact measure_mono (hsubset k)

  have : Tendsto (fun k => P (T k)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hA (univ_tendsto_one P) (fun k => hmono k)
      (fun k => by simpa using (prob_le_one (μ := P) (s := T k)))

  simpa [P, T] using this




theorem exists_tendstoInProbability_of_prob_tendsto_zero {Ω : Type u_1} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (θ₀ : ℝ)
    (h : ∀ (a : ENNReal), 0 < a → ∃ (θ : ℕ → Ω → ℝ),
    Tendsto (fun i => P { ω | a ≤ edist (θ i ω) θ₀}) atTop (𝓝 0)) :
    ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (ε : ℝ≥0∞), 0 < ε →
      Tendsto (fun i ↦ P {x | ε ≤ edist (θ_hat i x) θ₀}) atTop (𝓝 0):= by
  -- pick a_n = 1/(n+1)
  let a : ℕ → ENNReal := fun n => ( (n+1 : ENNReal) )⁻¹
  have a_pos : ∀ n, 0 < a n := by
    intro n
    simp [a]  -- (n+1:ENNReal) ≠ 0, so its inverse is > 0
  have hex : ∀ n, ∃ θ : ℕ → Ω → ℝ,
      Tendsto (fun i => P {ω | a n ≤ edist (θ i ω) θ₀}) atTop (𝓝 0) := by
    intro n
    exact h (a n) (a_pos n)

  choose θseq hθseq using hex

  simp_rw [@ENNReal.tendsto_atTop_zero] at hθseq


  have hθseq': ∀ (n : ℕ), ∃ N, P
    {ω | a n ≤ edist (θseq n N ω) θ₀} ≤ ENNReal.ofReal (((2:ℝ)⁻¹)^n):=by
    intro n
    obtain ⟨N, hN⟩ := (fun n => hθseq n (ENNReal.ofReal (((2:ℝ)⁻¹)^n))
      (by simp only [inv_pow, Nat.ofNat_pos,
      pow_pos, ENNReal.ofReal_inv_of_pos, Nat.ofNat_nonneg, ENNReal.ofReal_pow,
      ENNReal.ofReal_ofNat, gt_iff_lt, ENNReal.inv_pos, ne_eq, ENNReal.pow_eq_top_iff,
      ENNReal.ofNat_ne_top, false_and, not_false_eq_true])) n
    specialize hN N (by simp only [ge_iff_le, le_refl])
    use N

  choose f hanθP using hθseq'


  let θ_hat : ℕ → Ω → ℝ := fun n => fun ω => θseq n (f n) ω
  use θ_hat
  intro b hb
  rw [@ENNReal.tendsto_atTop_zero]
  intro ε hε

  obtain ⟨N₁, hN₁, hN₁_pow⟩ : ∃ N₁ > 0, ENNReal.ofReal (((2:ℝ)⁻¹)^N₁) < ε :=by
    by_cases htop : ε = ∞
    · use 1
      rw [htop]
      simp only [gt_iff_lt, zero_lt_one, pow_one, Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos,
        ENNReal.ofReal_ofNat, true_and, ENNReal.inv_lt_top, Nat.ofNat_pos]
    · by_cases h1: ε.toReal < 1
      · have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
          change 0 < ε at hε
          refine (ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg (a := 0)) htop).mp ?_
          simp only [ENNReal.toReal_zero, ENNReal.ofReal_zero]
          exact hε
        have hhalf0 : (0 : ℝ) < (2 : ℝ)⁻¹ := by nlinarith
        have hhalf1 : (2 : ℝ)⁻¹ < 1 := by nlinarith
        rcases exists_pow_lt_of_lt_one hε_toReal_pos hhalf1 with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have hleft_ne_top : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) ≠ ∞ := by
          simp only [inv_pow, Nat.ofNat_pos, pow_pos, ENNReal.ofReal_inv_of_pos, Nat.ofNat_nonneg,
            ENNReal.ofReal_pow, ENNReal.ofReal_ofNat, ne_eq, ENNReal.inv_eq_top, pow_eq_zero_iff',
            OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
        have hε_ne_top : ε ≠ ∞ := htop
        have h_toReal :
            (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n)).toReal < ε.toReal := by
          simpa using hn
        by_cases hn0: n > 0
        · refine ⟨ hn0, (ENNReal.toReal_lt_toReal hleft_ne_top hε_ne_top).1 h_toReal⟩
        · have h0 : n = 0 := by exact Nat.eq_zero_of_not_pos hn0
          exfalso
          rw [h0] at hn
          simp only [pow_zero] at hn
          exact (lt_self_iff_false 1).mp (lt_trans hn h1)

      · use 1
        have h1' := Std.not_lt.mp h1
        rw [← propext (ENNReal.ofReal_le_iff_le_toReal htop)] at h1'
        simp only [ENNReal.ofReal_one] at h1'
        simp only [Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat, pow_one,
          gt_iff_lt]
        have h: (2: ENNReal)⁻¹ < 1 := by exact ENNReal.one_half_lt_one
        simp only [zero_lt_one, true_and, gt_iff_lt]
        exact Std.lt_of_lt_of_le h h1'
  have ⟨N₂, hN₂, hN₂_lt_b⟩  : ∃ N₂ > 0, a N₂ < b :=by
    unfold a
    simp only [gt_iff_lt]
    by_cases htop : b = ⊤
    · refine ⟨1, by decide, ?_⟩
      rw [htop]
      simp only [Nat.cast_one, ENNReal.inv_lt_top, pos_add_self_iff, zero_lt_one]
    · have hb_toReal : 0 < b.toReal := by
        simpa using ENNReal.toReal_pos hb.ne' htop
      rcases exists_nat_one_div_lt hb_toReal with ⟨n, hn⟩
      refine ⟨n + 1, Nat.succ_pos n, ?_⟩
      have : ((↑(n + 1) + 1 : ℝ≥0∞)⁻¹).toReal < b.toReal := by
        have hpos : (0 : ℝ) < (n + 1 : ℝ) := by
          exact_mod_cast (Nat.succ_pos n)
        have : (1 : ℝ) / (n + 2) < b.toReal := lt_trans (by simpa
          [one_div] using (one_div_lt_one_div_of_lt hpos (by linarith))) hn
        simp only [Nat.cast_add, Nat.cast_one, ENNReal.toReal_inv, gt_iff_lt]
        rw [add_assoc, one_add_one_eq_two]
        simpa using this

      exact (ENNReal.toReal_lt_toReal (by simp) htop).1 this
  let N := max N₁ N₂
  use N
  intro n hn
  have hn_lt_ε : ENNReal.ofReal (((2:ℝ)⁻¹)^n) < ε :=
    lt_of_le_of_lt (ENNReal.ofReal_mono (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (le_trans (le_max_left N₁ N₂) hn))) (by simpa using hN₁_pow)
  have hbset_aset: { ω | b ≤ edist (θ_hat n ω) θ₀} ⊆ { ω | a n ≤ edist (θ_hat n ω) θ₀} :=by
    simp only [Set.setOf_subset_setOf]
    intro ω hω
    have haNb : a n ≤ b := by
      have h_aN_le_aN2 : a n ≤ a N₂ :=by
        unfold a
        simp only [ENNReal.inv_le_inv]
        refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mpr ?_
        exact Nat.cast_le.mpr (le_trans (le_max_right N₁ N₂) hn)
      exact le_trans h_aN_le_aN2 (le_of_lt hN₂_lt_b)
    exact le_trans haNb (by simpa using hω)
  have hP_le: P {ω | b ≤ edist (θ_hat n ω) θ₀} ≤ P { ω | a n ≤ edist (θ_hat n ω) θ₀} := by
    exact OuterMeasureClass.measure_mono P hbset_aset
  exact le_of_lt (Std.lt_of_le_of_lt hP_le (lt_of_le_of_lt (hanθP n) hn_lt_ε))


theorem exists_tendstoInProbability_of_prob_tendsto_zero'
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (f : ℝ → ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
  [IsProbabilityMeasure (f θ₀).1]
  (hfs : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), log_Likelihood f X θ n μ ω ≠ ⊤)
  (hfl : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), ⊥ ≠ log_Likelihood f X θ n μ ω)
  (hcont : ∀ (a : ℝ≥0∞), ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
    (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
  (htendsto : ∀ (θ : ℝ), Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
    log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1))
  (hfinite :  ∀ (a : ℝ≥0∞),
    ∀ (k : ℕ) (ω : Ω) (θ : ℝ),
      θ ∈ Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal) →
        log_Likelihood f X θ k μ ω ≠ ⊥ ∧ log_Likelihood f X θ k μ ω ≠ ⊤):
  ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (a : ℝ≥0∞), (0 < a) ∧ (a < ⊤) →
      Tendsto (fun i ↦ (f θ₀).1 {ω |  edist (θ_hat i ω) θ₀ < a ∧
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0)}) atTop (𝓝 1) :=by
  sorry


def pdf_support {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E]
  {h : MeasurableSpace Ω} (X : Ω → E) (P : Measure Ω) (μ : Measure E := by volume_tac):=
  Function.support (pdf X P μ)

noncomputable abbrev log_sum_ratio_rv {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
  (μ : Measure ℝ := by volume_tac)
  (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) : ℕ → Ω → ℝ :=
  fun i => fun (ω : Ω) =>
    Real.log ((pdf (X 0) (f θ).1 μ (X i ω)).toReal/ (pdf (X 0) (f θ₀).1 μ (X i ω)).toReal)

theorem log_likelihood_consistency_sublevel_measure_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    [FunLike (↑ProbFunSet) (Set Ω) ℝ≥0∞]
    [OuterMeasureClass (↑ProbFunSet) Ω]
    (μ : Measure ℝ := by volume_tac)
    [IsFiniteMeasure μ]
    (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure (f θ₀).1] [IsProbabilityMeasure (f θ).1]
    [HasPDF (X 0) (↑(f θ)) μ] [HasPDF (X 0) (↑(f θ₀)) μ]
    (hX : ∀ (n : ℕ), ∀ (ω : Ω), ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ
      = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (pdf (X 0) ((f θ)) μ a).toReal)
    {S : Set ℝ} {hs1 : S ⊆ (Set.Iio 0)} {hs2 : Convex ℝ S}
    {hs3 : ContinuousOn Real.log S} {hs4 : IsClosed S}
    (hrv : ∀ (i : ℕ), Measurable (X i))
    (hindep : iIndepFun X ↑(f θ₀))
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) (f θ₀) (f θ₀))
    {hs5 : ∀ᵐ (x : Ω) ∂(f θ₀).1, (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∈ S}
    (hint1 : Integrable (Real.log ∘ fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hint2 : Integrable (fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hint0 : Integrable (log_sum_ratio_rv f μ X θ₀ θ 0) (f θ₀).1)
    (hne_const : ¬ ((fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) =ᶠ[ae (f θ₀).1]
  Function.const Ω
    (⨍ (x : Ω),
      (fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) x ∂↑(f θ₀))))
    :
    Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
      log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1)
 := by sorry


theorem theorem37
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
    [IsFiniteMeasure μ]
    (hcont : ∀ (a : ℝ≥0∞), ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
      (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (hIsProbabilityMeasure: ∀ (θ: ℝ), IsProbabilityMeasure (f θ).1)
    (hHasPDF: ∀ (θ : ℝ), HasPDF (X 0) (↑(f θ)) μ)
    (hX : ∀ (n : ℕ), ∀ (ω : Ω), ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (pdf (X 0) ((f θ)) μ a).toReal)
    {S : Set ℝ} {hs1 : S ⊆ (Set.Iio 0)} {hs2 : Convex ℝ S}
    {hs3 : ContinuousOn Real.log S} {hs4 : IsClosed S}
    (hrv : ∀ (i : ℕ), Measurable (X i))
    (hindep : iIndepFun X (f θ₀))
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) (f θ₀) (f θ₀))
    {hs5 : ∀ (θ: ℝ), ∀ᵐ (x : Ω) ∂(f θ₀).1, (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∈ S}
    (hint : ∀ (θ: ℝ), Integrable (fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hne_const : ∀ (θ: ℝ), ¬ ((fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) =ᶠ[ae (f θ₀).1]
  Function.const Ω
    (⨍ (x : Ω),
      (fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) x ∂↑(f θ₀))))
    :
    ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (a : ℝ≥0∞), (0 < a) ∧ (a < ⊤) →
      Tendsto (fun i ↦ (f θ₀).1 {ω |  edist (θ_hat i ω) θ₀ < a ∧
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0)}) atTop (𝓝 1)
 := by sorry

#check ConvexOn.map_integral_le
theorem theorem37'
    {α : Type u} {ProbFunSet : Set (PMF α)} {Ω : Type u_1} [MeasurableSpace Ω]
    (f : ℝ → ProbFunSet) (θ θ₀ : ℝ) (ω : Set ℝ) (hω : IsOpen ω) (h3 : θ₀ ∈ ω) (x_set : Finset α)
    (x_set_fun : ℕ → α) (P : ProbabilityMeasure Ω) :  ∃ (θ: ℕ → Ω → ℝ),
    ∀ (n : ℕ), deriv g (θ n)  = 0
    ∧ TendstoInProbability θ P θ₀:= by
  rw [Metric.isOpen_iff] at hω
  obtain ⟨a, ha, hω⟩ := hω θ₀ h3
  sorry
