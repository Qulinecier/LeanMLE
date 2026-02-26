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

lemma tendsto_measure_compl_iff {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p]
    {l : Filter ι} {s : ι → Set Ω}
    (hs : ∀ i, MeasurableSet (s i)) :
  (Tendsto (fun i => p (s i)) l (nhds 0))
  ↔ (Tendsto (fun i => p ((s i)ᶜ)) l (nhds 1)):=by
  have hcompl: ∀ (i: ι), p (Set.univ) - p (s i) = p (s i)ᶜ :=by
    intro i
    rw [← MeasureTheory.measure_compl]
    · exact hs i
    · exact MeasureTheory.measure_ne_top p (s i)
  constructor
  · intro h
    have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
      (by left; exact ENNReal.one_ne_top)
    simp_rw [hcompl, tsub_zero] at hsub
    exact hsub
  · intro h
    have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
      (by left; exact ENNReal.one_ne_top)
    simp_rw [fun (i: ι) => (hcompl i).symm, MeasureTheory.measure_univ, tsub_self] at hsub
    have hone_sub_p: ∀ (i: ι), 1 - (1 - p (s i)) = p (s i) := by
      intro i
      refine ENNReal.sub_sub_cancel ENNReal.one_ne_top MeasureTheory.prob_le_one
    simp_rw [hone_sub_p] at hsub
    exact hsub
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


lemma exists_deriv_eq_zero_of_strict_endpoints
    (g : ℝ → ℝ) (θ₀ : ℝ) (a : ℝ≥0∞)
    (ha : 0 < a) (ha_fin : a < ⊤)
    (hcont : ContinuousOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (h1 : g θ₀ > g (θ₀ + a.toReal))
    (h2 : g θ₀ > g (θ₀ - a.toReal)) :
    ∃ θ, edist θ θ₀ < a ∧ deriv g θ = 0 := by

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


  have hed : edist θ θ₀ < a := by
    simp only [edist_dist]
    rw [ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg (LT.lt.ne_top ha_fin)]
    have : |θ - θ₀| < a.toReal := by
      have h1' : θ₀ - a.toReal < θ := by simpa [L] using hθIoo.1
      have h2' : θ < θ₀ + a.toReal := by simpa [U] using hθIoo.2
      have : -a.toReal < θ - θ₀ ∧ θ - θ₀ < a.toReal := by
        refine ⟨by linarith, by linarith⟩
      simpa [abs_lt] using this
    simpa [Real.dist_eq, abs_sub_comm] using this

  exact ⟨θ, hed, IsLocalMax.deriv_eq_zero (IsMaxOn.isLocalMax
    (fun y hy => hθmax' ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    (IsOpen.mem_nhds isOpen_Ioo hθIoo))⟩

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
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0) })
      atTop (𝓝 1) := by

  set θU : ℝ := θ₀ + a.toReal
  set θL : ℝ := θ₀ - a.toReal

  let AU : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θU k μ ω}
  let AL : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θL k μ ω}
  let A : ℕ → Set Ω := fun k => AU k ∩ AL k

  generalize hP : (f θ₀).1 = P at *
  have hAU : Tendsto (fun k => P (AU k)) atTop (𝓝 1) := by
    simpa [hP, θU, AU] using htendsto θU
  have hAL : Tendsto (fun k => P (AL k)) atTop (𝓝 1) := by
    simpa [hP, θL, AL] using htendsto θL

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
          (exists_deriv_eq_zero_of_strict_endpoints
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
  have h : ∀ (k: ℕ), ∀ (ω: Ω), ω ∈ A k → (ω ∈ AU k) ∧ (ω ∈ AL k) := by
    exact fun _ _ hω => ⟨Set.mem_of_mem_inter_left hω, Set.mem_of_mem_inter_right hω⟩


  let T : ℕ → Set Ω := fun k =>
    {ω : Ω |
      (edist (if h : (ω ∈ AU k) ∧ (ω ∈ AL k) then
        Classical.choose
          (exists_deriv_eq_zero_of_strict_endpoints
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
                (by simpa [AL, θL] using h.2)))
      else θ₀) θ₀ < a)
      ∧
      (deriv (fun θ => (log_Likelihood f X θ k μ ω).toReal)
        (if h : (ω ∈ AU k) ∧ (ω ∈ AL k) then
          Classical.choose
            (exists_deriv_eq_zero_of_strict_endpoints
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
                  (by simpa [AL, θL] using h.2)))
        else θ₀) = 0) }

  have hsubset : ∀ k, A k ⊆ T k := by
    intro k ω hω
    have h : (ω ∈ AU k) ∧ (ω ∈ AL k) := by simpa [A] using hω

    have hs :=
      (Classical.choose_spec
        (exists_deriv_eq_zero_of_strict_endpoints
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

    simpa [T, h] using And.intro hs.1 hs.2

  have hmono : ∀ k, P (A k) ≤ P (T k) := by
    intro k
    exact measure_mono (hsubset k)

  have : Tendsto (fun k => P (T k)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hA (univ_tendsto_one P) (fun k => hmono k)
      (fun k => by simpa using (prob_le_one (μ := P) (s := T k)))

  simpa [hP, T] using this



theorem theorem37
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
  let aN : ℕ → ℝ≥0∞ := fun n => ( (n+1 : ℝ≥0∞) )⁻¹
  have aN_pos : ∀ n, 0 < aN n := by
    intro n; simp [aN]
  have aN_fin : ∀ n, aN n < (⊤ : ℝ≥0∞) := by
    intro n; simpa [aN] using (ENNReal.inv_lt_top.2 (by simp))

  -- apply your fixed-a theorem to each aN n
  have hex :
      ∀ n, ∃ θ_hat : ℕ → Ω → ℝ,
        Tendsto (fun i =>
          (f θ₀).1 {ω |
            edist (θ_hat i ω) θ₀ < aN n ∧
            deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0 })
          atTop (𝓝 1) := by
    intro n
    -- this is exactly your already proved theorem, instantiated at `a := aN n`
    -- you’ll need to pass `hcont` and `hfinite` specialized at `aN n`
    -- (since your `exists_consistent_estimator_of_logLikelihood` uses a fixed `a`)
    -- so you call it here
    simpa [aN] using
      (exists_consistent_estimator_of_logLikelihood
        (f := f) (X := X) (θ₀ := θ₀) (μ := μ)
        (a := aN n) (ha := aN_pos n) (ha_fin := aN_fin n)
        (hfs := hfs) (hfl := hfl)
        (hcont := fun i ω => hcont (aN n) i ω)
        (htendsto := htendsto)
        (hfinite := fun k ω θ hθ => hfinite (aN n) k ω θ hθ))

  choose θseq hθseq using hex
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (( (2:ℝ)⁻¹ )^n)

  have hδ_lt_one : ∀ n, (1:ℝ≥0∞) - δ n < 1 := by
    intro n
    simp only [δ]
    simp only [inv_pow, Nat.ofNat_pos, pow_pos, ENNReal.ofReal_inv_of_pos, Nat.ofNat_nonneg,
      ENNReal.ofReal_pow, ENNReal.ofReal_ofNat]
    apply ENNReal.sub_lt_self ENNReal.one_ne_top (Ne.symm (zero_ne_one' ℝ≥0∞))
    rw [ENNReal.inv_ne_zero, ENNReal.pow_ne_top_iff]
    left
    exact Ne.symm ENNReal.top_ne_ofNat

  -- define Good set
  let Good : ℕ → ℕ → Set Ω := fun n i =>
    {ω | edist (θseq n i ω) θ₀ < aN n ∧
        deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θseq n i ω) = 0 }

  -- Now choose N n using `Tendsto` + Ioi neighborhood
  have hN_exists : ∀ n, ∃ N0, ∀ i ≥ N0, (1 - δ n) < (f θ₀).1 (Good n i) := by
    intro n
    have hnhds : Set.Ioi ((1:ℝ≥0∞) - δ n) ∈ 𝓝 (1:ℝ≥0∞) :=
      Ioi_mem_nhds (hδ_lt_one n)
    have hev : ∀ᶠ i in atTop, (1 - δ n) < (f θ₀).1 (Good n i) :=
      (hθseq n).eventually hnhds
    rcases (Filter.eventually_atTop.1 hev) with ⟨N0, hN0⟩
    exact ⟨N0, by intro i hi; exact hN0 i hi⟩

  choose N hN using hN_exists
  -- N : ℕ → ℕ
  -- hN : ∀ n, ∀ i ≥ N n, (1 - δ n) < P (Good n i)
  -- pick a_n = 1/(n+1)
  let m : ℕ → ℕ := fun i => Nat.findGreatest (fun n => N n ≤ i) i
  let θ_hat : ℕ → Ω → ℝ := fun i ω => θseq (m i) i ω
  use θ_hat
  intro a ha
  simp_rw [@Set.setOf_and]
  set P := (f θ₀).1

  -- abbreviate your target set (it matches the intersection form in the goal)
  let Target : ℕ → Set Ω := fun i =>
    {ω | edist (θ_hat i ω) θ₀ < a ∧
        deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0}

  -- First rewrite goal into Target form
  have hTarget :
      (fun i =>
        P ({ω | edist (θ_hat i ω) θ₀ < a} ∩
          {ω | deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0}))
        =
      (fun i => P (Target i)) := by
    funext i
    simp only [Target]
    rw [@Set.setOf_and]
    -- ext ω
    -- simp [Target, and_left_comm, and_assoc, and_comm]

  -- It suffices to prove Tendsto (fun i => P (Target i)) → 1
  suffices hmain : Tendsto (fun i => P (Target i)) atTop (𝓝 (1:ℝ≥0∞)) by
    simpa [hTarget] using hmain

  -- 1) show: N (m i) ≤ i  (by property of findGreatest)
  -- helper: once we know `N 0 ≤ i`, then `N (m i) ≤ i` by findGreatest_spec
  have hm_spec_of_N0 : ∀ i, N 0 ≤ i → N (m i) ≤ i := by
    intro i hN0i
    -- `Nat.findGreatest_spec` in your version needs a witness `a ≤ i` and `N a ≤ i`
    -- take `a := 0`
    have h0le : (0 : ℕ) ≤ i := Nat.zero_le i
    -- unfold `m` so the conclusion matches
    simpa [m] using (Nat.findGreatest_spec (P:= fun n => N n ≤ i) (n := i) h0le hN0i)

  -- eventually, `N 0 ≤ i`
  have hN0_eventually : ∀ᶠ i in atTop, N 0 ≤ i := by
    -- standard "eventually_atTop": true for all i ≥ N 0
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N 0, ?_⟩
    intro i hi
    exact hi


    -- exact Nat.findGreatest_spec (p := fun n => N n ≤ i) (n := i)

  -- 2) show: m i → ∞ i.e. ∀ n, eventually n ≤ m i
  -- this is a standard lemma from findGreatest:
  -- if N n ≤ i then n ≤ findGreatest (fun k => N k ≤ i) i
  have hm_ge : ∀ n, ∀ᶠ i in atTop, n ≤ m i := by
    intro n

    -- Eventually, i ≥ max n (N n)
    have hlarge : ∀ᶠ i in atTop, max n (N n) ≤ i := by
      -- standard atTop fact
      exact (Filter.eventually_atTop.2 ⟨max n (N n), by intro i hi; exact hi⟩)

    filter_upwards [hlarge] with i hi

    have hnle : n ≤ i := le_trans (le_max_left _ _) hi
    have hNle : N n ≤ i := le_trans (le_max_right _ _) hi

    -- Now n is an admissible candidate, so findGreatest >= n
    -- Variant A (common name):
    -- exact Nat.le_findGreatest (p := fun k => N k ≤ i) hnle hNle
    --
    -- Variant B (sometimes the args are flipped / bundled):
    simpa [m] using (Nat.le_findGreatest (P := fun k => N k ≤ i) hnle hNle)


  -- 3) pick n0 such that aN n0 < a (this uses ha : 0 < a ∧ a < ∞)
  -- you already proved this kind of lemma earlier; reuse it.
  have hn0 : ∃ n0 : ℕ, aN n0 < a := by
    have ha_pos : 0 < a := ha.1
    have ha_fin : a < (⊤ : ℝ≥0∞) := ha.2
    -- move to real
    have ha_toReal_pos : 0 < a.toReal := by
      -- for ENNReal, positivity + finiteness gives positive toReal
      exact ENNReal.toReal_pos ha_pos.ne' ha_fin.ne

    -- choose n0 with 1/(n0+1) < a.toReal
    rcases exists_nat_one_div_lt ha_toReal_pos with ⟨n0, hn0⟩

    refine ⟨n0, ?_⟩

    rw [← ENNReal.toReal_lt_toReal (LT.lt.ne_top (aN_fin n0)) (LT.lt.ne_top ha_fin)]
    simp only [aN]
    suffices 1 / (↑n0 + 1) = ((↑n0 + 1)⁻¹: ENNReal).toReal by
      rw [← this]
      exact hn0
    simp only [one_div, ENNReal.toReal_inv, inv_inj]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n0) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]

  rcases hn0 with ⟨n0, hn0_lt⟩

  -- 4) show eventually aN (m i) ≤ a, using monotonicity of aN and hm_ge n0
  have haN_eventually : ∀ᶠ i in atTop, aN (m i) ≤ a := by
    filter_upwards [hm_ge n0] with i hmi
    have haN_m_le : aN (m i) ≤ aN n0 := by
      -- aN is decreasing: n0 ≤ m i → aN (m i) ≤ aN n0
      -- expand aN and use antitonicity of inv
      simp [aN]
      -- goal becomes: ((↑(m i) + 1 : ℝ≥0∞))⁻¹ ≤ ((↑n0 + 1 : ℝ≥0∞))⁻¹
      have hcast :
          ( (n0 + 1 : ℕ) : ℝ≥0∞) ≤ ( (m i + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.succ_le_succ hmi
      simpa using hcast
    exact le_trans haN_m_le (le_of_lt hn0_lt)

  -- 5) inclusion: Good (m i) i ⊆ Target i, once aN (m i) ≤ a
  have hGood_subset_Target : ∀ᶠ i in atTop, Good (m i) i ⊆ Target i := by
    filter_upwards [haN_eventually] with i haN_le
    intro ω hω
    -- hω : edist (θseq (m i) i ω) θ₀ < aN (m i) ∧ deriv ... = 0
    -- need: edist (...) < a ∧ deriv ... = 0
    refine ⟨lt_of_lt_of_le hω.1 haN_le, ?_⟩
    -- derivative part is identical after unfolding θ_hat
    simpa [θ_hat, Good, Target] using hω.2

  -- 6) monotonicity of measure gives P(Good (m i) i) ≤ P(Target i)
  have hmonoP : ∀ᶠ i in atTop, P (Good (m i) i) ≤ P (Target i) := by
    filter_upwards [hGood_subset_Target] with i hsub
    exact measure_mono hsub

  -- 7) lower bound: eventually 1 - δ (m i) < P (Good (m i) i)
  have hlower : ∀ᶠ i in atTop, (1 : ℝ≥0∞) - δ (m i) < P (Good (m i) i) := by
    -- apply hN at n := m i, i := i, using the eventual bound `N 0 ≤ i`
    filter_upwards [hN0_eventually] with i hN0i
    exact hN (m i) i (hm_spec_of_N0 i hN0i)

  -- combine 6) and 7): eventually 1 - δ (m i) < P(Target i)
  have hlower_target : ∀ᶠ i in atTop, (1 : ℝ≥0∞) - δ (m i) < P (Target i) := by
    filter_upwards [hlower, hmonoP] with i hlt hle
    exact lt_of_lt_of_le hlt hle

  have hm_tendsto_atTop : Tendsto m atTop atTop := by
    -- definition of `Tendsto f atTop atTop`
    refine tendsto_atTop.2 ?_
    intro n
    -- exactly your `hm_ge n`
    simpa using (hm_ge n)
  have hδ_rewrite : (fun n => δ n) = fun n => (ENNReal.ofReal ((2:ℝ)⁻¹)) ^ n := by
    funext n
    simp [δ, ENNReal.ofReal_pow]
    rw [@ENNReal.inv_pow]
  have hδ_tendsto0_nat : Tendsto (fun n => δ n) atTop (𝓝 (0:ℝ≥0∞)) := by
    -- show base < 1
    have hlt1 : ENNReal.ofReal ((2:ℝ)⁻¹) < (1:ℝ≥0∞) := by
      -- `simp` usually solves this
      -- (since (2:ℝ)⁻¹ = 1/2 < 1)
      simpa using (by
        -- ofReal preserves < on nonneg reals; simp knows 0 ≤ (2:ℝ)⁻¹
        -- so this usually becomes `(1/2:ℝ) < 1`
        have : ((2:ℝ)⁻¹) < (1:ℝ) := by nlinarith
        -- and then `simp [ENNReal.ofReal_lt_one]`-ish
        -- easiest: just let simp/nlinarith do it in your file
        exact ENNReal.ofReal_lt_ofReal this)

    -- apply pow→0 lemma
    -- one of the following lines should work in your mathlib:
    -- simpa [hδ_rewrite] using (ENNReal.tendsto_pow_atTop_nhds_0_of_lt_1 hlt1)
    simpa [hδ_rewrite] using (tendsto_pow_atTop_nhds_0_of_lt_1 hlt1)

  have hδ_tendsto0 : Tendsto (fun i => δ (m i)) atTop (𝓝 (0:ℝ≥0∞)) := by
    have hm_tendsto_atTop : Tendsto m atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro n
      simpa using (hm_ge n)

    -- have hδ_tendsto0_nat : Tendsto (fun n => δ n) atTop (𝓝 (0:ℝ≥0∞)) := by
    --   -- paste the proof from section B
    --   sorry

    exact hδ_tendsto0_nat.comp hm_tendsto_atTop

  have hOneMinus :
      Tendsto (fun i => (1 : ℝ≥0∞) - δ (m i)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    apply tendsto_order.2
    constructor
    · -- lower: ∀ a < 1, eventually a < 1 - δ(m i)
      intro a ha
      -- ε := 1 - a
      let ε : ℝ≥0∞ := (1 : ℝ≥0∞) - a
      have hεpos : 0 < ε := by
        -- 0 < 1 - a ↔ a < 1
        simpa [ε] using (tsub_pos_iff_lt.2 ha)

      have hIio : Set.Iio ε ∈ 𝓝 (0 : ℝ≥0∞) :=
        Iio_mem_nhds hεpos

      have hδlt : ∀ᶠ i in atTop, δ (m i) < ε :=
        (hδ_tendsto0.eventually hIio)

      filter_upwards [hδlt] with i hlt

      -- from δ < ε, get 1-ε < 1-δ
      have htsub : (1 : ℝ≥0∞) - ε < (1 : ℝ≥0∞) - δ (m i) := by
        -- Use: a < b - c  ↔  a + c < b
        -- So it suffices to show: (1 - ε) + δ(m i) < 1
        have hε_le1 : ε ≤ (1 : ℝ≥0∞) := by
          -- holds for any ε: 1 - ε ≤ 1, hence ε ≤ 1 is also true here because ε = 1 - a,
          -- but the easiest is to use your definition ε = 1 - a (so ε ≤ 1 is `tsub_le_self`)
          -- If ε is literally `1 - a`, this works:
          -- simpa [ε] using (tsub_le_self : (1 : ℝ≥0∞) - a ≤ 1)
          -- If ε is not definitional, use:
          have : (1 : ℝ≥0∞) - ε ≤ (1 : ℝ≥0∞) := tsub_le_self
          -- from (1-ε ≤ 1) we get ε ≤ 1? not in general.
          -- So prefer the definitional route when ε := 1 - a.
          -- I'll assume ε is `1 - a` as in your proof:
          simpa [ε] using (tsub_le_self : (1 : ℝ≥0∞) - a ≤ (1 : ℝ≥0∞))
  -- hlt : δ (m i) < ε

        have hδ_ne_top : δ (m i) ≠ (⊤ : ℝ≥0∞) := by
          -- δ is `ENNReal.ofReal _`
          simp [δ]

        have hε_ne_top : ε ≠ (⊤ : ℝ≥0∞) := by
          -- ε ≤ 1, and 1 ≠ ⊤
          have hε_le_one : ε ≤ (1 : ℝ≥0∞) := by
            -- if ε was defined as `ε := (1:ℝ≥0∞) - a`, this is immediate:
            simpa [ε] using (tsub_le_self : (1 : ℝ≥0∞) - a ≤ (1 : ℝ≥0∞))
          exact ne_of_lt (lt_of_le_of_lt hε_le_one (lt_top_iff_ne_top.2 (by simp)))

        -- move hlt to reals
        have hlt_real : (δ (m i)).toReal < ε.toReal := by
          -- `toReal` is strictly monotone on finite ENNReals
          exact (ENNReal.toReal_lt_toReal hδ_ne_top hε_ne_top).2 hlt

        -- strict inequality in ℝ
        have htsub_real : (1 : ℝ) - ε.toReal < (1 : ℝ) - (δ (m i)).toReal := by
          linarith

        -- rewrite toReal of tsub with `x=1` (finite) and `y ≤ 1`
        have hε_le_one : ε ≤ (1 : ℝ≥0∞) := by
          simpa [ε] using (tsub_le_self : (1 : ℝ≥0∞) - a ≤ (1 : ℝ≥0∞))

        have hδ_le_one : δ (m i) ≤ (1 : ℝ≥0∞) := by
          -- δ n = ofReal((1/2)^n) ≤ 1
          -- simp normally can do this:
          simp [δ]
          rw [← ENNReal.rpow_natCast]
          simp only [ENNReal.rpow_natCast]
          refine one_le_pow_of_one_le' (one_le_two) (m i)

        have htoReal_left :
            ((1 : ℝ≥0∞) - ε).toReal = (1 : ℝ) - ε.toReal := by
          -- lemma name is stable in mathlib:
          -- `ENNReal.toReal_tsub` needs `ε ≤ 1` and `1 ≠ ⊤`
          -- simpa using (ENNReal.toReal_tsub hε_le_one (by simp : (1 : ℝ≥0∞) ≠ ⊤))
          rw [ENNReal.toReal_sub_of_le hε_le_one ENNReal.one_ne_top]
          simp only [ENNReal.toReal_one]

        have htoReal_right :
            ((1 : ℝ≥0∞) - δ (m i)).toReal = (1 : ℝ) - (δ (m i)).toReal := by
          rw [ENNReal.toReal_sub_of_le hδ_le_one ENNReal.one_ne_top]
          simp only [ENNReal.toReal_one]

        -- pull back to ENNReal using strict monotonicity of toReal on finite values
        have hleft_ne_top : (1 : ℝ≥0∞) - ε ≠ (⊤ : ℝ≥0∞) := by
          exact ne_of_lt (lt_of_le_of_lt (tsub_le_self : (1 : ℝ≥0∞) - ε ≤ 1)
          (lt_top_iff_ne_top.2 (by simp)))
        have hright_ne_top : (1 : ℝ≥0∞) - δ (m i) ≠ (⊤ : ℝ≥0∞) := by
          exact ne_of_lt (lt_of_le_of_lt (tsub_le_self : (1 : ℝ≥0∞) - δ (m i) ≤ 1)
          (lt_top_iff_ne_top.2 (by simp)))

        -- convert the real inequality back to ENNReal
        have : ((1 : ℝ≥0∞) - ε).toReal < ((1 : ℝ≥0∞) - δ (m i)).toReal := by
          -- rewrite both sides, then use htsub_real
          simpa [htoReal_left, htoReal_right] using htsub_real

        exact (ENNReal.toReal_lt_toReal hleft_ne_top hright_ne_top).1 this


      -- rewrite 1 - ε = a (since a ≤ 1)
      have ha_le : a ≤ (1 : ℝ≥0∞) := le_of_lt ha

      -- ε = 1 - a, so 1 - ε = 1 - (1 - a) = a
      simp only [ε] at htsub
      suffices 1 - (1 - a) = a by
        rw [← this]
        exact htsub
      refine ENNReal.sub_sub_cancel ENNReal.one_ne_top ha_le

    · -- upper: ∀ b > 1, eventually 1 - δ(m i) < b
      intro b hb
      rw [Filter.eventually_atTop]
      use 1
      intro i hi

      -- always: 1 - δ(m i) ≤ 1
      have hle : (1 : ℝ≥0∞) - δ (m i) ≤ (1 : ℝ≥0∞) :=
        tsub_le_self
      exact lt_of_le_of_lt hle hb
  -- 8) show δ (m i) → 0, hence (1 - δ (m i)) → 1




  -- eventually (1 - δ (m i)) ≤ P(Target i)
      -- goal: Tendsto (fun i => P (Target i)) atTop (𝓝 (1 : ℝ≥0∞))
  have hmain : Tendsto (fun i : ℕ => (P (Target i) : ℝ≥0∞)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    refine (tendsto_order.2 ?_)
    constructor
    · intro r hr
      have hlt1 :
          ∀ᶠ i in atTop, r < (1 : ℝ≥0∞) - δ (m i) :=
        (hOneMinus.eventually (Ioi_mem_nhds hr))
      filter_upwards [hlt1, hlower_target] with i hir hil
      exact lt_trans hir hil
    · intro r hr
      -- show: ∀ᶠ i, P (Target i) < r
      have hle1 : ∀ i, (P (Target i) : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by
        intro i
        -- P(Target i) ≤ P(univ) = 1
        have hmono : P (Target i) ≤ P Set.univ :=
          measure_mono (Set.subset_univ (Target i))
        simp only [measure_univ] at hmono
        exact hmono

      -- then it's true for all i, hence eventually
      rw [Filter.eventually_atTop]
      use 1
      intro i hi
      exact lt_of_le_of_lt (hle1 i) hr
      -- have hle : ∀ᶠ i in atTop, (P (Target i) : ℝ≥0∞) ≤ 1 := by
      --   refine Filter.eventually_of_forall (fun i => ?_)
      --   simpa using (prob_le_one (μ := P) (s := Target i))
      -- filter_upwards [hle] with i hi
      -- exact lt_of_le_of_lt hi hr
  rcases (Filter.eventually_atTop.1 hlower_target) with ⟨N0, hN0⟩
  -- hN0 : ∀ i ≥ N0, 1 - δ (m i) < P (Target i)
  let L : ℕ → ℝ≥0∞ := fun i => if i < N0 then 0 else 1 - δ (m i)
  have hL_le : ∀ i, L i ≤ P (Target i) := by
    intro i
    by_cases hi : i < N0
    · simp [L, hi]  -- goal becomes 0 ≤ P (Target i)
    · have hi' : N0 ≤ i := le_of_not_gt hi
      have : 1 - δ (m i) < P (Target i) := hN0 i hi'
      have : 1 - δ (m i) ≤ P (Target i) := le_of_lt this
      simpa [L, hi] using this
  have hL_eq : ∀ᶠ i in atTop, L i = (1 - δ (m i)) := by
    refine (Filter.eventually_atTop.2 ⟨N0, ?_⟩)
    intro i hi
    have : ¬ i < N0 := not_lt.mpr hi
    simp [L, this]
  have hL_tendsto : Tendsto L atTop (𝓝 (1 : ℝ≥0∞)) := by
    -- `hL_eq : ∀ᶠ i, L i = 1 - δ (m i)`
    -- rewrite it as EventuallyEq
    have hEq : (fun i => L i) =ᶠ[atTop] fun i => (1 : ℝ≥0∞) - δ (m i) := hL_eq
    -- transfer
    exact (hOneMinus.congr' hEq.symm)

  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    hL_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 (1 : ℝ≥0∞)))
    ?_ ?_
  · -- pointwise L i ≤ P(Target i)
    -- exact (eventually_of_forall hL_le)
    intro i
    simp only
    exact hL_le i
  · intro i
    simp only
    apply prob_le_one
