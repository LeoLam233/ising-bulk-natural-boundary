import IsingBulk.Tail.AllBranchExteriorPhaseSeparation
import IsingBulk.Tail.MicrocoreDensity
import IsingBulk.Tail.MicrocoreArclength
import IsingBulk.Tail.OriginalGlobalDisk
import IsingBulk.Analysis.JetsLocalChart
import IsingBulk.First.ResidueBounds

/-! Actual original all-B points instantiate the complete selected-pair
regular chart. Its low-dimensional neighborhood precedes all N and pairs. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.First Set Metric
open scoped BigOperators

theorem allBranchExterior_actualJetPoint_of_micro {n : ℕ} (v θ : ℝ) (s : ℂ) (u : AngularSpace n)
    (p q : Fin (n+1)) (hv : v < 0) (h : MicrocoreJetPoint v θ s u)
    (hc : CoefficientPoint p q (s,chartMap v θ s u))
    (hδ : chartMap v θ s u q-chartMap v θ s u p ≠ 0) : ActualJetPoint v θ p q s u := by
  let φ := chartMap v θ s u
  have hy : ∀ i, ‖regularY s (φ i)‖ < 1 := by
    intro i
    rw [show φ i=chartPhase s v θ (u i) from rfl,regularY_chartPhase _ _ _ _ (h.g_pos i),
      angularY_norm_real,Real.exp_lt_one_iff]
    exact hv
  have hz : ∀ i, ‖Complex.exp (-Complex.I*φ i)‖ < 1 := by
    intro i
    rw [show φ i=chartPhase s v θ (u i) from rfl,← chart_root_eq_physical]
    exact interiorRoot_norm_lt_one (h.im_pos i)
  have hyden : ∀ i, 1-(regularY s (φ i))^(-2:ℤ) ≠ 0 := by
    intro i
    have hh := one_sub_mul_ne_zero_of_norm_lt_one (hy i) (hy i)
    simp only [zpow_neg,zpow_ofNat]
    intro he
    have hx := inv_eq_one.mp (sub_eq_zero.mp he).symm
    apply hh
    rw [← pow_two,hx]
    simp
  have hKernel : regularKernel s φ ≠ 0 := by
    apply mul_ne_zero
    · exact one_sub_coordinateProduct_ne_zero (by omega) hy
    · rw [regularZProduct_eq_prod]
      exact one_sub_coordinateProduct_ne_zero (by omega) hz
  have hnum : regularG s (φ p)*Complex.sin (φ q)-regularG s (φ q)*Complex.sin (φ p) ≠ 0 := by
    rw [selected_denominator_identity s (φ p) (φ q) hc.gsum_ne]
    exact mul_ne_zero hδ hc.den_ne
  have hb : regularB s (φ p)-regularB s (φ q) ≠ 0 := by
    intro he
    apply hnum
    unfold regularB at he
    have hp := h.sin_ne p
    have hq := h.sin_ne q
    change Complex.sin (φ p) ≠ 0 at hp
    change Complex.sin (φ q) ≠ 0 at hq
    field_simp [hp,hq] at he
    simpa only [mul_zero,zero_mul,mul_comm] using he
  have hb' : chartB s v θ (u p)-chartB s v θ (u q) ≠ 0 := by
    simpa only [φ,chartMap,regularB_chartPhase _ _ _ _ (h.g_pos _)] using hb
  exact ⟨hc,h.s_ne,h.re_pos,h.im_pos,h.g_pos,h.sin_ne,hb',h.slit,hyden,hδ,hKernel⟩

theorem allBranchExterior_original_actual_chart (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ n : ℕ,
      ∀ p q : Fin (n+1), ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) → u p ≠ u q →
      ActualJetPoint (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    change ‖radialParameter d.theta 0‖ ≠ 0
    rw [radialParameter_norm (by norm_num)]
    norm_num
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [IsingBulk.First.sourceS,s₀] using sourceS_radial_zero_branch d
  have hcos : |Real.cos d.thetaB| < 1 := by
    have hs : 0 < Real.sin d.thetaB := d.a_pos
    have hh := Real.sin_sq_add_cos_sq d.thetaB
    rw [abs_lt]
    constructor <;> nlinarith [Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨U,P,hU,hsU,hP,hsP,hcoeff⟩ := coefficient_neighborhoods s₀ (Real.cos d.thetaB) hs₀ hS hcos
  obtain ⟨rU,hrU,hsubU⟩ := Metric.isOpen_iff.mp hU (s₀,0) hsU
  obtain ⟨rP,hrP,hsubP⟩ := Metric.isOpen_iff.mp hP (s₀,0,0) hsP
  let R := min rU rP
  have hR : 0 < R := lt_min hrU hrP
  obtain ⟨rφ,Cφ,hrφ,_,hφ⟩ := original_phase_small_radius d R hR
  obtain ⟨rChart,hrChart,hChart⟩ := original_microcore_chart d
  obtain ⟨c,rSep,hc,hrSep,hSep⟩ := original_phase_difference_lower d
  let r := min R (min rφ (min rChart rSep))/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := (half_lt_self (lt_min hR (lt_min hrφ (lt_min hrChart hrSep)))).trans_le (min_le_left _ _)
  have hrest : r < rφ ∧ r < rChart ∧ r < rSep := by
    have hh : r < min rφ (min rChart rSep) :=
      (half_lt_self (lt_min hR (lt_min hrφ (lt_min hrChart hrSep)))).trans_le (min_le_right _ _)
    simpa only [lt_min_iff] using hh
  refine ⟨r,hr,?_⟩
  intro ε hε hεr n p q u hu hupq
  let s := radialParameter d.theta ε
  let v := -d.c₀*ε
  have hchart := hChart ε hε (hεr.trans_lt hrest.2.1) n u (fun i => (hu i).trans_lt hrest.2.1)
  have hs : ‖s-s₀‖ < R := by rw [radialParameter_sub_zero_norm d.theta ε hε.le]; exact hεr.trans_lt hrR
  have hphase : ∀ i, ‖chartMap v d.thetaB s u i‖ < R := by
    intro i
    rw [original_chartMap_eq]
    exact (hφ ε r (u i) hε hεr hrest.1 (hu i)).2
  have hcpoint : CoefficientPoint p q (s,chartMap v d.thetaB s u) := by
    apply hcoeff (n+1) p q (s,chartMap v d.thetaB s u)
    · intro i
      apply hsubU
      simpa [mem_ball,Prod.dist_eq,dist_eq_norm] using
        And.intro (hs.trans_le (min_le_left _ _)) ((hphase i).trans_le (min_le_left _ _))
    · apply hsubP
      simpa [mem_ball,Prod.dist_eq,dist_eq_norm] using
        And.intro (hs.trans_le (min_le_right _ _))
          (And.intro ((hphase p).trans_le (min_le_right _ _)) ((hphase q).trans_le (min_le_right _ _)))
  apply allBranchExterior_actualJetPoint_of_micro v d.thetaB s u p q (by dsimp [v]; nlinarith [d.c₀_pos]) hchart hcpoint
  rw [original_chartMap_eq]
  apply norm_pos_iff.mp
  have hh := hSep ε (u q) (u p) hε (hεr.trans hrest.2.2.le)
    ((hu q).trans hrest.2.2.le) ((hu p).trans hrest.2.2.le)
  exact (mul_pos hc (abs_pos.mpr (sub_ne_zero.mpr hupq.symm))).trans_le hh

end
end IsingBulk.Tail
