import IsingBulk.Tail.ClosedUpperRootBoundary
import IsingBulk.Tail.DeformedRadialTransfer
import IsingBulk.Tail.SelectedGlobalEnvelope

/-! Actual coupled contour inputs for complete-pair compact transfer.
Root continuity is used at the real branch value, never holomorphy there. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology

theorem continuedRoot_real_segment_uniform {lo hi δ : ℝ} (hlo : -1 < lo) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ Icc lo hi, ∀ W : ℂ,
      ‖W-(w:ℂ)‖ < r → ‖continuedRoot W-continuedRoot (w:ℂ)‖ < δ := by
  let K := Complex.ofReal '' Icc lo hi
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hc : ∀ W ∈ K, ContinuousAt continuedRoot W := by
    rintro W ⟨w,hw,rfl⟩
    exact continuedRoot_continuousAt_real (hlo.trans_le hw.1)
  obtain ⟨r,hr,h⟩ := Metric.mem_uniformity_dist.mp
    (hK.uniformContinuousAt_of_continuousAt continuedRoot hc (Metric.dist_mem_uniformity hδ))
  refine ⟨r,hr,?_⟩
  intro w hw W hW
  have hh := h (a := (w:ℂ)) (b := W) (by simpa only [dist_eq_norm,norm_sub_rev] using hW)
    ⟨w,hw,rfl⟩
  change dist (continuedRoot (w:ℂ)) (continuedRoot W) < δ at hh
  simpa only [dist_eq_norm,norm_sub_rev] using hh

theorem radialAnglePoint_motion {v : ℝ} (hv : |v| ≤ 1) (θ : ℝ) :
    ‖radialAnglePoint v θ-limitingAngle θ‖ ≤ 2*|v| := by
  have he : radialAnglePoint v θ-limitingAngle θ=(Complex.exp (v:ℂ)-1)*limitingAngle θ := by
    rw [radialAnglePoint,Complex.exp_add]
    dsimp [limitingAngle]
    ring
  rw [he,norm_mul,limitingAngle_norm,mul_one]
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    Complex.norm_exp_sub_one_le (x := (v:ℂ)) (by simpa using hv)

theorem limitingAngle_reflection_motion {θ α : ℝ} (hα : 0 ≤ α) (hs : Real.sin θ ≤ 3*α/2) :
    ‖limitingAngle θ-((Real.cos θ:ℂ)-((|Real.sin θ|:ℝ):ℂ)*Complex.I)‖ ≤ 3*α := by
  have he : limitingAngle θ-((Real.cos θ:ℂ)-((|Real.sin θ|:ℝ):ℂ)*Complex.I)=
      ((Real.sin θ+|Real.sin θ|:ℝ):ℂ)*Complex.I := by
    rw [limitingAngle,Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos,← Complex.ofReal_sin]
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  by_cases hsin : 0 ≤ Real.sin θ
  · rw [abs_of_nonneg hsin,abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_neg (lt_of_not_ge hsin)]
    simp only [add_neg_cancel,abs_zero]
    positivity

theorem actual_deformedPoint_motion {N : ℕ} (hN : 0 < N) (f : SelectorFunctions)
    {c₀ eps τ lam α : ℝ} (hc : 0 ≤ c₀) (heps : 0 ≤ eps) (hτ : 0 ≤ τ)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hα : 0 ≤ α)
    (hp : ∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) (hm : ∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1)
    (hsmall : c₀*eps+2*τ ≤ 1) (θ : Fin N → ℝ) (i : Fin N)
    (hs : Real.sin (θ i) ≤ 3*α/2) :
    ‖deformedPoint f (Real.exp (-c₀*eps)) τ lam θ i-
      ((Real.cos (θ i):ℂ)-((|Real.sin (θ i)|:ℝ):ℂ)*Complex.I)‖ ≤ 2*(c₀*eps+2*τ)+3*α := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 := occupancy_nonneg (fun i => (hp (θ i)).1)
  have hP1 := occupancy_le (fun i => (hp (θ i)).2)
  have hv := coupledRadialExponent_bound hc heps hτ hl0 hl1 (hp (θ i)).1 (hp (θ i)).2 (hm (θ i)).1 (hm (θ i)).2
    (div_nonneg hP0 hn.le) ((div_le_one hn).mpr hP1)
  rw [deformedPoint_coupledRadialExponent]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (limitingAngle (θ i)) _).trans
    (add_le_add ((radialAnglePoint_motion (hv.trans hsmall) (θ i)).trans (by gcongr))
      (limitingAngle_reflection_motion hα hs))

theorem actual_deformed_sourceW_disk_motion (d : LocalBranchData) {N : ℕ} (hN : 1 ≤ N)
    (f : SelectorFunctions) {eps τ lam c : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hτ : 0 ≤ τ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hc : c ≤ 1/4)
    (hp : ∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) (hm : ∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1)
    (hsmall : d.c₀*eps+2*τ ≤ 1) (θ : Fin N → ℝ) (i : Fin N) {s : ℂ}
    (hs : ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ)) :
    ‖sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
      (limitingAngularW d.thetaB (θ i):ℂ)‖ ≤ 3*c/(N:ℝ)+(3+2*d.c₀)*eps+4*τ := by
  have hs0 := (selected_disk_parameter_envelope hN heps heps1 hc hs).1
  have hsn : 1 ≤ ‖radialParameter d.theta eps‖ := by rw [radialParameter_norm heps]; linarith
  have hd := sourceS_sub_norm_le hs0 hsn
  have hy := deformedPoint_sourceW_transfer d (by omega) f θ heps hτ hl0 hl1 hp hm hsmall i
  have he : sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
      sourceW (radialParameter d.theta eps) (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)=
      sourceS s-sourceS (radialParameter d.theta eps) := by unfold sourceW; ring
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))
    (sourceW (radialParameter d.theta eps) (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i))
    (limitingAngularW d.thetaB (θ i):ℂ)
  rw [he] at ht
  have hsc : 3*‖s-radialParameter d.theta eps‖ ≤ 3*c/(N:ℝ) := by
    calc
      _ ≤ 3*(c/(N:ℝ)) := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = _ := by ring
  linarith

/-- Uniform motion for every actual coordinate, including both endpoint
slivers and the lower branch, before N, occupancy or lambda are chosen. -/
theorem actual_current_pair_inputs (d : LocalBranchData) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧
      ∀ (N : ℕ) (eps τ lam α c : ℝ) (f : SelectorFunctions) (θ : Fin N → ℝ) (s : ℂ),
        1 ≤ N → 0 ≤ eps → eps < r → 0 ≤ τ → τ < r → 0 ≤ lam → lam ≤ 1 →
        0 ≤ α → α < r → c ≤ r →
        (∀ x, 0 ≤ f.p x ∧ f.p x ≤ 1) → (∀ x, 0 ≤ f.m x ∧ f.m x ≤ 1) →
        ‖s-radialParameter d.theta eps‖ ≤ c/(N:ℝ) → ∀ i,
        Real.sin (θ i) ≤ 3*α/2 →
        ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-
          ((Real.cos (θ i):ℂ)-((|Real.sin (θ i)|:ℝ):ℂ)*Complex.I)‖ < δ ∧
        ‖selectedContinuedRoot s (deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)-
          continuedRoot (limitingAngularW d.thetaB (θ i):ℂ)‖ < δ := by
  have hcos : -1 < Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  obtain ⟨rW,hrW,hroot⟩ := continuedRoot_real_segment_uniform (hi := 2+Real.cos d.thetaB) hcos hδ
  let v := min δ rW
  let r := min (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1)))
  have hv : 0 < v := lt_min hδ hrW
  have hcp : 0 < d.c₀+1 := by linarith [d.c₀_pos]
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrbase : 4*(d.c₀+1)*r ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*(d.c₀+1))).mp (min_le_left (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1))))
    nlinarith only [hh]
  have hrsmall : 20*(d.c₀+1)*r ≤ v := by
    have hh := (le_div_iff₀ (by positivity : 0<20*(d.c₀+1))).mp (min_le_right (1/(4*(d.c₀+1))) (v/(20*(d.c₀+1))))
    nlinarith only [hh]
  have hrquarter : r ≤ 1/4 := by nlinarith [mul_nonneg d.c₀_pos.le hr.le]
  refine ⟨r,hr,hrquarter,?_⟩
  intro N eps τ lam α c f θ s hN heps hepsr hτ hτr hl0 hl1 hα hαr hc hp hm hs i hsin
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hsmall : d.c₀*eps+2*τ ≤ 1 := by nlinarith [mul_nonneg d.c₀_pos.le hr.le]
  have heps1 : eps ≤ 1 := by linarith
  have hcN : c/(N:ℝ) ≤ r := by
    apply (div_le_iff₀ (by linarith : (0:ℝ)<N)).mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hn)]
  constructor
  · have hh := actual_deformedPoint_motion (by omega) f d.c₀_pos.le heps hτ hl0 hl1 hα hp hm hsmall θ i hsin
    apply hh.trans_lt
    have hvδ : v ≤ δ := min_le_left _ _
    nlinarith [mul_nonneg d.c₀_pos.le (sub_nonneg.mpr hepsr.le),mul_nonneg d.c₀_pos.le hr.le]
  · apply hroot (limitingAngularW d.thetaB (θ i))
      ⟨by unfold limitingAngularW; linarith [Real.cos_le_one (θ i)],
       by unfold limitingAngularW; linarith [Real.neg_one_le_cos (θ i)]⟩
    have hh := actual_deformed_sourceW_disk_motion d hN f heps heps1 hτ hl0 hl1 (hc.trans hrquarter) hp hm hsmall θ i hs
    apply hh.trans_lt
    have hvW : v ≤ rW := min_le_right _ _
    have hdiv : 3*c/(N:ℝ) ≤ 3*r := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcN (by norm_num : (0:ℝ)≤3)
    nlinarith [mul_nonneg d.c₀_pos.le (sub_nonneg.mpr hepsr.le),mul_nonneg d.c₀_pos.le hr.le]


/-- Original-circle specialization has no particle-count restriction. -/
theorem actual_original_pair_inputs (d : LocalBranchData) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/4 ∧ ∀ eps α θ : ℝ, ∀ s : ℂ,
      0 ≤ eps → eps < r → 0 ≤ α → α < r →
      ‖s-radialParameter d.theta eps‖ ≤ r → Real.sin θ ≤ 3*α/2 →
      ‖radialAnglePoint (-d.c₀*eps) θ-
        ((Real.cos θ:ℂ)-((|Real.sin θ|:ℝ):ℂ)*Complex.I)‖ < δ ∧
      ‖selectedContinuedRoot s (radialAnglePoint (-d.c₀*eps) θ)-
        continuedRoot (limitingAngularW d.thetaB θ:ℂ)‖ < δ := by
  obtain ⟨r,hr,hr1,hinput⟩ := actual_current_pair_inputs d hδ
  refine ⟨r,hr,hr1,?_⟩
  intro eps α θ s heps hepsr hα hαr hs hsin
  let f : SelectorFunctions := ⟨fun _ => 0,fun _ => 0,fun _ => 0⟩
  have hh := hinput 1 eps 0 0 α r f (fun _ => θ) s (by norm_num) heps hepsr
    (by norm_num) hr (by norm_num) (by norm_num) hα hαr le_rfl
    (fun _ => by simp [f]) (fun _ => by simp [f]) (by simpa using hs) 0 hsin
  have hy : deformedPoint f (Real.exp (-d.c₀*eps)) 0 0 (fun _ : Fin 1 => θ) 0 =
      radialAnglePoint (-d.c₀*eps) θ := by
    rw [deformedPoint_coupledRadialExponent]
    simp [coupledRadialExponent]
  simpa only [hy] using hh


end
end IsingBulk.Tail
