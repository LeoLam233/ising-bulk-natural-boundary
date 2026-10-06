import IsingBulk.Tail.SectorMicrocoreAngleBox
import IsingBulk.Tail.SectorPartitionSupport

/-! The complete all-branch angleBox sector is identified with an actual
compact real lower-branch chart before Lie transport. A fixed chart cutoff
is constructed to equal one on the entire source all-branch support. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

theorem scaledMicroCutoff_one {N : ℕ} {h : ℝ} (hh : 0 < h) (u : Fin N → ℝ)
    (hu : ∀ i, |u i| ≤ h/2) : scaledMicroCutoff N h u=1 := by
  apply Finset.prod_eq_one
  intro i _
  apply fixedBranchBump_one 1 (by norm_num)
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr (by linarith [hu i])

def allBranchChartWeight (N : ℕ) (b eta alpha delta h : ℝ) (hd : 0 < delta)
    (u : Fin N → ℝ) : ℝ :=
  scaledMicroCutoff N h u*angularSelector (constructedSelector b eta alpha) (fun i => u i-b)*
    ∏ i, sectorBranch b delta hd (u i-b)

def allBranchChartIntegral (N : ℕ) (d : LocalBranchData) (eta delta h eps : ℝ) (hd : 0 < delta)
    (w : (Fin N → ℝ) → ℂ) (s : ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹*∫ u, w u*(allBranchChartWeight N d.thetaB eta d.alpha delta h hd u:ℝ)*
    sourceReducedAngularDensity (Real.exp (-d.c₀*eps)) s (fun i => u i-d.thetaB)

def allBranchBoxIntegral (N : ℕ) (d : LocalBranchData) (eta delta eps : ℝ) (hd : 0 < delta)
    (w : (Fin N → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N, w (fun i => theta i+d.thetaB-2*Real.pi)*
    (angularSelector (constructedSelector d.thetaB eta d.alpha) theta*(∏ i,sectorBranch d.thetaB delta hd (theta i)):ℝ)*
    pulledDensity (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps)) d.tau 0 s theta

theorem allBranchChartWeight_smooth (N : ℕ) (b eta alpha delta h : ℝ) (hd : 0 < delta) :
    ContDiff ℝ ∞ (allBranchChartWeight N b eta alpha delta h hd) := by
  have hupper : ContDiff ℝ ∞ (fun u : Fin N → ℝ => angularSelector (constructedSelector b eta alpha) (fun i => u i-b)) := by
    unfold angularSelector selectorWeight constructedSelector periodicUpperA thresholdStep
    exact contDiff_prod (fun i _ => contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (((Real.contDiff_sin.comp ((contDiff_apply ℝ ℝ i).sub contDiff_const)).sub contDiff_const).div_const _)))
  exact ((scaledMicroCutoff_smooth N h).mul hupper).mul
    (contDiff_prod (fun i _ => (sector_labels_smooth b delta hd).2.2.comp
      ((contDiff_apply ℝ ℝ i).sub contDiff_const)))

theorem allBranchChartWeight_tsupport {N : ℕ} (b eta alpha delta h : ℝ) (hd : 0 < delta)
    (hh : 0 < h) : tsupport (allBranchChartWeight N b eta alpha delta h hd) ⊆ {u | ∀ i, |u i| ≤ h} := by
  intro u hu
  have hc : u ∈ tsupport (scaledMicroCutoff N h) :=
    tsupport_mul_subset_left (tsupport_mul_subset_left hu)
  exact scaledMicroCutoff_jet_tsupport hh [] hc

theorem all_branch_box_eq_compact_chart (d : LocalBranchData) (h : ℝ) (hh : 0 < h)
    (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (halpha : d.alpha < Real.sin d.thetaB/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta, delta ≤ delta0 →
      ∀ (N : ℕ) (eta eps : ℝ), 0 < eps → ∀ (w : (Fin N → ℝ) → ℂ) (s : ℂ),
        s ∈ dampingDomain (Real.exp (-d.c₀*eps)) →
        allBranchBoxIntegral N d eta delta eps hd w s = allBranchChartIntegral N d eta delta h eps hd w s := by
  obtain ⟨delta0,hd0,hcover⟩ := original_sector_branch_lower_chart d.thetaB_pos d.thetaB_lt (half_pos hh)
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta N eta eps heps w s hs
  let r := Real.exp (-d.c₀*eps)
  let center : Fin N → ℝ := fun _ => 2*Real.pi-d.thetaB
  let base : (Fin N → ℝ) → ℝ := fun theta =>
    angularSelector (constructedSelector d.thetaB eta d.alpha) theta * ∏ i, sectorBranch d.thetaB delta hd (theta i)
  let F : (Fin N → ℝ) → ℂ := fun theta =>
    w (fun i => theta i+d.thetaB-2*Real.pi)*
      (scaledMicroCutoff N h (fun i => theta i+d.thetaB-2*Real.pi)*base theta:ℝ)*sourceReducedAngularDensity r s theta
  have hinsert (theta : Fin N → ℝ) (htheta : theta ∈ angleBox N) :
      scaledMicroCutoff N h (fun i => theta i+d.thetaB-2*Real.pi)*base theta=base theta := by
    by_cases hz : base theta=0
    · rw [hz,mul_zero]
    · have hsel : angularSelector (constructedSelector d.thetaB eta d.alpha) theta≠0 := (mul_ne_zero_iff.mp hz).1
      have hp : (∏ i, sectorBranch d.thetaB delta hd (theta i))≠0 := (mul_ne_zero_iff.mp hz).2
      have hchi : scaledMicroCutoff N h (fun i => theta i+d.thetaB-2*Real.pi)=1 := by
        apply scaledMicroCutoff_one hh
        intro i
        exact (hcover delta hd hdelta N eta d.alpha d.alpha_pos halpha theta htheta
          (subset_closure hsel) i (subset_closure (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)))).le
      rw [hchi,one_mul]
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hnorm (theta : Fin N → ℝ) : pulledDensity (constructedSelector d.thetaB eta d.alpha) r d.tau 0 s theta =
      (N.factorial:ℂ)⁻¹*sourceReducedAngularDensity r s theta := by
    have hadm := (globalRoot_admissible (Real.exp_pos _) hr1 hs.2).toTuple N (angleTuple r theta)
      (fun i => anglePoint_norm (Real.exp_pos _).le (theta i))
    simpa only [sourceReducedAngularDensity,mul_assoc] using
      pulledDensity_original (constructedSelector d.thetaB eta d.alpha) r d.tau s theta hadm
  have hsupport : ∀ theta, theta ∉ angleBox N → F theta=0 := by
    intro theta hout
    by_cases hz : scaledMicroCutoff N h (fun i => theta i+d.thetaB-2*Real.pi)=0
    · simp [F,hz]
    · have hu := scaledMicroCutoff_jet_tsupport hh [] (subset_closure hz)
      exfalso
      apply hout
      constructor <;> intro i
      · have hx := (abs_le.mp (hu i)).1
        have hb := d.thetaB_lt
        linarith [Real.pi_pos]
      · have hx := (abs_le.mp (hu i)).2
        linarith [d.thetaB_pos]
  have heq : allBranchBoxIntegral N d eta delta eps hd w s = (N.factorial:ℂ)⁻¹*∫ theta in angleBox N, F theta := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro theta htheta
    change w _*(base theta:ℝ)*pulledDensity _ r d.tau 0 s theta = _
    rw [hnorm]
    dsimp only [F]
    rw [hinsert theta htheta]
    ring
  rw [heq,setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  unfold allBranchChartIntegral
  congr 1
  rw [← integral_add_right_eq_self F center]
  apply integral_congr_ae
  filter_upwards [] with u
  have hu : (fun i => (u+center) i+d.thetaB-2*Real.pi)=u := by funext i; dsimp [center]; ring
  have hperiod : u+center=fun i => (u i-d.thetaB)+2*Real.pi := by funext i; dsimp [center]; ring
  dsimp only [F]
  rw [hu]
  dsimp only [base]
  rw [hperiod,constructedSelector_all_period,sectorBranch_all_period,sourceReducedAngularDensity_all_period]
  dsimp [allBranchChartWeight]
  push_cast
  ring


theorem all_branch_box_chart_derivatives (d : LocalBranchData) (h : ℝ) (hh : 0 < h)
    (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (halpha : d.alpha < Real.sin d.thetaB/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta, delta ≤ delta0 →
      ∀ (N : ℕ) (eta eps : ℝ), 0 < eps → ∀ (w : (Fin N → ℝ) → ℂ) (s : ℂ),
        s ∈ dampingDomain (Real.exp (-d.c₀*eps)) → ∀ j : ℕ,
        iteratedDeriv j (allBranchBoxIntegral N d eta delta eps hd w) s =
          iteratedDeriv j (allBranchChartIntegral N d eta delta h eps hd w) s := by
  obtain ⟨delta0,hd0,heq⟩ := all_branch_box_eq_compact_chart d h hh hhb hhpi halpha
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta N eta eps heps w s hs j
  have he : allBranchBoxIntegral N d eta delta eps hd w =ᶠ[𝓝 s]
      allBranchChartIntegral N d eta delta h eps hd w := by
    filter_upwards [(dampingDomain_isOpen _).mem_nhds hs] with z hz
    exact heq delta hd hdelta N eta eps heps w z hz
  exact he.iteratedDeriv_eq j

end
end IsingBulk.Tail
