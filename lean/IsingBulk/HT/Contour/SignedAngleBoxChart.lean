import IsingBulk.HT.Contour.SignedChartBridge
import IsingBulk.Tail.AllBranchAngleBoxChart

/-! Exact signed angular-box to compact-chart change of variables. The real
support proof and angular periodicity are independent of the signed product
gaps, so this correspondence holds for every complex parameter and sign. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

theorem signedSourceAngularDensity_all_period {N : ℕ} (σ : ℂ) (r : ℝ) (s : ℂ)
    (theta : Fin N → ℝ) :
    signedSourceAngularDensity σ r s (fun i => theta i+2*Real.pi)=
      signedSourceAngularDensity σ r s theta := by
  have hy : angleTuple r (fun i => theta i+2*Real.pi)=angleTuple r theta := by
    funext i; exact anglePoint_add_period r (theta i)
  simp only [signedSourceAngularDensity,angleProductJacobian,angleJacobian,anglePoint_add_period,hy]

def signedAllBranchChartIntegral (σ : ℂ) (N : ℕ) (d : LocalBranchData) (eta delta h eps : ℝ) (hd : 0 < delta)
    (w : (Fin N → ℝ) → ℂ) (s : ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹*∫ u, w u*(allBranchChartWeight N d.thetaB eta d.alpha delta h hd u:ℝ)*
    signedSourceAngularDensity σ (Real.exp (-d.c₀*eps)) s (fun i => u i-d.thetaB)

def signedAllBranchBoxIntegral (σ : ℂ) (N : ℕ) (d : LocalBranchData) (eta delta eps : ℝ) (hd : 0 < delta)
    (w : (Fin N → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N, w (fun i => theta i+d.thetaB-2*Real.pi)*
    (angularSelector (constructedSelector d.thetaB eta d.alpha) theta*(∏ i,sectorBranch d.thetaB delta hd (theta i)):ℝ)*
    signedPulledDensity σ (constructedSelector d.thetaB eta d.alpha) (Real.exp (-d.c₀*eps)) d.tau 0 s theta

theorem signed_all_branch_box_eq_compact_chart (d : LocalBranchData) (h : ℝ) (hh : 0 < h)
    (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (halpha : d.alpha < Real.sin d.thetaB/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta, delta ≤ delta0 →
      ∀ (σ : ℂ) (N : ℕ) (eta eps : ℝ) (w : (Fin N → ℝ) → ℂ) (s : ℂ),
        signedAllBranchBoxIntegral σ N d eta delta eps hd w s = signedAllBranchChartIntegral σ N d eta delta h eps hd w s := by
  obtain ⟨delta0,hd0,hcover⟩ := original_sector_branch_lower_chart d.thetaB_pos d.thetaB_lt (half_pos hh)
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta σ N eta eps w s
  let r := Real.exp (-d.c₀*eps)
  let center : Fin N → ℝ := fun _ => 2*Real.pi-d.thetaB
  let base : (Fin N → ℝ) → ℝ := fun theta =>
    angularSelector (constructedSelector d.thetaB eta d.alpha) theta * ∏ i, sectorBranch d.thetaB delta hd (theta i)
  let F : (Fin N → ℝ) → ℂ := fun theta =>
    w (fun i => theta i+d.thetaB-2*Real.pi)*
      (scaledMicroCutoff N h (fun i => theta i+d.thetaB-2*Real.pi)*base theta:ℝ)*signedSourceAngularDensity σ r s theta
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
  have hnorm (theta : Fin N → ℝ) : signedPulledDensity σ (constructedSelector d.thetaB eta d.alpha) r d.tau 0 s theta =
      (N.factorial:ℂ)⁻¹*signedSourceAngularDensity σ r s theta := by
    simpa only [signedSourceAngularDensity,mul_assoc] using
      signedPulledDensity_original σ (constructedSelector d.thetaB eta d.alpha) r d.tau s theta
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
  have heq : signedAllBranchBoxIntegral σ N d eta delta eps hd w s = (N.factorial:ℂ)⁻¹*∫ theta in angleBox N, F theta := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro theta htheta
    change w _*(base theta:ℝ)*signedPulledDensity σ _ r d.tau 0 s theta = _
    rw [hnorm]
    dsimp only [F]
    rw [hinsert theta htheta]
    ring
  rw [heq,setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
  unfold signedAllBranchChartIntegral
  congr 1
  rw [← integral_add_right_eq_self F center]
  apply integral_congr_ae
  filter_upwards [] with u
  have hu : (fun i => (u+center) i+d.thetaB-2*Real.pi)=u := by funext i; dsimp [center]; ring
  have hperiod : u+center=fun i => (u i-d.thetaB)+2*Real.pi := by funext i; dsimp [center]; ring
  dsimp only [F]
  rw [hu]
  dsimp only [base]
  rw [hperiod,constructedSelector_all_period,sectorBranch_all_period,signedSourceAngularDensity_all_period]
  dsimp [allBranchChartWeight]
  push_cast
  ring


/-- The fixed real cutoff is kept unchanged through every complex derivative. -/
theorem signed_all_branch_box_chart_derivatives (d : LocalBranchData) (h : ℝ) (hh : 0 < h)
    (hhb : h ≤ d.thetaB/2) (hhpi : h ≤ (Real.pi-d.thetaB)/2)
    (halpha : d.alpha < Real.sin d.thetaB/4) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, ∀ hd : 0 < delta, delta ≤ delta0 →
      ∀ (σ : ℂ) (N : ℕ) (eta eps : ℝ) (w : (Fin N → ℝ) → ℂ) (s : ℂ) (j : ℕ),
        iteratedDeriv j (signedAllBranchBoxIntegral σ N d eta delta eps hd w) s =
          iteratedDeriv j (signedAllBranchChartIntegral σ N d eta delta h eps hd w) s := by
  obtain ⟨delta0,hd0,heq⟩ := signed_all_branch_box_eq_compact_chart d h hh hhb hhpi halpha
  refine ⟨delta0,hd0,?_⟩
  intro delta hd hdelta σ N eta eps w s j
  have hf : signedAllBranchBoxIntegral σ N d eta delta eps hd w =
      signedAllBranchChartIntegral σ N d eta delta h eps hd w := by
    funext z
    exact heq delta hd hdelta σ N eta eps w z
  rw [hf]

end
end IsingBulk.HT.Contour
