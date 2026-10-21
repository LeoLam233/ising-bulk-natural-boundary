import IsingBulk.HT.First.RegularChartData
import IsingBulk.HT.First.RegularOddLocalAsymptotic
import IsingBulk.HT.First.RegularOddLowerLocal
import IsingBulk.HT.First.NegativeComplementBound
import IsingBulk.First.SelectedYCutoffs

/-! Actual negative-family FIRST attachment on the original integer-angle
selected point. No reflected positive prime family or analytic certificate
is substituted for the literal physical source. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First IsingBulk.First.Regular
open scoped Topology BigOperators ContDiff

theorem negative_selected_lower_center_root {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : NegativeAdmissible p a) :
    exp (-(p:ℂ)*(IsingBulk.PrimeFamily.angle p a:ℂ)*I) = 1 := by
  have hpw := (negative_angleRoot_primitive hp ha).pow_eq_one
  rw [show -(p:ℂ)*(IsingBulk.PrimeFamily.angle p a:ℂ)*I =
    -(p:ℂ)*((IsingBulk.PrimeFamily.angle p a:ℂ)*I) by ring,
    neg_mul,exp_neg,exp_nat_mul]
  change (IsingBulk.PrimeFamily.angleRoot p a^p)⁻¹ = 1
  rw [hpw,inv_one]

theorem regular_chart_centers_ne (a : RegularChartData) (hab : a.alpha ≠ a.beta) :
    exp (-(a.alpha:ℂ)*I) ≠ exp (-(a.beta:ℂ)*I) := by
  intro he
  have hh := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := -(a.alpha:ℂ)*I) (y := -(a.beta:ℂ)*I)
    (by simpa using (show -Real.pi < -a.alpha by linarith [a.alpha_lt_pi,Real.pi_pos]))
    (by simpa using (show -a.alpha ≤ Real.pi by linarith [a.alpha_pos,Real.pi_pos]))
    (by simpa using (show -Real.pi < -a.beta by linarith [a.beta_lt_pi,Real.pi_pos]))
    (by simpa using (show -a.beta ≤ Real.pi by linarith [a.beta_pos,Real.pi_pos])) he
  have hi := congrArg Complex.im hh
  have hab' : a.alpha = a.beta := by simpa using hi
  exact hab hab'

theorem negative_selected_cutoff_delta_bound_pos {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (hab : a ≠ b) :
    0 < compatibleCutoffDeltaBound (PrimeFamily.angle p a) (PrimeFamily.angle p b) :=
  compatibleCutoffDeltaBound_pos (regular_chart_centers_ne
    (negativeSelectedRegularChart ha hb) (prime_angle_ne hp hab))

theorem negative_selected_local_pair_asymptotic {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (hab : a ≠ b) :
    let n := p-1
    let k := derivativeOrder (n+1)
    let A := negativeSelectedRegularChart ha hb
    (-I*localLeadingCoefficient A n k) ≠ 0 ∧
    ∃ (U : Set (Fin n → ℝ)) (c : CompatibleYCutoffData n A.alpha A.beta U),
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.leftWeight epsilon -
          (epsilon:ℂ)⁻¹*(-I*localLeadingCoefficient A n k))
        (fun epsilon => (epsilon:ℂ)⁻¹) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.rightWeight epsilon -
          (epsilon:ℂ)⁻¹*(-I*localLeadingCoefficient A n k))
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let n := p-1
  let A := negativeSelectedRegularChart ha hb
  let k := derivativeOrder (n+1)
  have hN : n+1=p := by dsimp [n]; have := hp.two_le; omega
  have hn : 1 ≤ n := by dsimp [n]; have := hp.two_le; omega
  have ho : Odd (n+1) := by rw [hN]; exact hp.odd_of_ne_two (by omega)
  have hNc : (n+1:ℂ)=((p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(n+1:ℂ)*(A.alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact negative_selected_lower_center_root hp ha
  have hBeta : exp (-(n+1:ℂ)*(A.beta:ℂ)*I)=1 := by
    rw [hNc]
    exact negative_selected_lower_center_root hp hb
  obtain ⟨hL,Da,hDa,hA⟩ := actual_local_mean_odd_asymptotic hn A ho hAlpha hBeta
  obtain ⟨_,Db,hDb,hB⟩ := actual_local_mean_odd_asymptotic hn A.swap ho hBeta hAlpha
  have hCut : 0 < compatibleCutoffDeltaBound A.alpha A.beta :=
    negative_selected_cutoff_delta_bound_pos hp ha hb hab
  let D := min Da (min Db (compatibleCutoffDeltaBound A.alpha A.beta))
  have hD : 0 < D := lt_min hDa (lt_min hDb hCut)
  let delta := D/2
  have hd : 0 < delta := half_pos hD
  have hdD : delta ≤ D := (half_lt_self hD).le
  have hdA : delta ≤ Da := hdD.trans (min_le_left _ _)
  have hdB : delta ≤ Db := hdD.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdCut : delta ≤ compatibleCutoffDeltaBound A.alpha A.beta :=
    hdD.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Ra,hRa,hPA⟩ := hA delta hd hdA
  obtain ⟨Rb,hRb,hPB⟩ := hB delta hd hdB
  let R := min Ra Rb
  have hR : 0 < R := lt_min hRa hRb
  let U := sourceShapeBall n R
  obtain ⟨c,hcd,hcH⟩ := exists_compatibleYCutoffData_at_delta n A.alpha A.beta
    (sourceShapeBall_mem_nhds_zero n hR) (show (0:ℝ)<1 by norm_num) hd hdCut
  have hη : Continuous (fun v => (c.eta v:ℂ)) := Complex.continuous_ofReal.comp c.eta_smooth.continuous
  have hη1 : ∀ v : ℝ, |v| ≤ delta → (c.eta v:ℂ)=1 := by
    intro v hv
    rw [c.eta_one v (by rwa [hcd]),ofReal_one]
  have hχ := liftShapeCutoff_continuous c.chi_smooth.continuous
  have hχ0 := liftShapeCutoff_zero (show c.chi 0=1 from c.chi_one.eq_of_nhds)
  have hχb := liftShapeCutoff_norm_le_one c.chi_range
  have hχs : ∀ x, liftShapeCutoff c.chi x ≠ 0 → ‖x‖ < R := by
    apply liftShapeCutoff_support
    intro t ht
    exact c.chi_support (subset_closure ht)
  have hpa := hPA (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχ0 hχb
    (fun x hx => (hχs x hx).trans_le (min_le_left _ _))
  have hpb := hPB (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχ0 hχb
    (fun x hx => (hχs x hx).trans_le (min_le_right _ _))
  have hleft := attach_local_odd_asymptotic c A k ((-I*localLeadingCoefficient A n k))
    (by simpa only [hcd] using hpa)
  have hright := attach_local_odd_asymptotic c A.swap k ((-I*localLeadingCoefficient A.swap n k))
    (by simpa only [hcd] using hpb)
  rw [localLeadingCoefficient_swap] at hright
  exact ⟨hL,U,c,hleft,hright⟩

theorem negative_selected_local_pair_lower_littleO {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) (hab : a ≠ b) (j : ℕ) (hj : j < derivativeOrder p) :
    let n := p-1
    let A := negativeSelectedRegularChart ha hb
    ∃ (U : Set (Fin n → ℝ)) (c : CompatibleYCutoffData n A.alpha A.beta U),
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n j A.theta c.leftWeight epsilon)
        (fun epsilon => (epsilon:ℂ)⁻¹) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n j A.theta c.rightWeight epsilon)
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let n := p-1
  let A := negativeSelectedRegularChart ha hb
  have hN : n+1=p := by dsimp [n]; have := hp.two_le; omega
  have hn : 1 ≤ n := by dsimp [n]; have := hp.two_le; omega
  have hNc : (n+1:ℂ)=((p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(n+1:ℂ)*(A.alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact negative_selected_lower_center_root hp ha
  have hBeta : exp (-(n+1:ℂ)*(A.beta:ℂ)*I)=1 := by
    rw [hNc]
    exact negative_selected_lower_center_root hp hb
  have hdegree : n-1+(n+1)*n = 2*derivativeOrder p-1 := by
    simpa only [hN,n] using odd_shape_radial_exponent (hp.odd_of_ne_two (by omega)) (by omega : 3 ≤ p)
  obtain ⟨Da,hDa,hA⟩ := actual_local_mean_lower_epsilon_limit hn hdegree hj A hAlpha hBeta
  obtain ⟨Db,hDb,hB⟩ := actual_local_mean_lower_epsilon_limit hn hdegree hj A.swap hBeta hAlpha
  have hCut : 0 < compatibleCutoffDeltaBound A.alpha A.beta :=
    negative_selected_cutoff_delta_bound_pos hp ha hb hab
  let D := min Da (min Db (compatibleCutoffDeltaBound A.alpha A.beta))
  have hD : 0 < D := lt_min hDa (lt_min hDb hCut)
  let delta := D/2
  have hd : 0 < delta := half_pos hD
  have hdD : delta ≤ D := (half_lt_self hD).le
  have hdA : delta ≤ Da := hdD.trans (min_le_left _ _)
  have hdB : delta ≤ Db := hdD.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdCut : delta ≤ compatibleCutoffDeltaBound A.alpha A.beta :=
    hdD.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Ra,hRa,hPA⟩ := hA delta hd hdA
  obtain ⟨Rb,hRb,hPB⟩ := hB delta hd hdB
  let R := min Ra Rb
  have hR : 0 < R := lt_min hRa hRb
  let U := sourceShapeBall n R
  obtain ⟨c,hcd,hcH⟩ := exists_compatibleYCutoffData_at_delta n A.alpha A.beta
    (sourceShapeBall_mem_nhds_zero n hR) (show (0:ℝ)<1 by norm_num) hd hdCut
  have hη : Continuous (fun v => (c.eta v:ℂ)) := Complex.continuous_ofReal.comp c.eta_smooth.continuous
  have hη1 : ∀ v : ℝ, |v| ≤ delta → (c.eta v:ℂ)=1 := by
    intro v hv
    rw [c.eta_one v (by rwa [hcd]),ofReal_one]
  have hχ := liftShapeCutoff_continuous c.chi_smooth.continuous
  have hχb := liftShapeCutoff_norm_le_one c.chi_range
  have hχs : ∀ x, liftShapeCutoff c.chi x ≠ 0 → ‖x‖ < R := by
    apply liftShapeCutoff_support
    intro t ht
    exact c.chi_support (subset_closure ht)
  have hpa := hPA (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχb
    (fun x hx => (hχs x hx).trans_le (min_le_left _ _))
  have hpb := hPB (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχb
    (fun x hx => (hχs x hx).trans_le (min_le_right _ _))
  have hleft := attach_local_odd_asymptotic c A j 0
    (by simpa only [hcd] using normalized_epsilon_limit_isLittleO hpa)
  have hright := attach_local_odd_asymptotic c A.swap j 0
    (by simpa only [hcd] using normalized_epsilon_limit_isLittleO hpb)
  exact ⟨U,c,by simpa only [mul_zero,sub_zero,CompatibleYCutoffData.leftWeight,n,A] using hleft,
    by simpa only [mul_zero,sub_zero,CompatibleYCutoffData.rightWeight,
      RegularChartData.swap,n,A] using hright⟩

theorem negative_selected_compatible_complement_bounded {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    {U : Set (Fin (p-1) → ℝ)}
    (c : CompatibleYCutoffData (p-1) (PrimeFamily.angle p a) (PrimeFamily.angle p b) U) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ‖(deriv^[j] (fun s => localizedDoubleFormFactor (p-1+1)
          (sourceRadialPair (negativeSelectedRegularChart ha hb).theta epsilon).1 s
          (fun u => c.remainder u.2)))
          (sourceRadialPair (negativeSelectedRegularChart ha hb).theta epsilon).2‖ ≤ C := by
  have hN : p-1+1=p := by have := hp.pos; omega
  have hW := odd_selected_compatible_complement_good hp c
  dsimp only at hW
  have hS : sourceS (exp (((negativeSelectedRegularChart ha hb).theta:ℂ)*I)) =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [sourceS,PrimeFamily.selectedPoint,negativeSelectedRegularChart,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      negative_selectedPoint_relation ha hb
  obtain ⟨e,he,hbound⟩ := negative_selected_complement_global_bound hp hp11 ha hb
    (negativeSelectedRegularChart ha hb).theta (negativeSelectedRegularChart ha hb).sin_theta_pos hS
    (compatibleDoubleComplement hN c) hW.1 hW.2.1 hW.2.2
  refine ⟨e,he,?_⟩
  intro j
  obtain ⟨C,hC,hB⟩ := hbound j
  refine ⟨C,hC,?_⟩
  intro epsilon heps hee
  have h := hB epsilon heps hee
  rw [← iteratedDeriv_eq_iterate] at h ⊢
  change ‖iteratedDeriv j (fun s => localizedDoubleFormFactor p
    (sourceRadialPair (negativeSelectedRegularChart ha hb).theta epsilon).1 s
    (fun u => reindexYWeight hN c.remainder u.2))
    (sourceRadialPair (negativeSelectedRegularChart ha hb).theta epsilon).2‖ ≤ C at h
  rw [localizedDoubleFormFactor_iteratedDeriv_y_reindex] at h
  exact h

end
end IsingBulk.HT.First.Regular
