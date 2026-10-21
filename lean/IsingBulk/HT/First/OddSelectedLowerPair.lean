import IsingBulk.HT.First.OddActualLowerLocalLimit
import IsingBulk.HT.First.OddSelectedLocalPair

/-! The actual two ordered local lower jets are o(ε⁻¹), with a constructed
compatible cutoff for each derivative order. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter Set IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem odd_selected_local_pair_lower_littleO {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) (j : ℕ) (hj : j < derivativeOrder p) :
    let n := p-1
    let A := selectedOrderedChart ha hb
    ∃ (U : Set (Fin n → ℝ)) (c : CompatibleYCutoffData n A.alpha A.beta U),
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n j A.theta c.leftWeight epsilon)
        (fun epsilon => (epsilon:ℂ)⁻¹) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n j A.theta c.rightWeight epsilon)
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let n := p-1
  let A := selectedOrderedChart ha hb
  have hN : n+1=p := by dsimp [n]; have := hp.two_le; omega
  have hn : 1 ≤ n := by dsimp [n]; have := hp.two_le; omega
  have hNc : (n+1:ℂ)=((p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(n+1:ℂ)*(A.alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_odd_lower_center_root hp ha
  have hBeta : exp (-(n+1:ℂ)*(A.beta:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_odd_lower_center_root hp hb
  have hdegree : n-1+(n+1)*n = 2*derivativeOrder p-1 := by
    simpa only [hN,n] using odd_shape_radial_exponent (hp.odd_of_ne_two (by omega)) (by omega : 3 ≤ p)
  obtain ⟨Da,hDa,hA⟩ := actual_local_mean_lower_epsilon_limit hn hdegree hj A hAlpha hBeta
  obtain ⟨Db,hDb,hB⟩ := actual_local_mean_lower_epsilon_limit hn hdegree hj A.swap hBeta hAlpha
  have hCut : 0 < compatibleCutoffDeltaBound A.alpha A.beta :=
    selected_cutoff_delta_bound_pos hp ha hb hab
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
      OrderedChartData.swap,n,A] using hright⟩

end
end IsingBulk.HT.First
