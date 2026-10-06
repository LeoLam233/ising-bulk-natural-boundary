import IsingBulk.First.ActualLocalFullProfile
import IsingBulk.First.SourceAsymptoticAttachment
import IsingBulk.First.SourceLowerAttachment
import IsingBulk.First.SelectedYCutoffs
import IsingBulk.First.SwappedChartCoefficient

/-! Both actual ordered charts use one constructed delta and one fixed shape
cutoff. All local source asymptotics and lower-order bounds are instantiated. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology

theorem selected_local_pair_profile {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    let n := 2*p-1
    let k := (n+1)^2/2-1
    let A := selectedOrderedChart ha hb
    localLeadingCoefficient A n k ≠ 0 ∧
    ∃ (U : Set (Fin n → ℝ)) (c : CompatibleYCutoffData n A.alpha A.beta U),
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.leftWeight epsilon -
          (Real.sqrt epsilon:ℂ)⁻¹*localLeadingCoefficient A n k)
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.rightWeight epsilon -
          (Real.sqrt epsilon:ℂ)⁻¹*localLeadingCoefficient A n k)
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
      ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j < k → ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < e →
        ‖radialWeightedDerivative n j A.theta c.leftWeight epsilon‖ ≤ C ∧
        ‖radialWeightedDerivative n j A.theta c.rightWeight epsilon‖ ≤ C := by
  dsimp only
  let n := 2*p-1
  let A := selectedOrderedChart ha hb
  let k := (n+1)^2/2-1
  have hN : n+1=2*p := by dsimp [n]; have := hp.two_le; omega
  have hn : 1 ≤ n := by dsimp [n]; have := hp.two_le; omega
  have he : Even (n+1) := by rw [hN]; exact even_two_mul p
  have hNc : (n+1:ℂ)=((2*p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(n+1:ℂ)*(A.alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_lower_center_root hp ha
  have hBeta : exp (-(n+1:ℂ)*(A.beta:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_lower_center_root hp hb
  obtain ⟨hL,Da,hDa,hA⟩ := actual_local_full_profile hn A he hAlpha hBeta
  obtain ⟨_,Db,hDb,hB⟩ := actual_local_full_profile hn A.swap he hBeta hAlpha
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
  obtain ⟨Ra,ea,hRa,hea,hPA⟩ := hA delta hd hdA
  obtain ⟨Rb,eb,hRb,heb,hPB⟩ := hB delta hd hdB
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
  have hleft := c.attach_local_asymptotic A k (localLeadingCoefficient A n k)
    (by simpa only [hcd] using hpa.1)
  have hright := c.attach_local_asymptotic A.swap k (localLeadingCoefficient A.swap n k)
    (by simpa only [hcd] using hpb.1)
  rw [localLeadingCoefficient_swap] at hright
  obtain ⟨eA,heA,hba⟩ := c.attach_local_lower_bounds A k ea hea (by simpa only [hcd] using hpa.2)
  obtain ⟨eB,heB,hbb⟩ := c.attach_local_lower_bounds A.swap k eb heb (by simpa only [hcd] using hpb.2)
  refine ⟨hL,U,c,hleft,hright,min eA eB,lt_min heA heB,?_⟩
  intro j hj
  obtain ⟨Ca,hCa,hCaB⟩ := hba j hj
  obtain ⟨Cb,hCb,hCbB⟩ := hbb j hj
  refine ⟨Ca+Cb,add_pos hCa hCb,?_⟩
  intro epsilon heps hepsE
  have hLA := hCaB epsilon heps (hepsE.trans_le (min_le_left _ _))
  have hRB := hCbB epsilon heps (hepsE.trans_le (min_le_right _ _))
  exact ⟨hLA.trans (by linarith),hRB.trans (by linarith)⟩

end
end IsingBulk.First
