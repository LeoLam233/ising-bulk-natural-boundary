import IsingBulk.First.SelectedLocalPair
import IsingBulk.First.SelectedComplementBound
import IsingBulk.First.LocalizedAnalytic

/-! The two constructed local source integrals and the actual complementary
integral are assembled. All three s-derivatives use the same fixed evaluation radius. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter IsingBulk.Branch
open scoped Topology

theorem first_upper_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    let n := 2*p-1
    let k := (n+1)^2/2-1
    let A := selectedOrderedChart ha hb
    let L := localLeadingCoefficient A n k
    L ≠ 0 ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => iteratedDeriv k (upperFormFactor (n+1)) (radialParameter A.theta epsilon)-
          (Real.sqrt epsilon:ℂ)⁻¹*(2*L))
        (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) ∧
      ∃ e : ℝ, 0 < e ∧ ∀ j : ℕ, j < k → ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < e →
        ‖iteratedDeriv j (upperFormFactor (n+1)) (radialParameter A.theta epsilon)‖ ≤ C := by
  dsimp only
  let n := 2*p-1
  let k := (n+1)^2/2-1
  let A := selectedOrderedChart ha hb
  obtain ⟨hL,U,c,hLeft,hRight,eL,heL,hLocal⟩ := selected_local_pair_profile hp ha hb hab
  obtain ⟨eC,heC,hComplement⟩ := selected_compatible_complement_bounded hp hp11 ha hb c
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin A.sin_theta_pos
  have hSplit (epsilon : ℝ) (heps : 0 < epsilon) (hepsd : epsilon < d) (j : ℕ) :
      iteratedDeriv j (upperFormFactor (n+1)) (radialParameter A.theta epsilon) =
        radialWeightedDerivative n j A.theta c.leftWeight epsilon +
        radialWeightedDerivative n j A.theta c.rightWeight epsilon +
        iteratedDeriv j (fun s => localizedDoubleFormFactor (n+1)
          (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
          (sourceRadialPair A.theta epsilon).2 := by
    have hr : 0 < (sourceRadialPair A.theta epsilon).1 := Real.exp_pos _
    have hr1 : (sourceRadialPair A.theta epsilon).1 < 1 := by
      change Real.exp (-(Real.sin A.theta/4)*epsilon) < 1
      rw [Real.exp_lt_one_iff]
      nlinarith [mul_pos A.sin_theta_pos heps]
    have hm := (hMargin epsilon heps hepsd (radialParameter A.theta epsilon)
      (by simpa using mul_pos (div_pos A.sin_theta_pos (by norm_num) : 0 < Real.sin A.theta/16) heps)).2
    have hs := upperFormFactor_iteratedDeriv_split (n+1) (Nat.succ_pos n) j hr hr1 hm
      c.leftWeight c.rightWeight c.left_smooth.continuous c.right_smooth.continuous
    simpa only [radialWeightedDerivative,sourceRadialPair,CompatibleYCutoffData.leftWeight,
      CompatibleYCutoffData.rightWeight,CompatibleYCutoffData.remainder,fixedYComplement] using hs
  obtain ⟨Ck,_,hCk⟩ := hComplement k
  have hComp : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => iteratedDeriv k (fun s => localizedDoubleFormFactor (n+1)
        (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
        (sourceRadialPair A.theta epsilon).2)
      (fun epsilon => (Real.sqrt epsilon:ℂ)⁻¹) := by
    apply bounded_radial_term_isLittleO heC
    intro epsilon hp he
    simpa only [iteratedDeriv_eq_iterate,n,A] using! (hCk epsilon hp he)
  refine ⟨hL,?_,?_⟩
  · apply ((hLeft.add hRight).add hComp).congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon hp he
    rw [hSplit epsilon hp he k]
    ring
  · refine ⟨min eL (min eC d),lt_min heL (lt_min heC hd),?_⟩
    intro j hj
    obtain ⟨Cl,hCl,hcl⟩ := hLocal j hj
    obtain ⟨Cc,hCc,hcc⟩ := hComplement j
    refine ⟨2*Cl+Cc,by positivity,?_⟩
    intro epsilon hp he
    have hl := hcl epsilon hp (he.trans_le (min_le_left _ _))
    have hc : ‖iteratedDeriv j (fun s => localizedDoubleFormFactor (n+1)
        (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
        (sourceRadialPair A.theta epsilon).2‖ ≤ Cc := by
      simpa only [iteratedDeriv_eq_iterate,n,A] using! (hcc epsilon hp
        (he.le.trans ((min_le_right _ _).trans (min_le_left _ _))))
    rw [hSplit epsilon hp (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) j]
    have hll : ‖radialWeightedDerivative n j A.theta c.leftWeight epsilon‖ ≤ Cl := by
      simpa only [n,A] using hl.1
    have hlr : ‖radialWeightedDerivative n j A.theta c.rightWeight epsilon‖ ≤ Cl := by
      simpa only [n,A] using hl.2
    let x : ℂ := radialWeightedDerivative n j A.theta c.leftWeight epsilon
    let y : ℂ := radialWeightedDerivative n j A.theta c.rightWeight epsilon
    let z : ℂ := iteratedDeriv j (fun s => localizedDoubleFormFactor (n+1)
      (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
      (sourceRadialPair A.theta epsilon).2
    change ‖x+y+z‖ ≤ 2*Cl+Cc
    change ‖x‖ ≤ Cl at hll
    change ‖y‖ ≤ Cl at hlr
    change ‖z‖ ≤ Cc at hc
    calc
      ‖x+y+z‖ ≤ ‖x+y‖+‖z‖ := norm_add_le (x+y) z
      _ ≤ (‖x‖+‖y‖)+‖z‖ := by linarith only [norm_add_le x y]
      _ ≤ Cl+Cl+Cc := add_le_add (add_le_add hll hlr) hc
      _ = 2*Cl+Cc := by ring


end
end IsingBulk.First
