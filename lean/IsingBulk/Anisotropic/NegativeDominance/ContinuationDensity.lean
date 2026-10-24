import IsingBulk.Anisotropic.NegativeDominance.ContinuationRoots

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges MeasureTheory
open scoped BigOperators Topology

def continuedAngularWeight {N : ℕ} (lam : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℂ :=
  (spectralT lam z/spectralS z)^(N.choose 2)*(spectralS z)⁻¹^N *
    (∏ i, 2*continuedTransferRoot lam z (q i)/(1-continuedTransferRoot lam z (q i)^2)) *
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
      angularRootPair (continuedTransferRoot lam z (q i)) (continuedTransferRoot lam z (q j)) (q i) (q j))

def continuedAngularDensity {N : ℕ} (lam : ℝ) (z : ℂ) (q : Fin N → ℂ) : ℂ :=
  continuedAngularWeight lam z q *
    ((1+∏ i,continuedTransferRoot lam z (q i))/(1-∏ i,continuedTransferRoot lam z (q i)))

def continuedAngularCoefficient (n : ℕ) (lam : ℝ) (z : ℂ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
    ∫ q in angleBox n, continuedAngularDensity lam z
      (fun i => (physicalDependentAngles n q i:ℂ))

theorem continuedAngularDensity_negative_joint_analyticAt {N : ℕ} (hN : Odd N)
    {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im)
    (q : Fin N → ℝ) (hq : ∑ i, q i=0) :
    AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => continuedAngularDensity lam p.1 p.2)
      (z,fun i => (q i:ℂ)) := by
  let p := (z,fun i => (q i:ℂ))
  have dz : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => t.1) p := analyticAt_fst
  have dq (i : Fin N) : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => t.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dr (i : Fin N) : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => continuedTransferRoot lam t.1 (t.2 i)) p := by
    exact AnalyticAt.fun_comp_of_eq
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i))
      (g := fun v : ℂ × ℂ => continuedTransferRoot lam v.1 v.2)
      (continuedTransferRoot_negative_joint_analyticAt hS hedge hb hB (q i)) (dz.prod (dq i)) rfl
  have hpair (i j : Fin N) : 1-continuedTransferRoot lam z (q i:ℂ)*continuedTransferRoot lam z (q j:ℂ)≠0 :=
    continuedTransferRoot_negative_pair_ne_zero hS hedge hb hB (q i) (q j)
  have hZ : 1-∏ i, continuedTransferRoot lam z (q i:ℂ)≠0 :=
    by
      have hlt := continuedTransferRoot_odd_negative_product_lt_one hN hS hedge hb hB q hq
      intro he
      rw [(sub_eq_zero.mp he).symm, norm_one] at hlt
      exact lt_irrefl _ hlt
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  have dS : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => spectralS t.1) p := Complex.analyticAt_sinh.comp dz
  have dT : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => spectralT lam t.1) p :=
    Complex.analyticAt_sinh.comp (analyticAt_const.mul dz)
  unfold continuedAngularDensity continuedAngularWeight
  refine (((((dT.div dS hS).pow _).mul ((dS.inv hS).pow _)).mul ?_).mul ?_).mul
    ((analyticAt_const.add dZ).div (analyticAt_const.sub dZ) hZ)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    apply (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod
    intro j _
    exact ((((analyticAt_const.mul (dr i)).mul (dr j)).mul
      ((Complex.analyticAt_sin.comp (((dq i).sub (dq j)).div_const)).pow 2))).div
        ((analyticAt_const.sub ((dr i).mul (dr j))).pow 2) (pow_ne_zero _ (hpair i j))


theorem continuedAngularDensity_eq_complexAngularDensity_of_im_pos {N : ℕ}
    (lam : ℝ) (z : ℂ) (q : Fin N → ℂ)
    (hi : ∀ i, 0<(transferW lam z (q i)).im) :
    continuedAngularDensity lam z q=complexAngularDensity lam z q := by
  unfold continuedAngularDensity continuedAngularWeight complexAngularDensity complexAngularWeight
  simp_rw [continuedTransferRoot_eq_transferRoot_of_im_pos (hi _)]

end
end IsingBulk.Anisotropic.NegativeDominance
