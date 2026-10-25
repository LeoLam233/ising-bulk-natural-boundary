import IsingBulk.Joint.Negative.AngularRoots

/-! Exact full-site angular coefficients for two independent complex couplings.
The onsite/full-lattice multiplier is retained. `unscaledAngularCoefficient`
uses the physical inside root, while `continuedAngularCoefficient` is its
locally analytic negative-edge continuation, including every odd order. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Anisotropic.RegularEdges MeasureTheory Set
open scoped BigOperators Topology

def complexAngularWeight {N : ℕ} (K : Coupling) (q : Fin N → ℂ) : ℂ :=
  (T K/S K)^(N.choose 2)*(S K)⁻¹^N *
    (∏ i, 2*transferRoot K (q i)/(1-transferRoot K (q i)^2)) *
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
      angularRootPair (transferRoot K (q i)) (transferRoot K (q j)) (q i) (q j))

def complexAngularDensity {N : ℕ} (K : Coupling) (q : Fin N → ℂ) : ℂ :=
  complexAngularWeight K q *
    ((1+∏ i,transferRoot K (q i))/(1-∏ i,transferRoot K (q i)))

def unscaledAngularCoefficient (n : ℕ) (K : Coupling) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
    multiAngleIntegral n (fun q => complexAngularDensity K
      (fun i => (physicalDependentAngles n q i:ℂ)))

theorem complexAngularDensity_joint_analyticAt {N : ℕ} (hN : 0<N)
    {K : Coupling} (hz : K∉spectralSet) (hS : S K≠0) (q : Fin N → ℝ) :
    AnalyticAt ℂ (fun p : Coupling × (Fin N → ℂ) => complexAngularDensity p.1 p.2)
      (K,fun i => (q i:ℂ)) := by
  let p := (K,fun i => (q i:ℂ))
  have dz : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => t.1) p := analyticAt_fst
  have dq (i : Fin N) : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => t.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dr (i : Fin N) : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => transferRoot t.1 (t.2 i)) p := by
    exact AnalyticAt.fun_comp_of_eq
      (f := fun t : Coupling × (Fin N → ℂ) => (t.1,t.2 i))
      (g := fun v : Coupling × ℂ => transferRoot v.1 v.2)
      (transferRoot_joint_analyticAt hz hS (q i)) (dz.prod (dq i)) rfl
  have hn (i : Fin N) := (transferRoot_bounds hz hS (q i)).2
  have hpair (i j : Fin N) : 1-transferRoot K (q i:ℂ)*transferRoot K (q j:ℂ)≠0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-∏ i, transferRoot K (q i:ℂ)≠0 :=
    one_sub_coordinateProduct_ne_zero hN hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  have dS : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => S t.1) p := Complex.analyticAt_sinh.comp (analyticAt_fst.comp dz)
  have dT : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => T t.1) p :=
    Complex.analyticAt_sinh.comp (analyticAt_snd.comp dz)
  unfold complexAngularDensity complexAngularWeight
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


def continuedAngularWeight {N : ℕ} (K : Coupling) (q : Fin N → ℂ) : ℂ :=
  (T K/S K)^(N.choose 2)*(S K)⁻¹^N *
    (∏ i, 2*continuedTransferRoot K (q i)/(1-continuedTransferRoot K (q i)^2)) *
    (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j),
      angularRootPair (continuedTransferRoot K (q i)) (continuedTransferRoot K (q j)) (q i) (q j))

def continuedAngularDensity {N : ℕ} (K : Coupling) (q : Fin N → ℂ) : ℂ :=
  continuedAngularWeight K q *
    ((1+∏ i,continuedTransferRoot K (q i))/(1-∏ i,continuedTransferRoot K (q i)))

def continuedAngularCoefficient (n : ℕ) (K : Coupling) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
    ∫ q in angleBox n, continuedAngularDensity K
      (fun i => (physicalDependentAngles n q i:ℂ))

theorem continuedAngularDensity_negative_joint_analyticAt {N : ℕ} (hN : Odd N)
    {b : ℝ} {K : Coupling} (hS : S K≠0)
    (hedge : A K+T K=(b : ℂ)*S K)
    (hb : |b|<1) (hB : 0<(-T K/S K).im)
    (q : Fin N → ℝ) (hq : ∑ i, q i=0) :
    AnalyticAt ℂ (fun p : Coupling × (Fin N → ℂ) => continuedAngularDensity p.1 p.2)
      (K,fun i => (q i:ℂ)) := by
  let p := (K,fun i => (q i:ℂ))
  have dz : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => t.1) p := analyticAt_fst
  have dq (i : Fin N) : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => t.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dr (i : Fin N) : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => continuedTransferRoot t.1 (t.2 i)) p := by
    exact AnalyticAt.fun_comp_of_eq
      (f := fun t : Coupling × (Fin N → ℂ) => (t.1,t.2 i))
      (g := fun v : Coupling × ℂ => continuedTransferRoot v.1 v.2)
      (continuedTransferRoot_negative_joint_analyticAt hS hedge hb hB (q i)) (dz.prod (dq i)) rfl
  have hpair (i j : Fin N) : 1-continuedTransferRoot K (q i:ℂ)*continuedTransferRoot K (q j:ℂ)≠0 :=
    continuedTransferRoot_negative_pair_ne_zero hS hedge hb hB (q i) (q j)
  have hZ : 1-∏ i, continuedTransferRoot K (q i:ℂ)≠0 :=
    by
      have hlt := continuedTransferRoot_odd_negative_product_lt_one hN hS hedge hb hB q hq
      intro he
      rw [(sub_eq_zero.mp he).symm, norm_one] at hlt
      exact lt_irrefl _ hlt
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  have dS : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => S t.1) p := Complex.analyticAt_sinh.comp (analyticAt_fst.comp dz)
  have dT : AnalyticAt ℂ (fun t : Coupling × (Fin N → ℂ) => T t.1) p :=
    Complex.analyticAt_sinh.comp (analyticAt_snd.comp dz)
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
    (K : Coupling) (q : Fin N → ℂ)
    (hi : ∀ i, 0<(transferW K (q i)).im) :
    continuedAngularDensity K q=complexAngularDensity K q := by
  unfold continuedAngularDensity continuedAngularWeight complexAngularDensity complexAngularWeight
  simp_rw [continuedTransferRoot_eq_transferRoot_of_im_pos (hi _)]


end
end IsingBulk.Joint.Negative
