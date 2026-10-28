import IsingBulk.HT22.Transport.FieldNeighborhood.CovarianceBall

namespace IsingBulk.HT22.SharpCovarianceJets
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

def sourceCentered {N : ℕ} (t : ℂ) (v : Fin N → ℂ) (i : Fin N) : ℂ :=
  centeredAngleSum (fun a => regularInverse t (v a)) i


def SharpBounds {N : ℕ} (x : SourcePoint N) (C H d c η : ℝ) (m : ℕ) : Prop :=
  (∀ y∈ball x (η*d/(N:ℝ)^2),c*H*d^2/2≤‖sourceCovariance y.1 y.2‖) ∧
  ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCovariance z.1 z.2) x‖≤
    (cauchyJetConstant m*(36*C)^2/η^m)*(N:ℝ)^(2*m+2)*H*d^2/d^m ∧
  (∀i, ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCentered z.1 z.2 i) x‖≤
    (cauchyJetConstant m*(36*C)/η^m)*(N:ℝ)^(2*m+1)*H*d/d^m) ∧
  ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => (sourceCovariance z.1 z.2)⁻¹) x‖≤
    (cauchyJetConstant m*2/c/η^m)*(N:ℝ)^(2*m)/(H*d^(m+2))


theorem pair_ball_jets {N : ℕ} (hN : 0<N) (x : SourcePoint N)
    (C H d η : ℝ) (hC : 0<C) (hH : 0<H) (hd : 0<d) (hη : 0<η)
    (hU : ∀ y∈ball x (η*d/(N:ℝ)^2),∀i,
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (y.1,y.2 i))
    (hD : ∀ y∈ball x (η*d/(N:ℝ)^2),∀i l,
      ‖regularInverse y.1 (y.2 i)-regularInverse y.1 (y.2 l)‖≤C*H*d)
    (hE : ∀ y∈ball x (η*d/(N:ℝ)^2),∀i l,
      ‖sourceInverseV y.1 (y.2 i)-sourceInverseV y.1 (y.2 l)‖≤C*d)
    (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCovariance z.1 z.2) x‖≤
      (cauchyJetConstant m*C^2/η^m)*(N:ℝ)^(2*m+2)*H*d^2/d^m ∧
    ∀i, ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceCentered z.1 z.2 i) x‖≤
      (cauchyJetConstant m*C/η^m)*(N:ℝ)^(2*m+1)*H*d/d^m := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hR (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      AnalyticAt ℂ (fun z : SourcePoint N => sourceCovariance z.1 z.2) y := by
    exact (Finset.analyticAt_fun_sum Finset.univ (fun i _ =>
      Finset.analyticAt_fun_sum Finset.univ (fun l _ =>
        ((sourceInverseCoordinate_analyticAt y i (hU y hy i)).sub
          (sourceInverseCoordinate_analyticAt y l (hU y hy l))).mul
        ((sourceInverseVCoordinate_analyticAt y i (hU y hy i)).sub
          (sourceInverseVCoordinate_analyticAt y l (hU y hy l)))))).div_const
  have hG (i : Fin N) (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      AnalyticAt ℂ (fun z : SourcePoint N => sourceCentered z.1 z.2 i) y :=
    Finset.analyticAt_fun_sum Finset.univ (fun l _ =>
      (sourceInverseCoordinate_analyticAt y i (hU y hy i)).sub
        (sourceInverseCoordinate_analyticAt y l (hU y hy l)))
  have hRb (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      ‖sourceCovariance y.1 y.2‖≤C^2*(N:ℝ)^2*H*d^2 := by
    have hp (i l : Fin N) : ‖(regularInverse y.1 (y.2 i)-regularInverse y.1 (y.2 l))*
        (sourceInverseV y.1 (y.2 i)-sourceInverseV y.1 (y.2 l))‖≤(C*H*d)*(C*d) := by
      rw [norm_mul]
      exact mul_le_mul (hD y hy i l) (hE y hy i l) (norm_nonneg _) (by positivity)
    have hh := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin N))) =>
      (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun l (_ : l∈(Finset.univ : Finset (Fin N))) => hp i l))))
    change ‖(∑i,∑l,(regularInverse y.1 (y.2 i)-regularInverse y.1 (y.2 l))*
      (sourceInverseV y.1 (y.2 i)-sourceInverseV y.1 (y.2 l)))/2‖≤_
    rw [norm_div,Complex.norm_ofNat]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    nlinarith [show 0≤C^2*(N:ℝ)^2*H*d^2 by positivity]
  have hGb (i : Fin N) (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      ‖sourceCentered y.1 y.2 i‖≤C*(N:ℝ)*H*d := by
    have hh := (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l (_ : l∈(Finset.univ : Finset (Fin N))) => hD y hy i l))
    change ‖∑l,(regularInverse y.1 (y.2 i)-regularInverse y.1 (y.2 l))‖≤_
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_left_comm,mul_assoc] using hh
  constructor
  · have hh := analytic_iteratedFDeriv_center_bound _ x (η*d/(N:ℝ)^2)
      (C^2*(N:ℝ)^2*H*d^2) (by positivity) hR hRb m
    convert hh using 1
    rw [pow_add,pow_mul,div_pow,mul_pow]
    field_simp
  · intro i
    have hh := analytic_iteratedFDeriv_center_bound _ x (η*d/(N:ℝ)^2)
      (C*(N:ℝ)*H*d) (by positivity) (hG i) (hGb i) m
    convert hh using 1
    rw [pow_add,pow_mul,div_pow,mul_pow]
    field_simp


theorem inverse_jets_of_margin {N : ℕ} (hN : 0<N) (x : SourcePoint N)
    (H d c η : ℝ) (hH : 0<H) (hd : 0<d) (hc : 0<c) (hη : 0<η)
    (hU : ∀ y∈ball x (η*d/(N:ℝ)^2),∀i,
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (y.1,y.2 i))
    (hmargin : ∀ y∈ball x (η*d/(N:ℝ)^2),c*H*d^2/2≤‖sourceCovariance y.1 y.2‖)
    (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => (sourceCovariance z.1 z.2)⁻¹) x‖≤
      (cauchyJetConstant m*2/c/η^m)*(N:ℝ)^(2*m)/(H*d^(m+2)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hR (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      AnalyticAt ℂ (fun z : SourcePoint N => sourceCovariance z.1 z.2) y := by
    exact (Finset.analyticAt_fun_sum Finset.univ (fun i _ =>
      Finset.analyticAt_fun_sum Finset.univ (fun l _ =>
        ((sourceInverseCoordinate_analyticAt y i (hU y hy i)).sub
          (sourceInverseCoordinate_analyticAt y l (hU y hy l))).mul
        ((sourceInverseVCoordinate_analyticAt y i (hU y hy i)).sub
          (sourceInverseVCoordinate_analyticAt y l (hU y hy l)))))).div_const
  have hpos : 0<c*H*d^2/2 := by positivity
  have hne (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) : sourceCovariance y.1 y.2≠0 := by
    intro hz
    have hh := hmargin y hy
    rw [hz,norm_zero] at hh
    linarith
  have hb (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      ‖(sourceCovariance y.1 y.2)⁻¹‖≤2/(c*H*d^2) := by
    rw [norm_inv]
    have hh := inv_le_inv₀ (lt_of_lt_of_le hpos (hmargin y hy)) hpos |>.mpr (hmargin y hy)
    convert hh using 1; field_simp
  have hh := analytic_iteratedFDeriv_center_bound _ x (η*d/(N:ℝ)^2)
    (2/(c*H*d^2)) (by positivity) (fun y hy => (hR y hy).inv (hne y hy)) hb m
  convert hh using 1
  rw [pow_add,pow_mul,div_pow,mul_pow]
  field_simp

end
end IsingBulk.HT22.SharpCovarianceJets
