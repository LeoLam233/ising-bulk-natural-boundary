import IsingBulk.Anisotropic.Geometry.RealGeometryAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

theorem rectangle_sign_criterion (h c H C t q T Q : ℝ)
    (hh : 0<h) (hH : 0<H) (hcpos : 0<c) (hCpos : 0<C)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : q^2+t^2=1) (hT : Q^2+T^2=1)
    (hq : q ≠ 0 ∨ Q ≠ 0) :
    ((c*t*T*Q-h*H*C*q)^2 ≤ (h*C*t*Q-c*H*q*T)^2 ∧
      (h*c*H*Q-C*t*q*T)^2 ≤ (h*C*t*Q-c*H*q*T)^2) ↔
    (C^2*t^2-c^2*H^2)*(c^2*T^2-h^2*C^2) ≤ 0 := by
  have ha := sq_pos_of_pos hh
  have hb := sq_pos_of_pos hH
  have halpha : 0 < H^2+Q^2 := by positivity
  have hbeta : 0 < h^2+q^2 := by positivity
  have hd : h^2*H^2 < (H^2+Q^2)*(h^2+q^2) := by
    rcases hq with hq | hQ
    · nlinarith [mul_pos hb (sq_pos_of_ne_zero hq), mul_nonneg (sq_nonneg h) (sq_nonneg Q),
        mul_nonneg (sq_nonneg q) (sq_nonneg Q)]
    · nlinarith [mul_pos ha (sq_pos_of_ne_zero hQ), mul_nonneg (sq_nonneg H) (sq_nonneg q),
        mul_nonneg (sq_nonneg q) (sq_nonneg Q)]
  have he := edge_auxiliary_identities h c H C t q T Q hc hC ht hT
  have hu : C^2*((c*t*T*Q-h*H*C*q)^2-(h*C*t*Q-c*H*q*T)^2) =
      (c^2*T^2-h^2*C^2)*((H^2+Q^2)*(C^2*t^2-c^2*H^2)-H^2*(c^2*T^2-h^2*C^2)) := by
    rw [numeratorU_factor]
    linear_combination (c^2*T^2-h^2*C^2)*he.1
  have hv : c^2*((h*c*H*Q-C*t*q*T)^2-(h*C*t*Q-c*H*q*T)^2) =
      -(C^2*t^2-c^2*H^2)*(h^2*(C^2*t^2-c^2*H^2)-(h^2+q^2)*(c^2*T^2-h^2*C^2)) := by
    rw [numeratorV_factor]
    linear_combination -(C^2*t^2-c^2*H^2)*he.2
  rw [← cone_inequalities_iff ha hb halpha hbeta hd, ← hu, ← hv]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨mul_nonpos_of_nonneg_of_nonpos (sq_nonneg C) (sub_nonpos.mpr h1),
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (sub_nonpos.mpr h2)⟩
  · rintro ⟨h1,h2⟩
    exact ⟨sub_nonpos.mp (nonpos_of_mul_nonpos_right h1 (sq_pos_of_pos hCpos)),
      sub_nonpos.mp (nonpos_of_mul_nonpos_right h2 (sq_pos_of_pos hcpos))⟩

end
end IsingBulk.Anisotropic
