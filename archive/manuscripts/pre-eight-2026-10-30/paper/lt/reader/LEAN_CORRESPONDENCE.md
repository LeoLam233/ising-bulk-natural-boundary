# LT source-level correspondence

The preserved independent review inspected actual C002 declarations, expanded predicates and relevant bodies. The literal source excerpts alongside this file retain16 inspected source files with line numbers and SHA-256 identities. All sources belong to the unchanged C002 archive SHA-256 `10f1ee8155740becee67717ba5ff8fa59bd94898b6903ec022c70ad527707f38`.

The actual terminal type in lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean is:

```lean
theorem theorem_nb_physical {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      (∀ x : ℝ, 16 < x → chi (x:ℂ) = rightPhysicalBulk J (x:ℂ)) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ¬ HasPhysicalBoundaryExtension J exteriorNormalizedBulk z) := by
  exact theorem_conditional_physical hJ hE1 hE2
    (fun _ _ _ hp hp11 ha hb hab => theorem_tail hp hp11 ha hb hab)

end
```

The normalized analytic `theorem_nb` internally discharges FIRST/lower-order/full absolute all-j tail obligations. The physical wrapper retains E1/E2 as explicit premises; E1 identifies the full physical even-order, all-site connected sum with the onsite term and pure-phase subtraction, while E2 is the real Yang magnetization input. The physical calibration conclusion is literally x>16; it is not expanded to an arbitrary complex chi equality. Inverse-temperature extension is on local sheets, not a single-valued global exterior beta. The selected obstruction is real C^k at the selected family. PropositionF.1 scalar/factorial conversion and the quantitative finite-prime all-arc calculation remain manuscript statements, not new formal exports.

The source-type/body correspondence and all110 editorial blocks were accepted in the original audit at that bounded scope. This continuation checked unchanged bytes plus the historical companion. No fresh Lean elaboration, compilation or kernel replay was executed or claimed.
