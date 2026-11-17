import IsingBulk.AnisoF002.Audit.RouteCheck

/-!
Finite C03 admission catalogue. Every entry was independently inspected in
its exact elaborated type and transitive stored type/value closure, bound to
unchanged historical source SHA-256 identities in support_manifest.json.
The expression hashes are additional deterministic change detectors; the
source SHA-256 verification remains mandatory. No namespace/module wildcard
is an admission rule, and no historical endpoint is included.
-/

namespace AnisoF002Audit.C03
open Lean

structure HistoricalRule where
  name : Name
  owner : Name
  kind : String
  typeHash : UInt64
  valueHash : Option UInt64
  group : String

/-- 54 generic Schur constants, 18 literal-domain constants (including two
compiler-generated Nat.AtLeastTwo numeral proofs), and five already admitted
spectral primitives; overlaps give 74 distinct exact names. -/
def historicalRules : Array HistoricalRule := #[
  { name := "IsingBulk.Anisotropic.HasDomainExtension".toName, owner := "IsingBulk.Anisotropic.Final.LocalExtension".toName, kind := "definition", typeHash := 2107289973, valueHash := some 3832340517, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.NaturalBoundaryOn".toName, owner := "IsingBulk.Anisotropic.Final.LocalExtension".toName, kind := "definition", typeHash := 477670872, valueHash := some 4087471351, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.geometryF1".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 3210013240, valueHash := some 2404057626, group := "baseline_spectral" },
  { name := "IsingBulk.Anisotropic.geometryF2".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 3210013240, valueHash := some 4181101961, group := "baseline_spectral" },
  { name := "IsingBulk.Anisotropic.inverseTemperature".toName, owner := "IsingBulk.Anisotropic.Final.AnalyticFactor".toName, kind := "definition", typeHash := 3981573739, valueHash := some 3313798523, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.inverseTemperature._proof_1".toName, owner := "IsingBulk.Anisotropic.Final.AnalyticFactor".toName, kind := "theorem", typeHash := 2547959801, valueHash := some 2289379630, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.omegaH".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 685996655, valueHash := some 798868679, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.omegaL".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 685996655, valueHash := some 2402284416, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceH".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 2611258793, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceL".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 464167890, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceP".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 1697674696, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.slicePInv".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 196901969, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceQ".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 504985644, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceQInv".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 2687296866, valueHash := some 3799520318, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceY".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 3468892319, valueHash := some 2365058031, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.sliceY._proof_1".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "theorem", typeHash := 2547959801, valueHash := some 2289379630, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.spectralA".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 3981573739, valueHash := some 3690806824, group := "baseline_spectral" },
  { name := "IsingBulk.Anisotropic.spectralS".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 612455587, valueHash := some 3193975476, group := "baseline_spectral" },
  { name := "IsingBulk.Anisotropic.spectralSet".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 685996655, valueHash := some 23895342, group := "literal_domain" },
  { name := "IsingBulk.Anisotropic.spectralT".toName, owner := "IsingBulk.Anisotropic.Geometry.Definitions".toName, kind := "definition", typeHash := 3981573739, valueHash := some 3237033788, group := "baseline_spectral" },
  { name := "IsingBulk.HT.First.pairProduct_append_unit".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 340072768, valueHash := some 3629381678, group := "generic_schur" },
  { name := "IsingBulk.HT.First.schur_even_list".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 1043661743, valueHash := some 4273382534, group := "generic_schur" },
  { name := "IsingBulk.HT.First.schur_ghost_entry".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 3027119225, valueHash := some 352594666, group := "generic_schur" },
  { name := "IsingBulk.HT.First.schur_odd_specialization".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 2425554405, valueHash := some 1578444299, group := "generic_schur" },
  { name := "IsingBulk.HT.First.schur_odd_specialization._proof_1_1".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 1869031038, valueHash := some 2186369620, group := "generic_schur" },
  { name := "IsingBulk.Schur.continuousAt_pairProduct".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "theorem", typeHash := 34760943, valueHash := some 2143505277, group := "generic_schur" },
  { name := "IsingBulk.Schur.continuousAt_pfaffian".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "theorem", typeHash := 3054537277, valueHash := some 3750694737, group := "generic_schur" },
  { name := "IsingBulk.Schur.eraseIdx_toFinset".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 1954273736, valueHash := some 697965151, group := "generic_schur" },
  { name := "IsingBulk.Schur.map_prod_eraseIdx".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 2032160561, valueHash := some 3684829726, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "definition", typeHash := 1653614140, valueHash := some 1215083095, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius_add".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 2406861692, valueHash := some 458833173, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius_add_ne_zero".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 2653848743, valueHash := some 2077382973, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius_inj".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 1885681448, valueHash := some 768000269, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius_kernel".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 2517870373, valueHash := some 2031208924, group := "generic_schur" },
  { name := "IsingBulk.Schur.mobius_ne_zero".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 2426362666, valueHash := some 423117297, group := "generic_schur" },
  { name := "IsingBulk.Schur.monic_ratio_partial_fractions".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "theorem", typeHash := 3607628064, valueHash := some 3223042837, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 765965244, valueHash := some 686932504, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct._f".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 790941849, valueHash := some 3057124604, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct.eq_1".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "theorem", typeHash := 132438309, valueHash := some 3147582730, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct.eq_2".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "theorem", typeHash := 563512805, valueHash := some 1075963059, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct.match_1".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 3435673807, valueHash := some 1035798657, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct_congr".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 236819873, valueHash := some 2350667057, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct_eraseIdx".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 1270869324, valueHash := some 1933658650, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct_map".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 1744927028, valueHash := some 2213020419, group := "generic_schur" },
  { name := "IsingBulk.Schur.pairProduct_weight".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 2045787914, valueHash := some 1365205438, group := "generic_schur" },
  { name := "IsingBulk.Schur.perturb".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "definition", typeHash := 2626977119, valueHash := some 1781298516, group := "generic_schur" },
  { name := "IsingBulk.Schur.perturb_continuous".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "theorem", typeHash := 495662338, valueHash := some 4064525784, group := "generic_schur" },
  { name := "IsingBulk.Schur.perturb_eventually_injective".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "theorem", typeHash := 2702061914, valueHash := some 3377701723, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 1701055239, valueHash := some 1159860798, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian._f".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 2064891173, valueHash := some 1314247678, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian.eq_2".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "theorem", typeHash := 1219082644, valueHash := some 3936010914, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian.eq_3".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "theorem", typeHash := 2026758410, valueHash := some 4229373550, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian.match_1".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 1936485647, valueHash := some 3412303518, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian.match_3".toName, owner := "IsingBulk.Algebra.SchurPfaffian".toName, kind := "definition", typeHash := 3634527956, valueHash := some 3422097920, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_congr".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 2795991455, valueHash := some 3336419572, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_map".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 63559470, valueHash := some 1364384316, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_xKernel_of_nodup".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 1157399979, valueHash := some 4288226490, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_xKernel_of_nodup._proof_1_1".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 4207537990, valueHash := some 584745013, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_xKernel_of_nodup._proof_1_2".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 4264295648, valueHash := some 1222066580, group := "generic_schur" },
  { name := "IsingBulk.Schur.pfaffian_xKernel_of_nodup._proof_1_3".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 3299411400, valueHash := some 1720377773, group := "generic_schur" },
  { name := "IsingBulk.Schur.schurWeight".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "definition", typeHash := 1974271556, valueHash := some 1561367870, group := "generic_schur" },
  { name := "IsingBulk.Schur.schurWeight.eq_1".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 2288419533, valueHash := some 217143145, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_fraction_of_nodup".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 166243392, valueHash := some 1407130865, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_fraction_specialization".toName, owner := "IsingBulk.Algebra.SchurContinuation".toName, kind := "theorem", typeHash := 318628428, valueHash := some 1614136704, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_partial_fractions".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "theorem", typeHash := 1943672128, valueHash := some 3550754126, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_residue_weight".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "theorem", typeHash := 1380816194, valueHash := some 3622773905, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_weighted_identity".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "theorem", typeHash := 780550818, valueHash := some 789866701, group := "generic_schur" },
  { name := "IsingBulk.Schur.schur_weights_sum".toName, owner := "IsingBulk.Algebra.SchurInterpolation".toName, kind := "theorem", typeHash := 431658180, valueHash := some 3462586368, group := "generic_schur" },
  { name := "IsingBulk.Schur.xKernel".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "definition", typeHash := 693042112, valueHash := some 3289234977, group := "generic_schur" },
  { name := "IsingBulk.Schur.xKernel.eq_1".toName, owner := "IsingBulk.Algebra.SchurMobius".toName, kind := "theorem", typeHash := 813568807, valueHash := some 2813419255, group := "generic_schur" },
  { name := "IsingBulk.Schur.xKernel_recurrence".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 3552108619, valueHash := some 1728011952, group := "generic_schur" },
  { name := "IsingBulk.Schur.xKernel_recurrence.match_1".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "definition", typeHash := 1936485647, valueHash := some 3412303518, group := "generic_schur" },
  { name := "IsingBulk.Schur.xKernel_skew".toName, owner := "IsingBulk.Algebra.SchurList".toName, kind := "theorem", typeHash := 1588968408, valueHash := some 354221682, group := "generic_schur" },
  { name := "_private.IsingBulk.HT.First.OddSchur.0.IsingBulk.HT.First.ghost_denominator".toName, owner := "IsingBulk.HT.First.OddSchur".toName, kind := "theorem", typeHash := 200626540, valueHash := some 1690185894, group := "generic_schur" }]

end AnisoF002Audit.C03
