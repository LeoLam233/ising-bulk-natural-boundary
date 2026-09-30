# Standalone manuscript and build

`manuscript.tex` embeds all sections, appendices and twelve bibliography entries. It has no external chapter or bibliography dependency. `manuscript.pdf` is the compiled v0.1-rc3 artifact; its SHA-256 is in the repository manifest. `LABEL_INDEX.json` maps all 65 labels to this PDF's numbering/pages.

Build with an existing Tectonic installation:

```sh
python scripts/build_paper.py --tectonic tectonic
```

The script also builds the two-page expert brief and writes only under `.local/`. It defaults to cached TeX resources; `--allow-resource-download` explicitly permits an existing Tectonic runtime to fetch missing resources. It does not install a runtime. Standard LaTeX packages used are visible in the source preambles. A normal pdflatex installation can also build the standalone source with repeated runs as needed for the table of contents.

During historical rc2 release preparation, the desktop native compiler could not find platform directories. The sources were preserved/opened in the editor and successfully exported using the already available cached Tectonic runtime with `--untrusted --only-cached`. No TeX installation or network download was performed for that build. The paper was rendered page by page and inspected; [rc2 layout/build records](../release/RC2_BUILD_QA.json) describe the result.

PDF bytes may vary with TeX version, font resources and creation timestamps. The frozen PDF hash identifies this artifact; rebuilding is expected to preserve content, not necessarily bytes. The rc2 manuscript preserved the mathematics of revision 8, as documented by the historical [rc1-to-rc2 source delta](../provenance/RC1_RC2_MANUSCRIPT_DELTA.json). The frozen mathematical candidate made the [W1 proof repairs](../provenance/W1_REPAIR_AUDIT.md); old delta and validation records remain historical. Its historical build and inspection results remain in [W1_CANDIDATE_VALIDATION.json](../release/W1_CANDIDATE_VALIDATION.json). Historical metadata-only release-prep build and mathematical-freeze results are in [RC3_RELEASE_PREP_VALIDATION.json](../release/RC3_RELEASE_PREP_VALIDATION.json). Its build uses portable Tectonic 0.17.0 with resources cached in the external work directory; the initial resource download is recorded separately from the final cached build.
