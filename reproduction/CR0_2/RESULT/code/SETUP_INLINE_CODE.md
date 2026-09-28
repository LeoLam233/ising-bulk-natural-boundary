# Retrospective copy of initial inline setup code

This is operational code executed before live logging was initialized. It was not saved as a `.py` file at execution time; the following copy is preserved retrospectively from the visible action. It was **not rerun** merely to manufacture a later execution record. Exact task-start and first-read timestamps remain unknown.

The first action executed the following with `python -B`:

```python
from pathlib import Path
import zipfile
p=Path('[LOCAL_PATH_REDACTED]
with zipfile.ZipFile(p) as z:
    names=z.namelist()
    print('\n'.join(names))
    root=Path('[LOCAL_PATH_REDACTED]
    root.mkdir(exist_ok=True)
    for n in names:
        dest=(root/n).resolve()
        if not dest.is_relative_to(root.resolve()):
            raise RuntimeError('Unsafe archive path')
    z.extractall(root)
    starts=[root/n for n in names if n.endswith('INPUT/START_HERE.md')]
    if len(starts)!=1:
        raise RuntimeError(f'Expected one START_HERE, found {starts}')
    print('\n===== START_HERE.md =====\n')
    print(starts[0].read_text())
```

The second action changed directory to `INPUT/` and displayed, in this order, `TASK.md`, `CONVENTIONS.md`, `OUTPUT_CONTRACT.md`, and `references/README.md` using `cat` in a shell loop.

The third action used Python's `Path.mkdir(exist_ok=False)` to create the fresh `RUN_OUTPUT/`, then `code/`, `evidence/`, and `pdf_views/`. It sampled `datetime.now(timezone.utc)`, `sys.version`, and `platform.platform()`, formed a run ID from that clock reading and `uuid.uuid4().hex[:8]`, wrote `evidence/setup.json`, and initialized the action log with the two explicitly retrospective setup entries, the live-log initialization, the runtime observation, and the disclosed mandatory procedural-skill read. The actual sampled values are retained in `evidence/setup.json`; this paragraph is not an independently timed execution record.

That action then displayed `[LOCAL_PATH_REDACTED]`, as required by a higher-priority environment instruction. This outside-packet procedural read is explicitly classified as a deviation, not hidden as an input read. No Ising research claim came from it. No other PDF skill file or external rendering script was read; the supplied PDF pages were subsequently rendered by the self-written `render_sources.py` using the installed PyMuPDF runtime.

All substantive research programs are preserved as actual `.py` files in this directory, with their original and refined outputs under `evidence/`. Inline shell wrappers that wrote files, printed supplied text, or made small report edits are described by the access/action log and visible-action index, rather than presented as a fictitious complete exported terminal transcript.
