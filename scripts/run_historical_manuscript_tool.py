"""Run a preserved version-specific manuscript tool in a verified historical view."""
from pathlib import Path
import subprocess,sys
from eight_paper_paths import historical_root
v=historical_root(Path(__file__).resolve().parents[1]);tool=Path(sys.argv[1])
assert not tool.is_absolute() and '..' not in tool.parts
raise SystemExit(subprocess.run([sys.executable,str(v/tool),*sys.argv[2:]],cwd=v).returncode)
