#!/usr/bin/env python3
"""Prepare or execute one explicitly requested Linux build/trust/replay sequence.

Default behavior is read-only preflight plus a command plan. No Lean build,
axiom traversal, endpoint elaboration, or replay occurs without --execute.
This is verification infrastructure, not a completed adversarial audit round.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
from preflight import APPROVED_AXIOMS, PreflightError, clean_environment, require, snapshot

IDENTITY_KEYS = ("PROOF_CRITICAL_PAYLOAD_ID", "VERIFICATION_INPUT_ID", "RUNTIME_ID")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def new_json(path: Path, value: dict) -> None:
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def same_inputs(before: dict, after: dict) -> None:
    for key in IDENTITY_KEYS:
        require(before[key] == after[key], f"Candidate input changed: {key}")


def require_clean_project(project: Path) -> None:
    """Require a fresh source-only project, without deleting or moving anything."""
    lake_dir = project / ".lake"
    require(not lake_dir.is_symlink(), "Fresh candidate .lake must not be a symlink")
    if lake_dir.exists():
        unexpected = sorted(p.name for p in lake_dir.iterdir() if p.name != "packages")
        require(not unexpected,
                "Fresh candidate must have no project Lake outputs/configuration cache; "
                f"found .lake entries {unexpected}. Use a fresh source-only directory.")
    for source in list((project / "IsingBulk").rglob("*.lean")) + [project / "IsingBulk.lean", project / "Audit.lean"]:
        for suffix in (".olean", ".olean.server", ".olean.private", ".ilean"):
            require(not source.with_suffix(suffix).exists(), f"Stale sibling output: {source.with_suffix(suffix)}")


def endpoint_source(endpoints: list[dict], project: Path) -> str:
    checks = "\n".join("#check " + entry["declaration"] for entry in endpoints)
    interface_path = project / "control_packet/continuation/fixtures/PositiveInterfaces.lean"
    interface_source = interface_path.read_text()
    require(interface_source.startswith("import IsingBulk\n"), "Unexpected literal interface fixture header")
    interface_source = interface_source.removeprefix("import IsingBulk\n")
    pairs = ",\n    ".join("(`" + entry["declaration"] + ", `" + entry["module"] + ")"
                            for entry in endpoints)
    return f'''import IsingBulk
import Lean.Util.CollectAxioms

set_option pp.fullNames true

{checks}

-- Exact expanded principal proposition checks, bound by verification identity.
{interface_source}

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array (Name × Name) := #[
    {pairs}]
  for (name, expectedModule) in expected do
    let some info := env.find? name
      | throwError "Missing final endpoint: {{name}}"
    unless info.isTheorem && !info.isUnsafe do
      throwError "Endpoint is not a safe theorem: {{name}}"
    let some moduleIdx := env.getModuleIdxFor? name
      | throwError "Missing module origin: {{name}}"
    let actualModule := env.header.moduleNames[moduleIdx.toNat]!
    unless actualModule == expectedModule do
      throwError "Wrong endpoint origin: {{name}}; expected {{expectedModule}}; got {{actualModule}}"
    logInfo m!"ENDPOINT_ORIGIN: {{name}}; MODULE: {{actualModule}}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unapproved endpoint axiom: {{name}}; {{ax}}"
    logInfo m!"ENDPOINT_AXIOMS: {{name}}; AXIOMS: {{axioms}}"
  logInfo m!"ENDPOINT_CHECK_PASSED: {{expected.size}}"
'''


def run_stage(name: str, argv: list[str], project: Path, logs: Path, env: dict[str, str]) -> dict:
    """Capture exact argv, real wait status and Linux wait4 resource usage."""
    record = {"stage": name, "argv": argv, "cwd": str(project), "started_utc": now(),
              "environment": {key: env.get(key) for key in ("LEAN_NUM_THREADS", "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE", "LAKE_CACHE_DIR", "LAKE_CONFIG")},
              "status": "STARTED"}
    new_json(logs / f"{name}.command.json", record)
    started = time.monotonic()
    interrupted = False
    with (logs / f"{name}.stdout.log").open("x") as out, (logs / f"{name}.stderr.log").open("x") as err:
        try:
            process = subprocess.Popen(argv, cwd=project, env=env, stdout=out, stderr=err,
                                       start_new_session=True)
        except OSError as exc:
            record.update({"finished_utc": now(), "elapsed_seconds": time.monotonic() - started,
                           "status": "SPAWN_FAILED", "exit_code": None, "error": str(exc)})
            new_json(logs / f"{name}.result.json", record)
            raise
        try:
            _, status, usage = os.wait4(process.pid, 0)
        except KeyboardInterrupt:
            interrupted = True
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            deadline = time.monotonic() + 5
            while True:
                waited, status, usage = os.wait4(process.pid, os.WNOHANG)
                if waited:
                    break
                if time.monotonic() >= deadline:
                    os.killpg(process.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                time.sleep(0.05)
        process.returncode = os.waitstatus_to_exitcode(status)
    record.update({"finished_utc": now(), "elapsed_seconds": time.monotonic() - started,
                   "exit_code": process.returncode, "interrupted": interrupted,
                   "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
                   "max_rss_kib_wait4": usage.ru_maxrss,
                   "rss_scope": "Linux wait4 maximum child/descendant RSS, not summed concurrent tree RSS",
                   "status": "PROCESS_EXIT_ZERO" if process.returncode == 0 and not interrupted else "PROCESS_FAILED"})
    new_json(logs / f"{name}.result.json", record)
    require(process.returncode == 0 and not interrupted,
            f"Stage {name} failed/interrupted (exit {process.returncode}); see {logs}")
    return record


def inspect_audit(logs: Path, source_references: list[dict]) -> int:
    text = (logs / "02_axiom_audit.stdout.log").read_text()
    unions = re.findall(r"AXIOM UNION:\s*\[([^\]]*)\]", text)
    counts = re.findall(r"AUDIT PASSED:\s*(\d+) kernel-safe project declarations", text)
    require(len(unions) == len(counts) == 1, "Missing/ambiguous Audit success markers")
    found = {name.strip() for name in unions[0].split(",") if name.strip()}
    require(found == APPROVED_AXIOMS, f"Unexpected Audit axiom union: {found}")
    require(int(counts[0]) > 0, "Audit enumerated no project declarations")
    actual = set(re.findall(r"^DECLARATION:\s*([^;\r\n]+);\s*AXIOMS:", text, re.M))
    expected = {entry["target"] for entry in source_references if entry["kind"] == "declaration"}
    require(expected <= actual,
            f"Ledger declaration references absent from actual Audit output: {sorted(expected-actual)}")
    return int(counts[0])


def inspect_endpoints(logs: Path, endpoints: list[dict]) -> None:
    text = (logs / "03_endpoints.stdout.log").read_text()
    require(re.findall(r"ENDPOINT_CHECK_PASSED:\s*(\d+)", text) == [str(len(endpoints))],
            "Endpoint check did not confirm the complete expected list")
    for entry in endpoints:
        require(f"ENDPOINT_ORIGIN: {entry['declaration']}; MODULE: {entry['module']}" in text,
                f"Missing exact endpoint origin log: {entry['declaration']}")
        require(f"ENDPOINT_AXIOMS: {entry['declaration']}; AXIOMS:" in text,
                f"Missing exact endpoint axiom log: {entry['declaration']}")


def command_plan(lean_bin: Path) -> dict[str, list[str]]:
    lake = str(lean_bin / "lake")
    return {
        "01_clean_project_build": [lake, "-f", "lakefile.toml", "--no-cache", "build", "IsingBulk"],
        "02_axiom_audit": [lake, "-f", "lakefile.toml", "env", str(lean_bin / "lean"), "-DwarningAsError=true", "Audit.lean"],
        "03_endpoints": [lake, "-f", "lakefile.toml", "env", str(lean_bin / "lean"), "-DwarningAsError=true", "<new-log-directory>/EndpointCheck.lean"],
        "03b_math_controls": [sys.executable, "control_packet/continuation/run_lean_controls.py", "--lean-bin-dir", str(lean_bin)],
        "04_kernel_replay": [lake, "-f", "lakefile.toml", "env", str(lean_bin / "leanchecker"), "--fresh", "--verbose", "IsingBulk"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=HERE.parents[1])
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--logs", type=Path, help="New log directory, created only for --execute")
    parser.add_argument("--approved-preflight", type=Path,
                        help="Previously inspected preflight JSON; all three input identities must match")
    parser.add_argument("--execute", action="store_true", help="Explicitly start the heavy sequence")
    parser.add_argument("--threads", type=int, default=1, help="LEAN_NUM_THREADS, default 1")
    args = parser.parse_args()
    stages = []
    logs = None
    try:
        require(args.threads > 0, "--threads must be positive")
        project, lean_bin = args.project.resolve(), args.lean_bin.resolve()
        initial = snapshot(project, lean_bin)
        lake = str(lean_bin / "lake")
        plan = command_plan(lean_bin)
        if not args.execute:
            print(json.dumps({"status": "PLAN_ONLY_NO_BUILD_OR_REPLAY", "commands": plan,
                              **{key: initial[key] for key in IDENTITY_KEYS}}, indent=2))
            return 0
        require(args.logs is not None and args.approved_preflight is not None,
                "--execute requires --logs and --approved-preflight")
        approved = json.loads(args.approved_preflight.read_text())
        require(approved.get("status") == "PREFLIGHT_PASS_NOT_BUILD_OR_REPLAY",
                "The supplied preflight receipt did not pass")
        same_inputs(approved, initial)
        require_clean_project(project)
        requested_logs = args.logs.resolve()
        require(not requested_logs.exists(), "Log directory already exists; it will not be reused or overwritten")
        require(not requested_logs.is_relative_to(HERE), "Keep generated logs outside the verification source directory")
        requested_logs.mkdir(parents=True, exist_ok=False)
        logs = requested_logs
        new_json(logs / "preflight.before.json", initial)
        new_json(logs / "sequence.started.json", {"started_utc": now(), "project": str(project),
                 "lean_bin": str(lean_bin), "threads": args.threads,
                 "clean_project_outputs_absent": True, "commands": plan,
                 **{key: initial[key] for key in IDENTITY_KEYS}})
        endpoint_file = logs / "EndpointCheck.lean"
        with endpoint_file.open("x", encoding="utf-8") as stream:
            stream.write(endpoint_source(initial["endpoints"], project))
        plan["03_endpoints"][-1] = str(endpoint_file)
        env = clean_environment(lean_bin)
        env["LEAN_NUM_THREADS"] = str(args.threads)
        declaration_count = None
        for name, argv in plan.items():
            same_inputs(initial, snapshot(project, lean_bin))
            print(json.dumps({"stage": name, "status": "STARTING", "utc": now()}), flush=True)
            result = run_stage(name, argv, project, logs, env)
            print(json.dumps({"stage": name, "status": result["status"],
                              "elapsed_seconds": result["elapsed_seconds"]}), flush=True)
            stages.append(result)
            if name == "02_axiom_audit":
                declaration_count = inspect_audit(logs, initial["source_references"])
            elif name == "03_endpoints":
                inspect_endpoints(logs, initial["endpoints"])
            elif name == "04_kernel_replay":
                replay_log = (logs / f"{name}.stdout.log").read_text()
                require("replaying IsingBulk with --fresh" in replay_log,
                        "Checker did not confirm the requested fresh root replay")
            same_inputs(initial, snapshot(project, lean_bin))
        final = snapshot(project, lean_bin)
        same_inputs(initial, final)
        new_json(logs / "preflight.after.json", final)
        result = {"status": "CHECK_SEQUENCE_PASSED_NOT_AUDIT_ROUND", "finished_utc": now(),
                  **{key: initial[key] for key in IDENTITY_KEYS}, "stages": stages,
                  "production_module_count": initial["production_module_count"],
                  "audited_safe_declaration_count": declaration_count,
                  "endpoint_count": initial["endpoint_count"],
                  "axiom_union": sorted(APPROVED_AXIOMS), "fresh_kernel_replay_exit": 0,
                  "final_candidate_gate": False, "audit_round_completed": False,
                  "scope": "Clean project build, axiom traversal, exact endpoint type/origin/axiom checks, official fresh kernel replay. No semantic/mutation/CI audit claims."}
        new_json(logs / "sequence.result.json", result)
        print(json.dumps({"status": result["status"], "logs": str(logs)}, indent=2))
        return 0
    except (PreflightError, OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        if logs is not None and logs.is_dir() and not (logs / "sequence.result.json").exists():
            new_json(logs / "sequence.result.json", {"status": "CHECK_SEQUENCE_FAILED", "finished_utc": now(),
                     "error": str(exc), "completed_processes": stages,
                     "final_candidate_gate": False, "audit_round_completed": False})
        print(f"CHECK_SEQUENCE_FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
