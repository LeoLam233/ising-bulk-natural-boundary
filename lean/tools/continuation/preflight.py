#!/usr/bin/env python3
"""Read-only candidate checks. This does not build or replay Lean proofs."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

HERE = Path(__file__).resolve().parent
APPROVED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")


class PreflightError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PreflightError(message)


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def identity(value: Any) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def safe_path(root: Path, relative: str) -> Path:
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts,
            f"Expected a project-relative path: {relative}")
    resolved = (root / path).resolve()
    require(resolved.is_relative_to(root), f"Path escapes project: {relative}")
    require(resolved.is_file(), f"Missing file: {relative}")
    return resolved


def clean_environment(lean_bin: Path) -> dict[str, str]:
    # Preserve ordinary host settings, but never inherit toolchain/cache or
    # dynamic-loader overrides into a proof-verification subprocess.
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("LEAN", "LAKE", "ELAN"))
           and key not in {"LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT",
                           "PYTHONPATH", "PYTHONHOME"}}
    env["PATH"] = str(lean_bin) + os.pathsep + os.defpath
    env["GIT_OPTIONAL_LOCKS"] = "0"
    env["LAKE_NO_CACHE"] = "true"
    env["LAKE_ARTIFACT_CACHE"] = "false"
    env["LAKE_CACHE_DIR"] = ""
    env["LAKE_CONFIG"] = "/dev/null"
    return env


def read_command(args: list[str], cwd: Path, env: dict[str, str]) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=120, check=False)
    require(result.returncode == 0,
            f"Read-only command failed ({result.returncode}): {args!r}\n{result.stderr}")
    return result.stdout.strip()


def check_dependency_source(dep_path: Path, revision: str, env: dict[str, str]) -> str:
    """Shared pinned-HEAD, tracked-source and Lake-override checks."""
    git = ["git", "--no-optional-locks", "-c", "core.fsmonitor=false", "-C", str(dep_path)]
    head = read_command(git + ["rev-parse", "HEAD"], dep_path, env)
    dirty = read_command(git + ["status", "--porcelain=v1", "--untracked-files=no"], dep_path, env)
    require(head == revision and not dirty, f"Dependency pin/source mismatch: {dep_path.name}\n{dirty}")
    tracked_configs = set(read_command(git + ["ls-tree", "--name-only", "HEAD", "--",
        "lakefile.lean", "lakefile.toml"], dep_path, env).splitlines())
    for config_name in ("lakefile.lean", "lakefile.toml"):
        config_file = dep_path / config_name
        if config_file.exists() or config_file.is_symlink():
            require(config_name in tracked_configs and not config_file.is_symlink(),
                    f"Unbound dependency configuration: {dep_path.name}/{config_name}")
    return head


def reject_dependency_project_namespaces(project: Path) -> None:
    """Reject the audited LEAN_PATH attack without deleting dependency outputs."""
    packages = project / ".lake/packages"
    if not packages.exists():
        return
    for dep_path in sorted(packages.iterdir()):
        build = dep_path / ".lake/build"
        seen: set[Path] = set()
        # Follow output-directory links too; visit each resolved directory once.
        for directory, dirs, files in os.walk(build, followlinks=True):
            for name in dirs + files:
                require(name not in {"IsingBulk", "Audit"}
                        and not name.startswith(("IsingBulk.olean", "Audit.olean")),
                        f"Foreign project namespace in dependency build: {Path(directory) / name}")
            resolved = Path(directory).resolve()
            if resolved in seen:
                dirs.clear()
            seen.add(resolved)


def lean_code(text: str) -> str:
    """Blank comments and Lean string/character literals, preserving positions.

    Raw strings use r followed by zero or more hashes and a quote; their
    terminator contains the same hashes. Character escapes follow pinned
    Lean.Parser.Basic. Apostrophes within identifiers are not character starts.
    This remains a lexical check, not a replacement for elaboration.
    """
    out = list(text)
    depth = 0
    quoted = False
    line_comment = False
    i = 0
    while i < len(text):
        c = text[i]
        pair = text[i:i + 2]
        if line_comment:
            if c == "\n":
                line_comment = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if pair == "/-":
                out[i:i + 2] = [" ", " "]
                depth += 1
                i += 2
            elif pair == "-/":
                out[i:i + 2] = [" ", " "]
                depth -= 1
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if c == "\\":
                out[i] = " "
                if i + 1 < len(text):
                    if text[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                else:
                    i += 1
            else:
                if c == '"':
                    quoted = False
                if c != "\n":
                    out[i] = " "
                i += 1
        elif pair == "--":
            out[i:i + 2] = [" ", " "]
            line_comment = True
            i += 2
        elif pair == "/-":
            out[i:i + 2] = [" ", " "]
            depth = 1
            i += 2
        elif c == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")) \
                and (raw := re.match(r'r(\#*)"', text[i:])):
            start = i
            delimiter = '"' + raw.group(1)
            end = text.find(delimiter, i + len(raw.group(0)))
            require(end >= 0, "Unterminated Lean raw string")
            i = end + len(delimiter)
            for j in range(start, i):
                if text[j] != "\n":
                    out[j] = " "
        elif c == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
            literal = re.match(r"'(?:[^\\']|\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'", text[i:])
            if literal:
                end = i + len(literal.group(0))
                for j in range(i, end):
                    if text[j] != "\n":
                        out[j] = " "
                i = end
            else:
                i += 1
        elif c == '"':
            out[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    require(depth == 0 and not quoted, "Unterminated Lean comment or string")
    return "".join(out)


def imports(code: str) -> set[str]:
    result: set[str] = set()
    for match in re.finditer(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", code, re.M):
        for name in match.group(1).split():
            require(NAME.fullmatch(name) is not None, f"Unsupported import syntax: {name}")
            result.add(name)
    return result


def declarations(code: str) -> dict[str, str]:
    """Lexical source-map check; compiled origin/type checks run separately."""
    namespace: list[str] = []
    scopes: list[int] = []
    result: dict[str, str] = {}
    for line in code.splitlines():
        ns = re.match(r"^namespace\s+([A-Za-z_0-9.']+)\s*$", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+\S+)?\s*$", line)
        if ns:
            scopes.append(len(namespace))
            namespace.extend(ns.group(1).split("."))
        elif section:
            scopes.append(len(namespace))
        elif re.match(r"^end(?:\s+\S+)?\s*$", line):
            if scopes:
                namespace = namespace[:scopes.pop()]
        else:
            declaration = re.match(
                r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
                r"(theorem|lemma|def|abbrev|structure|class|opaque)\s+([A-Za-z_0-9.']+)", line)
            if declaration:
                name = declaration.group(2)
                full = name.removeprefix("_root_.") if name.startswith("_root_.") else \
                    ".".join(namespace + [name])
                result[full] = declaration.group(1)
    return result


def snapshot(project: Path, lean_bin: Path, contract_path: Path = HERE / "endpoint_contract.json") -> dict:
    project = project.resolve()
    lean_bin = lean_bin.resolve()
    require(sys.platform.startswith("linux"), "This wrapper targets Linux/WSL")
    require(project.is_dir(), f"Missing project: {project}")
    require(not (project / "lakefile.lean").exists() and not (project / "lakefile.lean").is_symlink(),
            "Unbound alternative root lakefile.lean is forbidden; the frozen config is lakefile.toml")
    require(project == HERE.parents[1].resolve(),
            "Use the verification tools copied inside the selected candidate project; external mixed-tree drivers are unsupported")
    reject_dependency_project_namespaces(project)
    contract = json.loads(contract_path.read_text())
    require(contract["root_module"] == "IsingBulk", "Unexpected root module")
    freeze = json.loads(safe_path(project, "TOOLCHAIN_FREEZE.json").read_text())
    require(freeze["lean_commit"] == contract["lean_commit"], "Lean commit contract mismatch")
    require(freeze["lean"] == contract["lean_toolchain"], "Lean toolchain contract mismatch")
    require(freeze["mathlib"] == contract["mathlib_rev"], "Mathlib contract mismatch")
    frozen = {entry["path"]: entry["sha256"] for entry in freeze["files"]}
    require(frozen == contract["frozen_config_sha256"], "Frozen configuration contract mismatch")
    for path, expected in frozen.items():
        require(digest(safe_path(project, path)) == expected, f"Frozen configuration changed: {path}")

    source_meta = json.loads(safe_path(project, "SOURCE.json").read_text())
    manuscript = safe_path(project, source_meta["local_copy"])
    paper_bytes = manuscript.read_bytes()
    paper_blob = hashlib.sha1(b"blob " + str(len(paper_bytes)).encode() + b"\0" + paper_bytes).hexdigest()
    require(digest(manuscript) == source_meta["sha256"], "Manuscript SHA256 mismatch")
    require(paper_blob == source_meta["expected_git_blob"] == contract["manuscript_git_blob"],
            "Manuscript Git blob mismatch")
    manifest = json.loads(safe_path(project, "lake-manifest.json").read_text())
    require(manifest["name"] == "ising_bulk", "Wrong outer project manifest")
    packages = manifest["packages"]
    package_names = [dep["name"] for dep in packages]
    require(len(package_names) == len(set(package_names)), "Duplicate dependency name")
    require({dep["name"]: dep["rev"] for dep in packages} == contract["dependency_revisions"],
            "Dependency pin contract mismatch")

    env = clean_environment(lean_bin)
    runtime_files: dict[str, str] = {}
    for name in ("lean", "lake", "leanchecker"):
        path = lean_bin / name
        require(path.is_file() and os.access(path, os.X_OK), f"Missing executable: {path}")
        runtime_files["bin/" + name] = digest(path)
    runtime_root = lean_bin.parent
    for name in ("libLake_shared.so", "libInit_shared.so", "libleanshared.so",
                 "libleanshared_1.so", "libleanshared_2.so"):
        path = runtime_root / "lib/lean" / name
        require(path.is_file(), f"Missing official runtime shared library: {path}")
        runtime_files["lib/lean/" + name] = digest(path)
    version = read_command([str(lean_bin / "lean"), "--version"], project, env)
    require("version 4.34.1," in version and contract["lean_commit"] in version,
            f"Wrong Lean executable version: {version}")
    lake_version = read_command([str(lean_bin / "lake"), "--version"], project, env)
    require("Lean version 4.34.1" in lake_version, f"Wrong Lake version: {lake_version}")
    # Never invoke leanchecker with --help/--version: this CLI does not implement them.
    runtime = {"lean_version": version, "lake_version": lake_version, "sha256": runtime_files}

    dependency_records = []
    dependency_roots: list[Path] = []
    for dep in packages:
        require(dep["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", dep["rev"]) is not None,
                f"Unsupported or unpinned dependency: {dep['name']}")
        dep_path = project / manifest["packagesDir"] / dep["name"]
        require(dep_path.is_dir(), f"Dependency is absent; no download attempted: {dep['name']}")
        head = check_dependency_source(dep_path, dep["rev"], env)
        dependency_records.append({"name": dep["name"], "revision": head, "url": dep["url"]})
        dependency_roots.append(dep_path.resolve())

    production = sorted((project / "IsingBulk").rglob("*.lean"))
    require(production, "No IsingBulk production sources")
    source_files = production + [safe_path(project, "IsingBulk.lean")]
    audit = safe_path(project, "Audit.lean")
    code = {}
    forbidden = re.compile(r"\b(sorry|sorryAx|admit|native_decide|ofReduceBool|ofReduceNat|unsafe|axiom)\b"
                           r"|debug\.skipKernelTC")
    for path in source_files + [audit]:
        require(path.resolve().is_relative_to(project), f"Source symlink escapes project: {path}")
        relative = path.relative_to(project).as_posix()
        code[relative] = lean_code(path.read_text(encoding="utf-8"))
        bad = forbidden.search(code[relative])
        require(bad is None, f"Forbidden proof construct in {relative}: {bad.group(0) if bad else ''}")
    module_paths = {".".join(p.relative_to(project).with_suffix("").parts): p for p in production}
    root_imports = imports(code["IsingBulk.lean"])
    missing = sorted(set(module_paths) - root_imports)
    require(not missing, f"Production modules absent from root: {missing}")
    external_imports = set()
    for relative, text in code.items():
        for module in imports(text):
            if module == "IsingBulk":
                continue
            if module.startswith("IsingBulk."):
                require(module in module_paths, f"Project import without source in {relative}: {module}")
            else:
                external_imports.add(module)
    for module in sorted(external_imports):
        suffix = Path(*module.split(".")).with_suffix(".lean")
        require(any((base / suffix).is_file() for base in dependency_roots + [runtime_root / "src/lean"]),
                f"External import has no supplied pinned source: {module}")

    with safe_path(project, "CLAIM_LEDGER.tsv").open(newline="", encoding="utf-8-sig") as stream:
        ledger_rows = list(csv.DictReader(stream, delimiter="\t"))
    labels = [r["source_label"] for r in ledger_rows]
    require(len(labels) == len(set(labels)), "Duplicate claim ledger source label")
    ledger = {r["source_label"]: r for r in ledger_rows}
    source_map = json.loads(safe_path(project, "tools/continuation/source_references.json").read_text())
    require(source_map.get("schema") == "ising-source-reference-map-v1", "Unexpected source-reference schema")
    references = source_map["references"]
    reference_keys = [(entry["source_label"], entry["ledger_token"]) for entry in references]
    ledger_keys = {(row["source_label"], token.strip()) for row in ledger_rows
                   for token in row["lean_declaration"].split(";") if token.strip()}
    require(len(reference_keys) == len(set(reference_keys)), "Duplicate source-reference entry")
    require(set(reference_keys) == ledger_keys,
            f"Source-reference coverage mismatch; missing={sorted(ledger_keys-set(reference_keys))}; "
            f"extra={sorted(set(reference_keys)-ledger_keys)}")
    for entry in references:
        target = entry["target"]
        require(NAME.fullmatch(target) is not None and target.startswith("IsingBulk."),
                f"Unsafe/invalid source-reference target: {target}")
        require(entry["kind"] in ("module", "declaration"), f"Unknown source-reference kind: {entry['kind']}")
        if entry["kind"] == "module":
            require(target in module_paths, f"Source-reference module has no production file: {target}")
    paper = paper_bytes.decode("utf-8")
    endpoint_names = [entry["declaration"] for entry in contract["endpoints"]]
    require(len(endpoint_names) == len(set(endpoint_names)), "Duplicate endpoint contract entry")
    for entry in contract["endpoints"]:
        name, path, module = entry["declaration"], entry["source"], entry["module"]
        require(NAME.fullmatch(name) is not None and NAME.fullmatch(module) is not None,
                f"Invalid endpoint name/module: {name}")
        require(module_paths.get(module) == project / path, f"Endpoint source/module mismatch: {name}")
        require(declarations(code[path]).get(name) in ("theorem", "lemma"),
                f"Endpoint declaration absent from expected source namespace: {name}")
        label = entry["source_label"]
        require("\\label{" + label + "}" in paper, f"Missing manuscript label: {label}")
        require(label in ledger, f"Missing ledger source-map entry: {label}")
        require(ledger[label]["source_commit"] == source_meta["repository_snapshot_commit"],
                f"Ledger source commit mismatch: {label}")
        if entry.get("require_ledger_declaration", False):
            tokens = {s.strip() for s in ledger[label]["lean_declaration"].split(";")}
            require(name in tokens, f"Ledger {label} must name exact endpoint {name}")

    proof_paths = sorted({p.relative_to(project).as_posix() for p in source_files} |
                         set(frozen) | {"TOOLCHAIN_FREEZE.json", "SOURCE.json", source_meta["local_copy"]})
    proof_input = {
        "files": {path: digest(safe_path(project, path)) for path in proof_paths},
        "dependencies": sorted(dependency_records, key=lambda d: d["name"]),
        "lean_commit": contract["lean_commit"],
    }
    verification_paths = ["Audit.lean", "CLAIM_LEDGER.tsv", "CORRESPONDENCE.md", "COVERAGE.md",
                          "GAP_MANIFEST.md", "CONTINUATION_SOURCE_CORRESPONDENCE.md",
                          "CONTINUATION_AUXILIARY_SCOPE.md", "tools/continuation/source_references.json"]
    controls = project / "control_packet/continuation"
    generated_parts = {"results", "logs", "run_logs", "__pycache__"}
    for path in sorted(controls.rglob("*")):
        if (path.is_file() and not generated_parts.intersection(path.relative_to(controls).parts)
                and path.suffix in (".py", ".lean", ".json", ".md", ".toml", ".sh", ".ps1")):
            verification_paths.append(path.relative_to(project).as_posix())
    verification = {path: digest(safe_path(project, path)) for path in sorted(set(verification_paths))}
    verification.update({"tool:" + p.name: digest(p) for p in sorted(HERE.iterdir())
                         if p.is_file() and p.suffix in (".py", ".json", ".md", ".lean")})
    verification["endpoint_contract_content"] = identity(contract)
    return {
        "status": "PREFLIGHT_PASS_NOT_BUILD_OR_REPLAY",
        "PROOF_CRITICAL_PAYLOAD_ID": identity(proof_input),
        "VERIFICATION_INPUT_ID": identity(verification),
        "RUNTIME_ID": identity(runtime),
        "proof_inputs": proof_input,
        "verification_inputs": verification,
        "runtime": runtime,
        "production_module_count": len(production),
        "endpoint_count": len(contract["endpoints"]),
        "endpoints": contract["endpoints"],
        "source_reference_count": len(references),
        "source_references": references,
        "root_module": "IsingBulk",
        "source_check_limit": "Lexical declaration/source-map check; compiled type and origin checks remain separate.",
        "dependency_check_limit": "Exact Git revisions and clean tracked source; caches are not proof evidence.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=HERE.parents[1])
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, help="Write a new receipt; existing files are never overwritten")
    args = parser.parse_args()
    try:
        result = snapshot(args.project, args.lean_bin)
        if args.output:
            with args.output.open("x", encoding="utf-8") as stream:
                json.dump(result, stream, indent=2)
                stream.write("\n")
        print(json.dumps({k: result[k] for k in ("status", "PROOF_CRITICAL_PAYLOAD_ID",
                         "VERIFICATION_INPUT_ID", "RUNTIME_ID", "production_module_count", "endpoint_count")}, indent=2))
        return 0
    except (PreflightError, OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        print(f"PREFLIGHT_FAILED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
