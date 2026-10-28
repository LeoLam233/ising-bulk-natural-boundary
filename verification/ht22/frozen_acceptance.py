#!/usr/bin/env python3
"""Execution-only frozen HT22 acceptance on an authorized Linux/WSL heavy node.

This program never edits a proof, updates a pin, publishes, or dispatches work.
It requires a new output directory and makes an independent source/cache copy.
Python 3.11+, git, and the official Lean 4.34.1 toolchain must already exist.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import pathlib
import re
import shutil
import stat
import subprocess
import sys
import time
import tomllib
import traceback
import zipfile

P = pathlib.Path
COMMIT = "465375f2b6cc0952adaca87eddc859a40f577748"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
ROOT = "IsingBulkHT22"
AUDIT = "AuditHT22"
CONFIG = "lakefile.ht22.toml"
THEOREM = "IsingBulk.HT22.ht22_full_target"
TARGET = "IsingBulk.HT22.HT22FullTarget"
PINS = {
    "mathlib": "d13f23b723b8a846827a245b89c10fc7d3f11612",
    "plausible": "118aa17ee84656b8bd727fef7c458ee8c833385c",
    "LeanSearchClient": "ddf04cf3949fa556442341e87d47f9f6e6074707",
    "importGraph": "e928b72544873815af278d38681b31c0293588e3",
    "proofwidgets": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
    "aesop": "355695d523e41d0554926416cba2a2b3544fbbc9",
    "Qq": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
    "batteries": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
    "Cli": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REGRESSIONS = {
    "LT": ("lakefile.toml", "IsingBulk", "Audit"),
    "HT": ("lakefile.ht.toml", "IsingBulkHT", "AuditHT"),
    "ANISO": ("lakefile.anisotropic.toml", "IsingBulkAnisotropic", "AuditAnisotropic"),
    "JOINT": ("lakefile.joint.toml", "IsingBulkJoint", "AuditJoint"),
    "LT22": ("lakefile.toml", "IsingBulk.Preferred22", None),
}
SCOPE_PRINTS = [
    THEOREM, TARGET,
    "IsingBulk.HT22.PhysicalScope.PublishedRealHTSpinFormFactors",
    "IsingBulk.HT22.PhysicalScope.realBulk",
    "IsingBulk.HT22.PhysicalScope.realSusceptibility",
    "IsingBulk.HT22.Physical.interiorBulk",
    "IsingBulk.HT22.Physical.physicalSusceptibility",
    "IsingBulk.HT22.Physical.oddSeries",
    "IsingBulk.HT22.Physical.coefficient",
    "IsingBulk.HT22.FullTail.coefficientMass",
    "IsingBulk.HT22.AngularFieldJetsStatement",
    "IsingBulk.HT22.SharpCovarianceJetsStatement",
    "IsingBulk.HT.Final.HasInteriorExtension",
    "IsingBulk.Final.HasExteriorExtension",
    "IsingBulk.HT22.equalAngleLeadingCoefficient",
]


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with P(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def safe_rel(name):
    require(isinstance(name, str) and "\\" not in name, "invalid archive path")
    q = pathlib.PurePosixPath(name)
    require(not q.is_absolute() and all(x not in ("", ".", "..") for x in name.split("/")),
            "unsafe/noncanonical archive path: " + name)
    require(".git" not in q.parts and ".lake" not in q.parts,
            "snapshot must not contain repository metadata or caches: " + name)
    require(not any(name.endswith(s) for s in (".olean", ".olean.private", ".olean.server", ".ilean", ".pyc")),
            "compiled object in source-only snapshot: " + name)
    return q


def strip_lean_comments(text):
    """Lexical comment removal; preserve strings/newlines, handle nested comments."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1; i += 2
            elif pair == "-/":
                depth -= 1; i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i + 1]); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif pair == "/-":
            depth = 1; i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            if text[i] == '"': string = True
            out.append(text[i]); i += 1
    require(depth == 0, "unterminated Lean block comment")
    return "".join(out)


def local_import_graph(project):
    modules = {}
    for path in project.rglob("*.lean"):
        rel = path.relative_to(project)
        if ".lake" in rel.parts:
            continue
        module = rel.with_suffix("").as_posix().replace("/", ".")
        text = strip_lean_comments(path.read_text())
        imports = []
        for line in text.splitlines():
            m = re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+?)\s*$", line)
            if m:
                for item in m.group(1).split():
                    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", item),
                            "unsupported import syntax in " + str(rel))
                    imports.append(item)
        modules[module] = imports
    return modules


def local_closure(graph, roots):
    queue, seen = list(roots), set()
    while queue:
        n = queue.pop()
        if n in seen or n not in graph:
            continue
        seen.add(n); queue.extend(graph[n])
    return seen


class Job:
    def __init__(self, args):
        self.a = args
        self.out = args.output.resolve()
        self.out.mkdir(parents=True, exist_ok=False)
        self.receipts = self.out / "receipts"
        self.receipts.mkdir()
        self.source = self.out / "work/source"
        self.project = self.source / "repository/lean"
        self.commands = []
        self.steps = {}
        self.env = os.environ.copy()
        for k in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_HOME", "LEAN_OPTS", "LEANFLAGS"):
            self.env.pop(k, None)
        self.env.update(ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1", RAYON_NUM_THREADS="2",
                        LAKE_ARTIFACT_CACHE="false", LAKE_NO_CACHE="true", PYTHONDONTWRITEBYTECODE="1")
        self.binaries = {}

    def save(self, name, obj):
        write_json(self.receipts / name, obj)

    def run(self, label, command, cwd=None, env=None):
        require(re.fullmatch(r"[A-Za-z0-9_.-]+", label), "unsafe command label")
        command = [str(x) for x in command]
        cwd = cwd or self.project
        rec = dict(label=label, command=command, cwd=str(cwd), started_utc=now(),
                   environment_overrides={k: self.env[k] for k in
                    ("ELAN_TOOLCHAIN", "LEAN_NUM_THREADS", "RAYON_NUM_THREADS", "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE")})
        self.save(label + ".command.json", rec)
        start = time.monotonic()
        stdout = self.receipts / (label + ".stdout.log")
        stderr = self.receipts / (label + ".stderr.log")
        code = None
        try:
            with stdout.open("wb") as so, stderr.open("wb") as se:
                code = subprocess.call(command, cwd=cwd, env=env or self.env, stdout=so, stderr=se)
        finally:
            rec.update(exit_code=code, ended_utc=now(), elapsed_seconds=time.monotonic() - start,
                       stdout_sha256=sha(stdout) if stdout.exists() else None,
                       stderr_sha256=sha(stderr) if stderr.exists() else None)
            self.save(label + ".receipt.json", rec)
            self.commands.append(rec)
        print(label + ": exit " + str(code), flush=True)
        require(code == 0, label + " failed; see unmodified stdout/stderr")
        return stdout.read_text(errors="replace")

    def lake(self, *args, config=CONFIG):
        return [self.binaries["lake"]["path"], "--no-cache", "--no-ansi", "-v", "-f", config, *args]

    def verify_sources(self):
        for name, item in self.manifest["files"].items():
            path = self.source / name
            require(path.is_file() and not path.is_symlink(), "missing/symlink frozen source: " + name)
            require(path.stat().st_size == item["size"] and sha(path) == item["sha256"],
                    "frozen source changed: " + name)
        require(sha(self.source / "SOURCE_MANIFEST.json") == self.a.manifest_sha256,
                "embedded source manifest changed")
        # No new proof/module may silently enter the project after extraction.
        for path in self.project.rglob("*.lean"):
            if ".lake" not in path.relative_to(self.project).parts:
                require(path.relative_to(self.source).as_posix() in self.manifest["files"],
                        "unmanifested project Lean source: " + str(path))

    def extract(self):
        require(sha(self.a.snapshot) == self.a.snapshot_sha256, "snapshot ZIP SHA256 mismatch")
        with zipfile.ZipFile(self.a.snapshot) as z:
            names = z.namelist()
            require(len(names) == len(set(names)), "duplicate ZIP member")
            manifest_data = z.read("SOURCE_MANIFEST.json")
            require(sha_bytes(manifest_data) == self.a.manifest_sha256, "manifest SHA256 mismatch")
            self.manifest = json.loads(manifest_data)
            require(self.manifest.get("format") == 1 and isinstance(self.manifest.get("files"), dict),
                    "unsupported/empty frozen manifest")
            require(self.manifest["files"], "empty source manifest")
            require(set(names) == set(self.manifest["files"]) | {"SOURCE_MANIFEST.json"},
                    "ZIP member set differs from exact frozen manifest")
            self.source.mkdir(parents=True)
            for info in z.infolist():
                rel = safe_rel(info.filename)
                require(not info.is_dir() and not stat.S_ISLNK(info.external_attr >> 16),
                        "non-regular ZIP member: " + info.filename)
                data = z.read(info)
                if info.filename != "SOURCE_MANIFEST.json":
                    item = self.manifest["files"][info.filename]
                    require(set(item) >= {"sha256", "size"} and len(data) == item["size"] and sha_bytes(data) == item["sha256"],
                            "snapshot member mismatch: " + info.filename)
                path = self.source / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        embedded_driver = self.source / "acceptance_job/run_ht22_acceptance.py"
        require(sha(embedded_driver) == sha(P(__file__)), "invoked driver is not the frozen snapshot driver")
        self.baseline = json.loads((self.source / "PROTECTED_BASELINE.json").read_text())
        require(self.baseline.get("commit") == COMMIT and self.baseline.get("files"), "protected commit mismatch")
        for name, item in self.baseline["files"].items():
            safe_rel(name)
            path = self.source / "repository" / name
            data = path.read_bytes()
            require(sha_bytes(data) == item["sha256"], "protected SHA256 mismatch: " + name)
            oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(oid == item["git_blob"] and item["mode"] in ("100644", "100755"),
                    "protected Git blob/mode mismatch: " + name)
        self.verify_sources()
        for name in ("SOURCE_MANIFEST.json", "PROTECTED_BASELINE.json", "SNAPSHOT_STATUS.json"):
            shutil.copyfile(self.source / name, self.receipts / name)
        self.save("SOURCE_IDENTITY.json", dict(snapshot=str(self.a.snapshot.resolve()),
                  snapshot_sha256=self.a.snapshot_sha256, source_manifest_sha256=self.a.manifest_sha256,
                  exact_member_count=len(self.manifest["files"]) + 1,
                  protected_commit=COMMIT, protected_files=len(self.baseline["files"]),
                  source_immutable_by_contract_and_hash=True, source_root=str(self.source), driver_sha256=sha(P(__file__))))
        self.steps["immutable_snapshot"] = "PASS"

    def environment(self):
        require((self.project / "lean-toolchain").read_text().strip() == TOOLCHAIN, "toolchain pin mismatch")
        lock = json.loads((self.project / "lake-manifest.json").read_text())
        packages = lock["packages"]
        require(len(packages) == 9 and {x["name"]: x["rev"] for x in packages} == PINS,
                "nine-package revision lock mismatch")
        require(all(x["type"] == "git" and not x.get("subDir") for x in packages),
                "unsupported dependency layout")
        cfg = tomllib.loads((self.project / CONFIG).read_text())
        require(cfg.get("defaultTargets") == [ROOT, AUDIT], "incorrect HT22 default roots")
        require("-DwarningAsError=true" in cfg.get("moreLeanArgs", []), "strict Lean warnings disabled")
        require(cfg.get("require") == [{"name": "mathlib", "git": "https://github.com/leanprover-community/mathlib4.git", "rev": PINS["mathlib"]}],
                "HT22 config dependency override")
        version = self.run("01-lean-version", ["lean", "--version"])
        require(re.search(r"\b4\.34\.1\b", version) and LEAN_COMMIT in version, "wrong Lean version/commit")
        prefix = P(self.run("02-lean-prefix", ["lean", "--print-prefix"]).strip()).resolve()
        self.toolchain_prefix = prefix
        for name in ("lean", "lake", "leanchecker"):
            binary = (prefix / "bin" / name).resolve()
            require(binary.is_file() and os.access(binary, os.X_OK), "missing official toolchain binary: " + name)
            require(binary.parent == (prefix / "bin").resolve(), "toolchain binary escapes pinned prefix")
            self.binaries[name] = dict(path=str(binary), sha256=sha(binary))
        self.run("03-lake-version", [self.binaries["lake"]["path"], "--version"])
        if self.a.binary_hashes:
            expected = json.loads(self.a.binary_hashes.read_text())
            require(expected == {k: v["sha256"] for k, v in self.binaries.items()}, "tool binary hash mismatch")
        self.env["PATH"] = str(prefix / "bin") + os.pathsep + self.env.get("PATH", "")
        self.save("TOOLCHAIN.json", dict(version=version.strip(), toolchain=TOOLCHAIN, binaries=self.binaries,
                  binary_hashes_externally_pinned=bool(self.a.binary_hashes), python=sys.version,
                  platform=sys.platform, uname=list(os.uname()), environment=self.env_subset()))
        self.steps["toolchain"] = "PASS"

    def env_subset(self):
        return {k: self.env.get(k) for k in ("ELAN_TOOLCHAIN", "LEAN_NUM_THREADS", "RAYON_NUM_THREADS",
                "LAKE_ARTIFACT_CACHE", "LAKE_NO_CACHE", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT")}

    def verify_package(self, name, root, label):
        path = root / name
        require(path.is_dir(), "missing pinned package: " + str(path))
        base = ["git", "-c", "safe.directory=" + str(path.resolve())]
        head = self.run(label + "-" + name + "-head", base + ["rev-parse", "HEAD"], cwd=path).strip()
        status = self.run(label + "-" + name + "-status", base + ["status", "--porcelain", "--untracked-files=no"], cwd=path)
        require(head == PINS[name] and not status.strip(), "dependency changed or unpinned: " + name)
        foreign = []
        for f in path.rglob("*"):
            if f.is_file() and (f.name.endswith(".lean") or ".olean" in f.name or f.name.endswith(".ilean")):
                rel = f.relative_to(path)
                if "IsingBulk" in rel.parts or f.name.startswith(("IsingBulk", "AuditHT22")):
                    foreign.append(rel.as_posix())
        require(not foreign, "project artifacts contaminate dependency cache: " + name + " " + str(foreign[:10]))
        return dict(name=name, rev=head, tracked_source_clean=True, foreign_project_objects=0)

    def dependencies(self):
        cache = self.a.packages.resolve()
        require(cache.is_dir(), "--packages must be a preprovisioned nine-package directory")
        require(not cache.is_relative_to(self.out) and not self.out.is_relative_to(cache), "output/cache paths overlap")
        dest = self.project / ".lake/packages"
        dest.mkdir(parents=True)
        records = []
        for name in PINS:
            self.verify_package(name, cache, "05-input")
            # Independent byte copies: no hardlinks, symlinked packages or writable shared caches.
            shutil.copytree(cache / name, dest / name, symlinks=False)
            records.append(self.verify_package(name, dest, "06-isolated"))
        self.save("DEPENDENCIES.json", dict(pins=PINS, source_cache=str(cache), isolated_cache=str(dest),
                  method="shutil.copytree independent files; no project object import", packages=records))
        self.verify_sources()
        self.steps["nine_pinned_dependencies"] = "PASS"

    def plan_build_and_regressions(self):
        self.graph = local_import_graph(self.project)
        self.added_modules = sorted(n for n in self.graph if n == "IsingBulk.HT22" or
                                    n.startswith("IsingBulk.HT22.") or n in (ROOT, AUDIT))
        baseline_paths = set(self.baseline["files"])
        unprotected = []
        for name in self.manifest["files"]:
            if name.startswith("repository/") and name.removeprefix("repository/") not in baseline_paths:
                unprotected.append(name.removeprefix("repository/"))
        allowed = lambda n: n.startswith("lean/IsingBulk/HT22/") and n.endswith(".lean") or n in (
            "lean/IsingBulk/HT22.lean", "lean/IsingBulkHT22.lean", "lean/AuditHT22.lean", "lean/lakefile.ht22.toml")
        require(all(allowed(n) for n in unprotected), "unclassified new repository input: " + str([n for n in unprotected if not allowed(n)]))
        rows = {}
        for name, (config, root, audit) in REGRESSIONS.items():
            closure = local_closure(self.graph, [root] + ([audit] if audit else []))
            overlap = sorted(closure & set(self.added_modules))
            require(not overlap, "protected original root unexpectedly imports HT22: " + name)
            rows[name] = dict(config=config, root=root, audit=audit, local_source_closure=sorted(closure),
                              new_ht22_intersection=overlap, affected=False)
        self.save("AFFECTED_REGRESSION_RATIONALE.json", dict(protected_sources_changed=[],
                  protected_config_toolchain_lock_changed=False, new_repository_files=unprotected,
                  exact_protected_inventory_verified=True, routes=rows, selected_mode=self.a.regressions,
                  conclusion="No original route is affected: all original bytes/configs are unchanged; no original root/audit imports any additive HT22 module. Optional all-mode executes conservative extra replays.",
                  limitation="Import closures establish noninterference only; proof acceptance uses full type/value/structural graphs, not import lists."))
        self.steps["affected_regression_analysis"] = "PASS_NO_AFFECTED_ROUTES"

    def object_hashes(self):
        build = self.project / ".lake/build"
        return {p.relative_to(build).as_posix(): sha(p) for p in sorted(build.rglob("*"))
                if p.is_file() and (".olean" in p.name or p.suffix == ".ilean")}

    def strict_build(self):
        build = self.project / ".lake/build"
        require(not build.exists(), "project build objects unexpectedly exist before clean build")
        foreign = [str(p) for p in self.project.rglob("*.olean*") if ".lake" not in p.relative_to(self.project).parts]
        require(not foreign, "project source contains forbidden reused objects")
        self.save("CLEAN_PREFLIGHT.json", dict(project_build_absent=True, local_project_objects=foreign,
                  isolated_source_root=str(self.source), only_permitted_cache="exact nine pinned upstream dependencies",
                  strict_config_sha256=sha(self.project / CONFIG), no_cache_flags=True))
        self.run("10-clean-root-build", self.lake("build", ROOT))
        self.steps["strict_clean_root_build"] = "PASS"
        self.run("11-audit-build", self.lake("build", AUDIT))
        self.steps["strict_audit_build"] = "PASS"
        # All additive proof/control source is compiled, including files not imported by the root.
        self.run("12-all-additive-source-build", self.lake("build", *("+" + n for n in self.added_modules)))
        # Deliberate kernel-valid old-route bypass needs this protected module;
        # build it as a fixture prerequisite, never a production proof input.
        bypass_module = "IsingBulk.HT.Final.FullNaturalBoundary"
        self.run("13-bypass-fixture-prerequisite", self.lake("build", "+" + bypass_module))
        expected = local_closure(self.graph, self.added_modules + [bypass_module])
        absent = [n for n in sorted(expected) if not (build / "lib/lean" / P(*n.split("."))).with_suffix(".olean").is_file()]
        require(not absent, "clean source build missing objects: " + str(absent))
        self.save("CLEAN_BUILD.json", dict(root=ROOT, audit=AUDIT, compiled_additive_modules=self.added_modules,
                  expected_local_source_closure=sorted(expected), missing_objects=absent,
                  fixture_only_prerequisites=[bypass_module],
                  project_source_clean=True, upstream_cache_only=True, warning_as_error=True,
                  note="Root and audit have separately recorded zero exits; additive modules build is not a claim that every module is reachable from the terminal theorem."))
        self.ht22_objects = self.object_hashes()
        self.save("HT22_PROOF_OBJECT_SHA256.json", self.ht22_objects)
        self.verify_sources()
        self.steps["strict_all_additive_source_build"] = "PASS"

    def fresh(self):
        self.run("20-official-fresh-kernel", self.lake("env", self.binaries["leanchecker"]["path"], "--fresh", "--verbose", ROOT))
        require(self.object_hashes() == self.ht22_objects, "official fresh replay changed proof objects")
        self.verify_sources()
        self.save("FRESH_KERNEL.json", dict(root=ROOT, separate_command=True, exit_code=0, fresh=True, verbose=True,
                  binary=self.binaries["leanchecker"], source_manifest_sha256=self.a.manifest_sha256,
                  proof_object_manifest_sha256=sha(self.receipts / "HT22_PROOF_OBJECT_SHA256.json"),
                  proof_objects_unchanged=True))
        self.steps["official_fresh_kernel"] = "PASS"

    def lean_environment(self):
        program = "import os,json,shutil;print('HT22_ENV='+json.dumps({'LEAN_PATH':os.environ.get('LEAN_PATH',''),'lean':shutil.which('lean')}))"
        output = self.run("30-lake-environment", self.lake("env", sys.executable, "-c", program))
        records = [x.removeprefix("HT22_ENV=") for x in output.splitlines() if x.startswith("HT22_ENV=")]
        require(len(records) == 1, "cannot identify Lake import environment")
        data = json.loads(records[0])
        require(P(data["lean"]).resolve() == P(self.binaries["lean"]["path"]), "Lake selected wrong Lean executable")
        resolved, absent = [], []
        for item in data["LEAN_PATH"].split(os.pathsep):
            if not item: continue
            p = P(item)
            if not p.is_absolute(): p = self.project / p
            p = p.resolve()
            if not p.is_dir():
                absent.append(str(p)); continue
            require(p.is_relative_to(self.project / ".lake") or p == self.toolchain_prefix / "lib/lean",
                    "unexpected nonisolated import path: " + str(p))
            resolved.append(str(p))
        project_lib = str((self.project / ".lake/build/lib/lean").resolve())
        require(project_lib in resolved, "Lake path lacks newly clean-built project root")
        self.lean_path = os.pathsep.join(dict.fromkeys(resolved))
        self.probe_env = self.env | {"LEAN_PATH": self.lean_path}
        self.save("LEAN_IMPORT_ENVIRONMENT.json", dict(raw=data, effective_lean_path=self.lean_path,
                  omitted_nonexistent_optional_paths=absent, no_external_project_objects=True))

    def graph_and_scope(self):
        controls = self.source / "verification_controls"
        generated = controls / "generated"
        generated.mkdir(exist_ok=True)
        self.final_base = generated / "final"
        self.bypass_base = generated / "old_route_bypass"
        for case, stem, base in (("final", "FinalGraph", self.final_base), ("bypass", "OldRouteBypassGraph", self.bypass_base)):
            driver = generated / (stem + ".lean")
            cmd = [sys.executable, controls / "make_graph_driver.py", "--case", case,
                   "--output", driver, "--graph-base", base]
            if case == "final": cmd += ["--module", ROOT, "--root", THEOREM]
            self.run("31-generate-" + case, cmd, cwd=self.source)
            self.run("32-graph-" + case, [self.binaries["lean"]["path"], "-j1", "-DwarningAsError=true",
                                          "--root", generated, driver], cwd=self.project, env=self.probe_env)
        policy_cmd = [sys.executable, controls / "route_policy.py", self.final_base, "--root", THEOREM, "--physical"]
        for name in self.a.require: policy_cmd += ["--require", name]
        self.run("33-complete-final-graph-policy", policy_cmd, cwd=self.source)
        rows = [json.loads(s) for s in P(str(self.final_base) + ".graph.jsonl").read_text().splitlines() if s.strip()]
        summary = json.loads(P(str(self.final_base) + ".summary.json").read_text())
        types = [json.loads(s) for s in P(str(self.final_base) + ".types.jsonl").read_text().splitlines() if s.strip()]
        terminal = [r for r in types if r["name"] == THEOREM]
        require(len(terminal) == 1 and terminal[0]["pretty_type"] == TARGET, "terminal type changed or has premises")
        require(summary["missing"] == [] and summary["unsafe_or_partial"] == [], "incomplete/unsafe closure")
        require(set(summary["axioms"]) <= ALLOWED_AXIOMS, "unexpected axiom")
        require(not any(r["name"].startswith("sorryAx") for r in rows), "sorry reachable from terminal")
        canonical = json.dumps(sorted(rows, key=lambda r: r["name"]), sort_keys=True, separators=(",", ":")).encode()
        self.save("CLOSURE.json", dict(summary=summary, canonical_graph_sha256=sha_bytes(canonical),
                  root_type=terminal[0], required_extra=self.a.require, graph_edges=["type", "value", "structural"],
                  source_manifest_sha256=self.a.manifest_sha256,
                  proof_object_manifest_sha256=sha(self.receipts / "HT22_PROOF_OBJECT_SHA256.json")))
        probe = generated / "ScopeProbe.lean"
        text = "import " + ROOT + "\nset_option pp.all true\nset_option pp.universes true\nset_option pp.proofs true\nset_option pp.explicit true\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        text += "\n".join("#print " + n for n in SCOPE_PRINTS) + "\n"
        text += "#print axioms " + THEOREM + "\n"
        text += f"example : @{THEOREM} = (show {TARGET} from {THEOREM}) := rfl\n"
        probe.write_text(text)
        self.run("34-expanded-terminal-and-physical-scope", [self.binaries["lean"]["path"], "-j1", "-DwarningAsError=true",
                 "--root", generated, probe], cwd=self.project, env=self.probe_env)
        self.steps["complete_type_value_structural_scan"] = "PASS"
        self.steps["expanded_terminal_and_physical_types"] = "PASS"

    def controls(self):
        controls = self.source / "verification_controls"
        cmd = [sys.executable, controls / "run_controls.py", "--phase", "final", "--no-deps",
               "--lean", self.binaries["lean"]["path"], "--lean-path", self.lean_path,
               "--frozen-manifest", self.source / "SOURCE_MANIFEST.json", "--final-root", THEOREM,
               "--final-graph-base", self.final_base, "--bypass-graph-base", self.bypass_base]
        for name in self.a.require: cmd += ["--require", name]
        self.run("40-effective-final-controls", cmd, cwd=self.source)
        receipts = list((controls / "runs").glob("*/receipt.json"))
        require(len(receipts) == 1, "cannot uniquely identify final controls receipt")
        receipt = json.loads(receipts[0].read_text())
        require(receipt.get("accepted") and receipt.get("final_controls_passed") and receipt.get("phase") == "final",
                "controls did not certify final frozen run")
        require(receipt.get("frozen_manifest_sha256") == self.a.manifest_sha256, "controls source identity mismatch")
        require(self.object_hashes() == self.ht22_objects, "scope/controls altered clean-built proof objects")
        self.verify_sources()
        self.steps["effective_positive_negative_controls"] = "PASS"

    def regressions(self):
        if self.a.regressions == "affected":
            self.steps["affected_regressions"] = "NOT_REQUIRED_PROVED_ADDITIVE_NONINTERFERENCE"
            return
        # Preserve exact HT22 objects; each optional old-route build starts empty.
        build = self.project / ".lake/build"
        preserved = self.out / "work/ht22-build-preserved"
        shutil.move(str(build), preserved)
        try:
            for name, (config, root, audit) in REGRESSIONS.items():
                if build.exists(): shutil.rmtree(build)
                self.run("50-" + name + "-clean-build", self.lake("build", root, *([audit] if audit else []), config=config))
                before = self.object_hashes()
                self.save("REGRESSION_" + name + "_OBJECT_SHA256.json", before)
                self.run("51-" + name + "-official-fresh", self.lake("env", self.binaries["leanchecker"]["path"], "--fresh", "--verbose", root, config=config))
                require(self.object_hashes() == before, "regression replay changed proof objects: " + name)
                self.verify_sources()
                self.steps["optional_regression_" + name] = "PASS_STRICT_CLEAN_BUILD_AND_FRESH_REPLAY"
        finally:
            if build.exists(): shutil.rmtree(build)
            shutil.move(preserved, str(build))
        require(self.object_hashes() == self.ht22_objects, "HT22 preserved build restore mismatch")
        self.steps["affected_regressions"] = "PASS_PLUS_ALL_FIVE_CONSERVATIVE_REPLAYS"

    def finish_checks(self):
        self.verify_sources()
        require(sha(self.a.snapshot) == self.a.snapshot_sha256, "input ZIP changed during acceptance")
        require(self.object_hashes() == self.ht22_objects, "final HT22 proof object hash drift")
        for name in PINS:
            self.verify_package(name, self.project / ".lake/packages", "60-final")
        self.save("FINAL_IMMUTABILITY.json", dict(source_manifest_sha256=self.a.manifest_sha256,
                  snapshot_sha256=self.a.snapshot_sha256, all_frozen_bytes_unchanged=True,
                  protected_files_unchanged=True, all_nine_dependency_sources_clean=True,
                  ht22_proof_objects_unchanged=True))
        self.steps["final_immutability"] = "PASS"

    def bundle_results(self, status, error=None):
        # Include original streams, generated probes, graphs and portable-control receipts.
        # Do not include source/cache/object bloat; immutable input ZIP remains separately local.
        for dirname in ("generated", "runs"):
            src = self.source / "verification_controls" / dirname
            if src.exists():
                dest = self.receipts / "verification_controls" / dirname
                for file in src.rglob("*"):
                    if file.is_file() and not file.is_symlink() and file.suffix in (".json", ".jsonl", ".log", ".lean"):
                        target = dest / file.relative_to(src)
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copyfile(file, target)
        self.save("SUMMARY.json", dict(status=status, steps=self.steps, error=error,
                  source_manifest_sha256=self.a.manifest_sha256, snapshot_sha256=self.a.snapshot_sha256,
                  root=ROOT, audit=AUDIT, theorem=THEOREM, commands=len(self.commands), ended_utc=now(),
                  independent_audits=0, author_proof_changes=False, publication=False, uploads=False,
                  scope="Frozen-source execution acceptance only. Three separately sealed independent full-scope Lean audits remain mandatory; this is not an audit verdict or campaign completion."))
        inventory = {p.relative_to(self.receipts).as_posix(): dict(sha256=sha(p), size=p.stat().st_size)
                     for p in sorted(self.receipts.rglob("*")) if p.is_file()}
        self.save("RESULT_MANIFEST.json", dict(format=1, files=inventory))
        archive = self.out / ("HT22_ACCEPTANCE_" + status + "_" + self.a.manifest_sha256[:16] + ".zip")
        with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED, compresslevel=6) as z:
            for p in sorted(self.receipts.rglob("*")):
                if p.is_file(): z.write(p, p.relative_to(self.receipts).as_posix())
        with zipfile.ZipFile(archive) as z:
            require(z.testzip() is None, "result ZIP failed readback")
            for name, item in inventory.items():
                require(sha_bytes(z.read(name)) == item["sha256"], "result ZIP content mismatch: " + name)
        write_json(self.out / "RESULT_ZIP_RECEIPT.json", dict(path=str(archive), sha256=sha(archive),
                  size=archive.stat().st_size, readback_verified=True, status=status,
                  source_manifest_sha256=self.a.manifest_sha256, uploaded=False))
        print("Result: " + str(archive), flush=True)


def parse_args():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--snapshot", type=P, required=True, help="exact source-only ZIP from Dot")
    p.add_argument("--snapshot-sha256", required=True)
    p.add_argument("--manifest-sha256", required=True, help="SHA256 of embedded SOURCE_MANIFEST.json")
    p.add_argument("--packages", type=P, required=True, help="read-only source of nine pinned dependency repos/caches; copied, never linked or modified")
    p.add_argument("--output", type=P, required=True, help="new, nonexistent isolated scratch/results directory")
    p.add_argument("--binary-hashes", type=P, help="optional expected {lean:sha256,lake:sha256,leanchecker:sha256} JSON")
    p.add_argument("--regressions", choices=("affected", "all"), default="affected",
                   help="affected derives exact additive noninterference; all additionally source-cleans/builds/fresh-replays all five old roots")
    p.add_argument("--require", action="append", default=[], help="additional mechanism declaration required in terminal proof closure")
    a = p.parse_args()
    for digest in (a.snapshot_sha256, a.manifest_sha256):
        if not re.fullmatch(r"[0-9a-f]{64}", digest): p.error("hashes must be full lowercase SHA256")
    for name in a.require:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name): p.error("invalid required declaration")
    if not a.snapshot.is_file(): p.error("snapshot ZIP does not exist")
    if a.output.exists(): p.error("--output must not exist; never reuse a partial acceptance directory")
    return a


def main():
    args = parse_args()
    job = Job(args)
    status, error = "FAIL", None
    try:
        job.extract()
        job.environment()
        job.dependencies()
        job.plan_build_and_regressions()
        job.strict_build()
        job.fresh()
        job.lean_environment()
        job.graph_and_scope()
        job.controls()
        job.regressions()
        job.finish_checks()
        status = "PASS"
    except BaseException as exc:
        error = str(exc)
        (job.receipts / "FAILURE_TRACEBACK.log").write_text(traceback.format_exc())
        print("FAIL: " + error, file=sys.stderr, flush=True)
    finally:
        job.bundle_results(status, error)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
