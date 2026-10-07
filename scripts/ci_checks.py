#!/usr/bin/env python3
"""CI audit checks for recursion-topology-fv (INVARIANTS.md I4).

Checks are selected by flag (multiple may be passed together — the Lean audits share a
single `lake env lean` invocation, so Mathlib is loaded once):

  --self-test              Exercise the source lexer and project-module
                           enumeration used by the hygiene gate.

  --check-axioms           Every headline theorem depends only on the permitted
                           axiom set {propext, Classical.choice, Quot.sound}, and on
                           no `sorryAx` (I4). We generate `#print axioms` lines and
                           parse the output. NOTE this pins only the *listed*
                           theorems' footprints — it is not the repo-wide promise;
                           that is `--check-hygiene`.

  --check-hygiene          The repo-wide I4 promise: **no** `sorry` and **no**
                           non-permitted axiom anywhere in the project's own
                           modules. Two independent layers, because `lake build`
                           enforces neither (`sorry` is only a *warning* and an
                           `axiom` declaration compiles fine, so a stray
                           `axiom bad : False` or a `sorry` in any theorem not
                           reachable from HEADLINE_THEOREMS passes both `lake build`
                           and `--check-axioms`):
                             1. A Lean metaprogram walks every constant declared in
                                the project's modules and fails if it *is* a
                                non-permitted axiom or if `collectAxioms` reports
                                `sorryAx`/a non-permitted axiom.
                             2. A source scan of the umbrella
                                `recursion-topology-fv.lean` and `recursion-topology-fv/**/*.lean`
                                (comments and string literals stripped) rejecting
                                `sorry`/`sorryAx`/`admit`/`native_decide` and any
                                `axiom` declaration — this also catches an
                                anonymous or unused hole regardless of reachability.

                           Every discovered module is built explicitly and then
                           imported by the metaprogram. Thus a new `.lean` file
                           cannot evade the audit merely by being absent from the
                           umbrella import closure.

Later issues extend HEADLINE_THEOREMS as they add headline results.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Headline theorems whose axiom footprint CI pins. Add every theorem that an
# issue treats as a principal result.
HEADLINE_THEOREMS = [
    "VanillaZkVM.ZkVM.cte_iff_knowledgeSound",   # keystone
    "VanillaZkVM.knowledgeSound_trivialAS",      # non-vacuity floor
    "VanillaZkVM.chain_flatten",                 # concatenation lemma
    "VanillaZkVM.TwoStep.System.committedTrace_extract",  # two-layer committed-chain extraction
    "VanillaZkVM.trace_mem_extract",             # memory trace reconstruction
    "VanillaZkVM.TwoStep.System.cte", # full-memory two-step CTE
    "VanillaZkVM.MemorySanity.exactVC_bindingAssumptions",  # satisfiability
    "VanillaZkVM.MemorySanity.appendBitVC_not_updateBinding",  # countermodel
    "VanillaZkVM.ISA.System.step_iff_operation_at_pc",  # fixed-program selection
    "VanillaZkVM.ISA.System.committedOperation_step",  # committed/step bridge
    "VanillaZkVM.MultiStep.System.combine_tree", # tree-unrolling extraction
    "VanillaZkVM.MultiStep.System.committedTrace_extract",  # embed ∘ tree unrolling
    "VanillaZkVM.MultiStep.System.cte",          # full-memory multi-step CTE
    "VanillaZkVM.Bus.System.stepWithBus_committedOperation",  # bus/ISA witness bridge
    "VanillaZkVM.Bus.System.segment_extract",  # one-segment bus unification
    "VanillaZkVM.Bus.TwoStepSystem.execution_extract",  # non-recursive per-segment execution
    "VanillaZkVM.Bus.TwoStepSystem.cte",       # bus-backed two-step CTE
    "VanillaZkVM.VanillaVM.System.cte_main",   # recursive CTE with bus-checked segments
]

# Project source scanned by the hygiene source layer.
LEAN_ROOT = REPO / "recursion-topology-fv.lean"
LEAN_SRC_DIR = REPO / "recursion-topology-fv"
# Tokens that must never appear in project source (I4). `axiom` is included
# because the permitted axioms come from core/Mathlib — we never declare our own.
FORBIDDEN_TOKENS = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\bsorryAx\b"), "direct sorryAx use"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"\baxiom\b"), "axiom declaration"),
]

# Walks every constant *declared in the project's own modules* and fails on a
# non-permitted axiom or a `sorryAx`. Scoped in a section so its `open`s cannot
# perturb the `#print axioms` lines that share this compilation.
LEAN_HYGIENE = """
section CIHygieneCheck
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut problems : Array String := #[]
  let mut scanned := 0
  for i in [0 : env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if mod == `«recursion-topology-fv» || (`«recursion-topology-fv»).isPrefixOf mod then
      let data := env.header.moduleData[i]!
      for n in data.constNames do
        scanned := scanned + 1
        match env.find? n with
        | some (.axiomInfo _) =>
            if !permitted.contains n then
              problems := problems.push s!"  {mod}: declares axiom {n}"
        | _ =>
            for a in ← liftCoreM (Lean.collectAxioms n) do
              if !permitted.contains a then
                problems := problems.push s!"  {mod}: {n} depends on {a}"
  IO.println s!"Hygiene: scanned {scanned} declarations across project modules."
  if problems.isEmpty then
    IO.println "OK: no sorry and no non-permitted axiom in any project module."
  else
    IO.println s!"FAIL: {problems.size} hygiene violation(s):"
    for p in problems do IO.println p
    throwError "repo-wide axiom/sorry hygiene check failed (I4)"

end CIHygieneCheck
"""


def project_lean_files() -> list[Path]:
    """Every source module in the root `lean_lib recursion-topology-fv`.

    The umbrella file is a sibling of the module directory, so a directory-only
    glob is insufficient. Keep this enumeration in one place: it drives the
    source scan, explicit module build, and generated imports.
    """
    files = [LEAN_ROOT] if LEAN_ROOT.is_file() else []
    if LEAN_SRC_DIR.is_dir():
        files.extend(LEAN_SRC_DIR.rglob("*.lean"))
    return sorted(set(files))


def module_name(path: Path) -> str:
    """Translate a project source path to its Lean module name.

    A component that is not a plain identifier (the hyphenated root directory)
    is written `«...»`, which is how both `import` and `lake build +<module>`
    spell it.
    """
    rel = path.relative_to(REPO)
    if rel.suffix != ".lean":
        raise ValueError(f"not a Lean source file: {rel}")
    parts = rel.with_suffix("").parts
    component = re.compile(r"^[A-Za-z_][A-Za-z0-9_'-]*$")
    plain = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
    if not parts or any(not component.match(part) for part in parts):
        raise ValueError(f"cannot derive a Lean module name from {rel}")
    return ".".join(part if plain.match(part) else f"«{part}»" for part in parts)


def _strip_lean_noncode(src: str) -> str:
    """Blank comments and ordinary string literals while preserving newlines.

    Lean block comments nest. String escapes are skipped so an escaped quote
    does not end a string early. Replacing non-code characters with spaces,
    rather than deleting them, preserves the line numbers reported by CI.
    """
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_line_comment = False
    in_string = False
    while i < n:
        two = src[i:i + 2]

        if in_line_comment:
            if src[i] == "\n":
                out.append("\n")
                in_line_comment = False
            else:
                out.append(" ")
            i += 1
            continue

        if depth:
            if two == "/-":
                depth += 1
                out.extend((" ", " "))
                i += 2
                continue
            if two == "-/":
                depth -= 1
                out.extend((" ", " "))
                i += 2
                continue
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue

        if in_string:
            if src[i] == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if src[i + 1] == "\n" else " ")
                i += 2
                continue
            if src[i] == '"':
                in_string = False
                out.append(" ")
            else:
                out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue

        if two == "/-":
            depth += 1
            out.extend((" ", " "))
            i += 2
            continue
        if two == "--":
            in_line_comment = True
            out.extend((" ", " "))
            i += 2
            continue
        if src[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def source_problems(path: Path, src: str) -> list[str]:
    """Forbidden-token diagnostics for one source, with stable line numbers."""
    problems: list[str] = []
    stripped = _strip_lean_noncode(src)
    rel = path.relative_to(REPO).as_posix()
    for lineno, line in enumerate(stripped.splitlines(), start=1):
        for pattern, label in FORBIDDEN_TOKENS:
            if pattern.search(line):
                problems.append(f"  {rel}:{lineno}: {label} — {line.strip()[:70]}")
    return problems


def check_hygiene_source() -> int:
    """Source layer: reject forbidden tokens in project `.lean` files."""
    problems: list[str] = []
    files = project_lean_files()
    if not files:
        print("ERROR: no project .lean files found under recursion-topology-fv/", file=sys.stderr)
        return 1
    for path in files:
        problems.extend(source_problems(path, path.read_text(encoding="utf-8")))
    if problems:
        print(f"FAIL: {len(problems)} forbidden token(s) in project source (I4):",
              file=sys.stderr)
        for p in problems:
            print(p, file=sys.stderr)
        return 1
    print(f"OK: no forbidden tokens in {len(files)} project source file(s).")
    return 0


def self_test() -> int:
    """Regression checks for the hygiene gate's easy-to-break plumbing."""
    failures: list[str] = []
    sample = """-- sorry axiom
/- outer sorryAx /- nested admit -/ native_decide -/
def harmless := "sorry axiom sorryAx admit native_decide"
theorem bad : True := by
  sorry
"""
    labels = [p.split(": ", 1)[1].split(" —", 1)[0]
              for p in source_problems(LEAN_ROOT, sample)]
    if labels != ["sorry"]:
        failures.append(f"lexer expected only code `sorry`, got {labels}")
    stripped = _strip_lean_noncode(sample)
    if len(stripped.splitlines()) != len(sample.splitlines()):
        failures.append("lexer did not preserve source line count")

    direct = "example : True := by\n  exact sorryAx True true\n"
    direct_labels = [p.split(": ", 1)[1].split(" —", 1)[0]
                     for p in source_problems(LEAN_ROOT, direct)]
    if direct_labels != ["direct sorryAx use"]:
        failures.append(f"direct sorryAx was not detected: {direct_labels}")

    forbidden_code = """axiom bad : False
example : True := by admit
example : True := by native_decide
"""
    forbidden_labels = [p.split(": ", 1)[1].split(" —", 1)[0]
                        for p in source_problems(LEAN_ROOT, forbidden_code)]
    expected_forbidden = ["axiom declaration", "admit", "native_decide"]
    if forbidden_labels != expected_forbidden:
        failures.append(
            f"forbidden code expected {expected_forbidden}, got {forbidden_labels}"
        )

    escaped_string = 'def harmlessEscaped := "quote: \\"; sorry axiom sorryAx admit native_decide"\n'
    escaped_labels = source_problems(LEAN_ROOT, escaped_string)
    if escaped_labels:
        failures.append(f"escaped string produced false positives: {escaped_labels}")

    files = project_lean_files()
    if LEAN_ROOT not in files:
        failures.append("umbrella recursion-topology-fv.lean is absent from project enumeration")
    names = [module_name(path) for path in files]
    if len(names) != len(set(names)):
        failures.append("project source enumeration produced duplicate module names")
    # The umbrella plus one module from each layer of the
    # Preliminaries -> Specification -> VMs tree, to catch a glob that stops
    # recursing into subdirectories.
    expected_modules = [
        "«recursion-topology-fv»",
        "«recursion-topology-fv».Preliminaries.ArgumentSystem",
        "«recursion-topology-fv».Specification.Cte",
        "«recursion-topology-fv».VMs.TwoStep.TwoStep",
    ]
    missing = [m for m in expected_modules if m not in names]
    if missing:
        failures.append(f"expected modules missing from enumeration: {missing}")

    if failures:
        print(f"FAIL: {len(failures)} CI self-test(s):", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print("OK: CI hygiene lexer and project-module enumeration self-tests pass.")
    return 0


def _fail(msg: str, res: subprocess.CompletedProcess) -> int:
    print(msg, file=sys.stderr)
    print(res.stdout, file=sys.stderr)
    print(res.stderr, file=sys.stderr)
    return 1


def run_lean(body: str) -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", dir=REPO, delete=False, encoding="utf-8"
    ) as f:
        f.write(body)
        path = Path(f.name)
    try:
        return subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    finally:
        path.unlink(missing_ok=True)


def build_project_modules(modules: list[str]) -> subprocess.CompletedProcess:
    """Build every discovered module, including files outside the default target."""
    return subprocess.run(
        ["lake", "build", *(f"+{module}" for module in modules)],
        cwd=REPO,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def eval_axioms(out: str) -> int:
    bad = False
    if "sorryAx" in out:
        print("FAIL: a headline theorem depends on sorryAx.", file=sys.stderr)
        bad = True
    for used in re.findall(r"depends on axioms: \[([^\]]*)\]", out):
        for ax in (a.strip() for a in used.split(",") if a.strip()):
            if ax not in PERMITTED_AXIOMS:
                print(f"FAIL: disallowed axiom '{ax}'.", file=sys.stderr)
                bad = True
    if bad:
        return 1
    print(f"OK: headline theorems use only {sorted(PERMITTED_AXIOMS)}.")
    return 0


def main() -> int:
    # Module names and Lean output contain unicode (`«…»`); keep printing them
    # from crashing on a non-UTF-8 console (e.g. Windows cp1252).
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--check-axioms", action="store_true")
    ap.add_argument("--check-hygiene", action="store_true")
    args = ap.parse_args()
    if not (args.self_test or args.check_axioms or args.check_hygiene):
        ap.error("pass --self-test, --check-axioms and/or --check-hygiene")

    rc_test = self_test() if args.self_test else 0
    rc_src = check_hygiene_source() if args.check_hygiene else 0

    files = project_lean_files()
    try:
        modules = [module_name(path) for path in files]
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    if args.check_hygiene:
        print(f"Building all {len(modules)} discovered project module(s).")
        built = build_project_modules(modules)
        if built.returncode != 0:
            return _fail("FAIL: a discovered project module did not compile.", built)

    body = "".join(f"import {module}\n" for module in modules)
    if args.check_axioms:
        body += "".join(f"#print axioms {t}\n" for t in HEADLINE_THEOREMS)
    if args.check_hygiene:
        body += LEAN_HYGIENE

    if not (args.check_axioms or args.check_hygiene):
        return rc_test

    res = run_lean(body)
    # A non-zero exit means either an elaboration error (a renamed or removed
    # headline theorem) or the hygiene metaprogram's `throwError`. Both checks
    # share this single compile, so distinguish by the marker it prints.
    if res.returncode != 0:
        combined = res.stdout + res.stderr
        why = ("FAIL: repo-wide axiom/sorry hygiene violation (I4)."
               if "hygiene violation" in combined
               else "FAIL: a headline theorem did not elaborate.")
        return _fail(why, res)

    rc = rc_test | rc_src
    if args.check_axioms:
        print(res.stdout.strip())
        rc |= eval_axioms(res.stdout)
    elif args.check_hygiene:
        print(res.stdout.strip())
    return rc


if __name__ == "__main__":
    sys.exit(main())
