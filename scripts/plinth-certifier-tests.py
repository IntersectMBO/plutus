#!/usr/bin/env python3

"""Plinth certifier test pipeline — subcommand-based interface.

Certificate folders use stable names (<pkg>_<module>_<loc>.agda-cert) so
rebuilding overwrites in-place rather than creating new timestamped folders.
The user controls what gets rebuilt via normal cabal incremental compilation
(or cabal clean + cabal build when a full rebuild is needed).

Usage: plinth-certifier-tests.py <command> [options]

Commands:
    build   — Generate Agda certificates via cabal build with certify plugin option
    check   — Run Agda type-checking on generated certificates
    status  — Show summary of current certificate state (read-only)
    clean   — Remove certificate directories
    run     — Full pipeline: build then check
"""

from __future__ import annotations

import argparse
import fnmatch
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def repo_root() -> Path:
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True,
    )
    return Path(result.stdout.strip())


REPO_ROOT = repo_root()
DEFAULT_CERT_DIR = REPO_ROOT / "agda-certificates"
DEFAULT_PATTERN = "*.agda-cert"

AGDA_PASS_LOG = "agda-check-PASS.log"
AGDA_FAIL_LOG = "agda-check-FAIL.log"


def die(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def agda_log_file(d: Path) -> Path | None:
    """Return the agda check log if one exists (PASS or FAIL)."""
    p = d / AGDA_PASS_LOG
    if p.exists():
        return p
    f = d / AGDA_FAIL_LOG
    if f.exists():
        return f
    return None


def remove_agda_logs(d: Path) -> None:
    """Remove any existing agda check logs."""
    for name in (AGDA_PASS_LOG, AGDA_FAIL_LOG):
        f = d / name
        if f.exists():
            f.unlink()


# ---------------------------------------------------------------------------
# Certificate inspection
# ---------------------------------------------------------------------------

@dataclass
class CertStatus:
    """Status of a single certificate directory."""
    name: str
    path: Path
    certifier: str = "?"       # PASS | FAIL | NO-RESULT
    agda: str = "PENDING"      # PASS | FAIL | SKIP | PENDING | STALE
    fail_reason: str = ""


def inspect_cert(d: Path) -> CertStatus:
    """Read the status files in a certificate directory."""
    s = CertStatus(name=d.name, path=d)
    pass_file = d / "plinth-certifier-PASS.txt"
    fail_file = d / "plinth-certifier-FAIL.txt"

    if pass_file.exists():
        s.certifier = "PASS"
    elif fail_file.exists():
        s.certifier = "FAIL"
        lines = fail_file.read_text().splitlines()[:5]
        s.fail_reason = "\n".join(lines)
    else:
        s.certifier = "NO-RESULT"

    # Determine Agda status
    if s.certifier != "PASS":
        # Certifier didn't pass — Agda check is skipped
        s.agda = "SKIP"
    elif (d / AGDA_PASS_LOG).exists():
        log = d / AGDA_PASS_LOG
        if pass_file.stat().st_mtime > log.stat().st_mtime:
            s.agda = "STALE"
        else:
            s.agda = "PASS"
    elif (d / AGDA_FAIL_LOG).exists():
        log = d / AGDA_FAIL_LOG
        if pass_file.stat().st_mtime > log.stat().st_mtime:
            s.agda = "STALE"
        else:
            s.agda = "FAIL"
    else:
        s.agda = "PENDING"

    return s


def is_uptodate(d: Path) -> bool:
    """True if an agda check log exists and is at least as new as plinth-certifier-PASS.txt."""
    log = agda_log_file(d)
    pass_f = d / "plinth-certifier-PASS.txt"
    return (
        log is not None
        and pass_f.exists()
        and pass_f.stat().st_mtime <= log.stat().st_mtime
    )


def list_cert_dirs(cert_dir: Path, pattern: str) -> list[Path]:
    """Return sorted list of certificate directories matching pattern."""
    if not cert_dir.is_dir():
        return []
    dirs = []
    for d in sorted(cert_dir.iterdir()):
        if d.is_dir() and fnmatch.fnmatch(d.name, pattern):
            dirs.append(d)
    return dirs


# ---------------------------------------------------------------------------
# cmd_build
# ---------------------------------------------------------------------------

def cmd_build(args: argparse.Namespace) -> int:
    cert_dir = args.output.resolve()
    targets = args.targets or ["all"]

    print("=== build ===")
    print(f"Targets   : {' '.join(targets)}")
    print(f"Output    : {cert_dir}")
    print(f"Clean     : {args.clean}")
    print()

    if args.clean:
        print("--- cabal clean ---")
        subprocess.run(["cabal", "clean"])
        if cert_dir.exists():
            print(f"--- removing {cert_dir} ---")
            shutil.rmtree(cert_dir)
        print()

    cert_dir.mkdir(parents=True, exist_ok=True)

    print("--- cabal update ---")
    update = subprocess.run(["cabal", "update"])
    if update.returncode != 0:
        die(f"cabal update failed (exit code {update.returncode})")
    print()

    print(f"--- cabal build {' '.join(targets)} ---")
    result = subprocess.run(
        ["cabal", "build", *targets,
         f"--ghc-options=\"-fplugin-opt=Plinth.Plugin:certify={cert_dir}\""],
    )

    if result.returncode != 0:
        die(f"cabal build failed (exit code {result.returncode})")
    print()
    return result.returncode


# ---------------------------------------------------------------------------
# cmd_check
# ---------------------------------------------------------------------------

def _check_one(cert_dir: Path) -> tuple[str, str, str]:
    """Check a single certificate. Returns (status, name, detail).

    Runs in a subprocess worker so must be self-contained.
    """
    print(f"Checking: {cert_dir.name}")
    name = cert_dir.name
    pass_file = cert_dir / "plinth-certifier-PASS.txt"
    fail_file = cert_dir / "plinth-certifier-FAIL.txt"

    # Check certifier result
    if pass_file.exists():
        pass  # proceed to Agda
    elif fail_file.exists():
        return ("SKIP", name, "certifier failed")
    else:
        return ("SKIP", name, "no plinth-certifier result file")

    # Find .agda-lib
    agda_libs = list(cert_dir.glob("*.agda-lib"))
    if not agda_libs:
        return ("SKIP", name, "no .agda-lib found")

    agda_lib = agda_libs[0]
    cert_name = None
    for line in agda_lib.read_text().splitlines():
        m = re.match(r"^name:\s*(.+)$", line)
        if m:
            cert_name = m.group(1).strip()
            break

    if not cert_name:
        return ("SKIP", name, "could not parse name from .agda-lib")

    main_agda = cert_dir / "src" / f"{cert_name}.agda"
    if not main_agda.exists():
        return ("SKIP", name, f"main module not found: src/{cert_name}.agda")

    # Remove old logs before running
    for old_log in ("agda-check-PASS.log", "agda-check-FAIL.log"):
        f = cert_dir / old_log
        if f.exists():
            f.unlink()

    # Run Agda
    result = subprocess.run(
        ["agda-with-stdlib-and-metatheory", f"src/{cert_name}.agda"],
        cwd=cert_dir,
        capture_output=True, text=True,
    )
    output = result.stdout + result.stderr

    if result.returncode == 0:
        (cert_dir / "agda-check-PASS.log").write_text(output)
        return ("PASS", name, "")
    else:
        (cert_dir / "agda-check-FAIL.log").write_text(output)
        return ("FAIL", name, f"exit code {result.returncode}")


def cmd_check(args: argparse.Namespace) -> int:
    cert_dir = args.output.resolve()
    pattern = args.pattern
    jobs = args.jobs
    force = args.force

    print("=== check ===")
    print(f"Certificate dir : {cert_dir}")
    print(f"Filter pattern  : {pattern}")
    print(f"Parallel jobs   : {jobs}")
    print(f"Force re-check  : {force}")
    print()

    if not cert_dir.is_dir():
        die(f"certificate directory does not exist: {cert_dir}")

    all_dirs = list_cert_dirs(cert_dir, pattern)
    skipped_uptodate = 0
    dirs_to_check: list[Path] = []

    for d in all_dirs:
        if not force and is_uptodate(d):
            skipped_uptodate += 1
        else:
            if force:
                build_dir = d / "_build"
                if build_dir.is_dir():
                    shutil.rmtree(build_dir)
            dirs_to_check.append(d)

    if skipped_uptodate > 0:
        print(f"Skipped {skipped_uptodate} already-checked certificates (use --force to re-check)")
        print()

    if not dirs_to_check:
        print("No certificate directories to check.")
        print()
        return 0

    print(f"Certificates to check: {len(dirs_to_check)}")
    print()

    # Run checks
    results: list[tuple[str, str, str]] = []
    with ProcessPoolExecutor(max_workers=jobs) as executor:
        futures = {executor.submit(_check_one, d): d for d in dirs_to_check}
        for future in as_completed(futures):
            status, name, detail = future.result()
            results.append((status, name, detail))
            if detail:
                print(f"{status}: {name} ({detail})", file=sys.stderr)
            else:
                print(f"{status}: {name}", file=sys.stderr)

    # Sort results by name for deterministic output
    results.sort(key=lambda r: r[1])

    # Tally
    pass_list = [r[1] for r in results if r[0] == "PASS"]
    fail_list = [r[1] for r in results if r[0] == "FAIL"]
    skip_list = [r[1] for r in results if r[0] == "SKIP"]
    total = len(results)

    # Write summary
    results_file = cert_dir / "__results__.txt"
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    lines = [
        "=== Plinth Certifier Test Results ===",
        f"Date: {now}",
        f"Certificate dir: {cert_dir}",
        f"Filter pattern : {pattern}",
        "",
        f"Total  : {total}",
        f"Passed : {len(pass_list)}",
        f"Failed : {len(fail_list)}",
        f"Skipped: {len(skip_list)}",
    ]
    if skipped_uptodate > 0:
        lines.append(f"Up-to-date (not re-checked): {skipped_uptodate}")
    lines.append("")

    if pass_list:
        lines.append("--- Passed ---")
        lines.extend(f"  PASS: {p}" for p in pass_list)
        lines.append("")

    if fail_list:
        lines.append("--- Failed ---")
        lines.extend(f"  FAIL: {f}" for f in fail_list)
        lines.append("")

    if skip_list:
        lines.append("--- Skipped ---")
        lines.extend(f"  SKIP: {s}" for s in skip_list)
        lines.append("")

    summary = "\n".join(lines)
    print()
    print(summary)
    results_file.write_text(summary + "\n")
    print(f"Results written to: {results_file}")
    print()

    return 1 if fail_list else 0


# ---------------------------------------------------------------------------
# cmd_status
# ---------------------------------------------------------------------------

def cmd_status(args: argparse.Namespace) -> int:
    cert_dir = args.output.resolve()
    pattern = args.pattern

    if not cert_dir.is_dir():
        print(f"No certificate directory found at: {cert_dir}")
        return 0

    dirs = list_cert_dirs(cert_dir, pattern)
    counts: dict[str, int] = {
        "cert_PASS": 0, "cert_FAIL": 0, "cert_NO-RESULT": 0,
        "agda_PASS": 0, "agda_FAIL": 0, "agda_SKIP": 0,
        "agda_PENDING": 0, "agda_STALE": 0,
    }

    for d in dirs:
        s = inspect_cert(d)
        counts[f"cert_{s.certifier}"] += 1
        counts[f"agda_{s.agda}"] += 1
        # Skip fully-passing certificates (both certifier and agda PASS)
        if s.certifier == "PASS" and s.agda == "PASS":
            continue
        print(f"  {s.certifier:<12s} {s.agda:<10s} {s.name}")

    print()
    print("=== Status Summary ===")
    print(f"Total certificates : {len(dirs)}")
    print()
    print(f"Certifier PASS     : {counts['cert_PASS']}")
    print(f"Certifier FAIL     : {counts['cert_FAIL']}")
    print(f"No result file     : {counts['cert_NO-RESULT']}")
    print()
    print(f"Agda PASS          : {counts['agda_PASS']}")
    print(f"Agda FAIL          : {counts['agda_FAIL']}")
    print(f"Agda SKIP          : {counts['agda_SKIP']}")
    print(f"Agda PENDING       : {counts['agda_PENDING']}")
    print(f"Agda STALE         : {counts['agda_STALE']}")
    return 0


# ---------------------------------------------------------------------------
# cmd_clean
# ---------------------------------------------------------------------------

def cmd_clean(args: argparse.Namespace) -> int:
    cert_dir = args.output.resolve()
    pattern = args.pattern

    if not cert_dir.is_dir():
        print(f"Nothing to clean: {cert_dir} does not exist.")
        return 0

    if pattern == DEFAULT_PATTERN:
        print(f"Removing entire certificate directory: {cert_dir}")
        shutil.rmtree(cert_dir)
    else:
        dirs = list_cert_dirs(cert_dir, pattern)
        for d in dirs:
            print(f"Removing: {d.name}")
            shutil.rmtree(d)
        print(f"Removed {len(dirs)} certificate directories.")
    return 0


# ---------------------------------------------------------------------------
# cmd_run
# ---------------------------------------------------------------------------

def cmd_run(args: argparse.Namespace) -> int:
    # Build phase
    build_ns = argparse.Namespace(
        output=args.output,
        clean=args.clean,
        targets=args.targets,
    )
    # cmd_build aborts the script (via die) if cabal update or cabal build fails
    cmd_build(build_ns)

    # Check phase
    check_ns = argparse.Namespace(
        output=args.output,
        pattern=DEFAULT_PATTERN,
        jobs=args.jobs,
        force=args.force,
    )
    return cmd_check(check_ns)


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="plinth-certifier-tests.py",
        description="Plinth certifier test pipeline",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # -- build --
    p_build = sub.add_parser("build", help="Generate Agda certificates (cabal build with certify)")
    p_build.add_argument("--clean", action="store_true", help="Run cabal clean before building")
    p_build.add_argument("-o", "--output", type=Path, default=DEFAULT_CERT_DIR,
                         help="Certificate output directory")
    p_build.add_argument("targets", nargs="*", help="Cabal targets (default: all)")

    # -- check --
    p_check = sub.add_parser("check", help="Run Agda type-checking on certificates")
    p_check.add_argument("-j", "--jobs", type=int, default=1,
                         help="Parallel Agda processes (default: 1)")
    p_check.add_argument("--force", action="store_true",
                         help="Re-check all certificates, even those already checked. "
                              "Also deletes Agda _build directories to force a clean rebuild.")
    p_check.add_argument("-o", "--output", type=Path, default=DEFAULT_CERT_DIR,
                         help="Certificate directory to scan")
    p_check.add_argument("pattern", nargs="?", default=DEFAULT_PATTERN,
                         help="Glob pattern to filter certificate directories")

    # -- status --
    p_status = sub.add_parser("status", help="Show summary of current certificates (read-only)")
    p_status.add_argument("-o", "--output", type=Path, default=DEFAULT_CERT_DIR,
                          help="Certificate directory to scan")
    p_status.add_argument("pattern", nargs="?", default=DEFAULT_PATTERN,
                          help="Glob pattern to filter certificate directories")

    # -- clean --
    p_clean = sub.add_parser("clean", help="Remove certificate directories")
    p_clean.add_argument("-o", "--output", type=Path, default=DEFAULT_CERT_DIR,
                         help="Certificate directory")
    p_clean.add_argument("pattern", nargs="?", default=DEFAULT_PATTERN,
                         help="Glob pattern to filter which directories to remove")

    # -- run --
    p_run = sub.add_parser("run", help="Full pipeline (build + check)")
    p_run.add_argument("--clean", action="store_true", help="Run cabal clean before building")
    p_run.add_argument("-j", "--jobs", type=int, default=8,
                       help="Parallel Agda processes (default: 8)")
    p_run.add_argument("--force", action="store_true",
                       help="Re-check all certificates, even those already checked. "
                            "Also deletes Agda _build directories to force a clean rebuild.")
    p_run.add_argument("-o", "--output", type=Path, default=DEFAULT_CERT_DIR,
                       help="Certificate output directory")
    p_run.add_argument("targets", nargs="*", help="Cabal targets (default: all)")

    return parser


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    parser = make_parser()
    args = parser.parse_args()

    dispatch = {
        "build": cmd_build,
        "check": cmd_check,
        "status": cmd_status,
        "clean": cmd_clean,
        "run": cmd_run,
    }

    rc = dispatch[args.command](args)
    sys.exit(rc)


if __name__ == "__main__":
    main()
