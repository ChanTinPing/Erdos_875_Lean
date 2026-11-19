"""Build the pinned public progression theorem and verify the two JSP-000726 endpoints."""

import argparse
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

PIN = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
UPSTREAM = "https://github.com/plby/lean-proofs.git"
IMPORT = re.compile(r"^(?:(?:public|private|meta) )*import (?:all )?([\w.]+)$", re.MULTILINE)
PROOF_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = ("Jsp000726.erdos_875", "Jsp000726.erdos_875_eventual")


def ensure_checkout(replay_directory):
    checkout = replay_directory / "plby"
    if not checkout.exists():
        subprocess.run(["git", "init", "--quiet", str(checkout)], check=True)
        subprocess.run(["git", "-C", str(checkout), "remote", "add", "origin", UPSTREAM], check=True)
        subprocess.run(["git", "-C", str(checkout), "config", "core.autocrlf", "false"], check=True)
    command = ["git", "-C", str(checkout)]
    current = subprocess.run(
        [*command, "rev-parse", "--verify", "HEAD"], check=False, text=True, capture_output=True
    )
    if current.stdout.strip() != PIN:
        subprocess.run([*command, "fetch", "--depth", "1", "origin", PIN], check=True)
        subprocess.run([*command, "checkout", "--detach", PIN], check=True)
    subprocess.run([*command, "diff", "--quiet", "HEAD", "--"], check=True)
    return checkout


def set_up_sources(bundle, replay_directory, checkout):
    for name in ("Jsp000726PinnedStructure.lean", "Jsp000726Verified.lean"):
        shutil.copy2(bundle / name, replay_directory / name)
    subprocess.run(
        [
            sys.executable,
            str(bundle / "prepare_replay.py"),
            "--checkout",
            str(checkout),
            "--output",
            str(replay_directory / "replay-src"),
            "--order",
            str(replay_directory / "replay-order.txt"),
        ],
        env={**os.environ, "PYTHONUTF8": "1"},
        check=True,
    )


def run_lean(command, directory, environment, log, rss_limit):
    with log.open("w", encoding="utf-8") as output, subprocess.Popen(
        command, cwd=directory, env=environment, stdout=output, stderr=output
    ) as process:
        if rss_limit is not None:
            status = Path("/proc") / str(process.pid) / "status"
            while process.poll() is None:
                try:
                    rss = next(
                        line for line in status.read_text().splitlines() if line.startswith("VmRSS:")
                    )
                except (FileNotFoundError, StopIteration):
                    time.sleep(0.025)
                    continue
                if int(rss.split()[1]) > rss_limit * 1024:
                    print(f"Lean exceeded {rss_limit} MiB RSS.", file=output, flush=True)
                    process.kill()
                    break
                time.sleep(0.025)
        code = process.wait()
    if code:
        print(log.read_text(encoding="utf-8", errors="replace")[-12000:], file=sys.stderr)
        raise RuntimeError(f"Lean failed. See {log}")


def compile_upstream(lean, replay_directory, environment, rss_limit):
    source = replay_directory / "replay-src"
    output = replay_directory / "replay-oleans"
    logs = replay_directory / "replay-logs"
    logs.mkdir(exist_ok=True)
    modules = (replay_directory / "replay-order.txt").read_text().splitlines()
    local_modules = set(modules)
    for index, module in enumerate(modules, 1):
        relative = Path(*module.split("."))
        source_file = (source / relative).with_suffix(".lean")
        olean = (output / relative).with_suffix(".olean")
        dependencies = [
            (output / Path(*name.split("."))).with_suffix(".olean")
            for name in IMPORT.findall(source_file.read_text(encoding="utf-8"))
            if name in local_modules
        ]
        latest_input = max(path.stat().st_mtime_ns for path in [source_file, *dependencies])
        if olean.exists() and olean.stat().st_mtime_ns >= latest_input:
            continue
        print(f"[{index}/{len(modules)}] {module}", flush=True)
        olean.parent.mkdir(parents=True, exist_ok=True)
        try:
            run_lean(
                [lean, "-j", "1", "--root", str(source), "-o", str(olean), str(source_file)],
                source,
                environment,
                logs / f"{module}.log",
                rss_limit,
            )
        except RuntimeError:
            olean.unlink(missing_ok=True)
            raise


def verify_endpoints(lean, replay_directory, environment, rss_limit):
    log = replay_directory / "replay-logs" / "jsp000726-final.log"
    adapter = replay_directory / "Jsp000726PinnedStructure.lean"
    adapter_output = replay_directory / "replay-oleans" / "Jsp000726PinnedStructure.olean"
    run_lean(
        [lean, "-j", "1", "-o", str(adapter_output), str(adapter)],
        replay_directory,
        environment,
        log.with_name("jsp000726-pinned-input.log"),
        rss_limit,
    )
    source_file = replay_directory / "Jsp000726Verified.lean"
    run_lean([lean, "-j", "1", str(source_file)], replay_directory, environment, log, rss_limit)
    content = log.read_text(encoding="utf-8", errors="replace")
    print(content, end="")
    for theorem in TARGETS:
        match = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]*)\]", content)
        if not match or not set(match.group(1).split(", ")).issubset(PROOF_AXIOMS):
            raise RuntimeError(f"Unexpected axiom audit for {theorem}. See {log}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rss-limit-mib", type=int)
    args = parser.parse_args()
    if args.rss_limit_mib is not None and (args.rss_limit_mib < 1 or not Path("/proc/self").exists()):
        parser.error("--rss-limit-mib requires Linux and a positive limit")
    lean = shutil.which("lean")
    if lean is None or "LEAN_PATH" not in os.environ:
        parser.error("Run this program through 'lake env' after building the project")
    bundle = Path(__file__).resolve().parent
    project = bundle.parent
    replay_directory = project / ".lake" / "public-structure"
    replay_directory.mkdir(parents=True, exist_ok=True)
    checkout = ensure_checkout(replay_directory)
    set_up_sources(bundle, replay_directory, checkout)
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "1"
    environment["LEAN_PATH"] = os.pathsep.join(
        [str(replay_directory / "replay-oleans"), environment["LEAN_PATH"]]
    )
    compile_upstream(lean, replay_directory, environment, args.rss_limit_mib)
    verify_endpoints(lean, replay_directory, environment, args.rss_limit_mib)


if __name__ == "__main__":
    main()
