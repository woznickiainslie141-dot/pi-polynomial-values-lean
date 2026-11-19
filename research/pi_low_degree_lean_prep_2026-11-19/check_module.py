"""Use the project's bounded Lean runner with the manifest's existing local checkouts."""
import json
from pathlib import Path
import subprocess
import sys


WORKSPACE = Path(__file__).resolve().parents[2]
PROJECT = WORKSPACE / "formalization" / "OddPiPowers"
OVERRIDES = PROJECT / ".lake" / "package-overrides.json"


def git(directory, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(directory), *args], text=True
    ).strip()


def cached_packages():
    manifest = json.loads((PROJECT / "lake-manifest.json").read_bytes())
    entries = []
    for pin in manifest["packages"]:
        if pin["type"] != "git" or pin.get("subDir"):
            raise ValueError(f"Unsupported local package entry: {pin['name']}")
        relative = Path(manifest["packagesDir"]) / pin["name"]
        directory = PROJECT / relative
        revision = pin["rev"]
        if git(directory, "rev-parse", "HEAD") != revision or git(directory, "cat-file", "-t", revision) != "commit":
            raise ValueError(f"Local revision mismatch: {pin['name']}")
        if git(directory, "status", "--short", "--untracked-files=no"):
            raise ValueError(f"Tracked files differ from the pinned checkout: {pin['name']}")
        entry = {k: pin[k] for k in ("name", "scope", "configFile", "manifestFile", "inherited")}
        entries.append(dict(entry, type="path", dir=relative.as_posix(), copy=False))
    return (json.dumps(dict(version=manifest["version"], packages=entries)) + "\n").encode()


def main():
    if not sys.argv[1:]:
        raise SystemExit("Pass the source, timeout and log arguments to bounded_lean.py.")
    # The project owns the single compiler slot. All Git checks precede the trial.
    sys.path.insert(0, str(WORKSPACE / "scripts"))
    from bounded_lean import other_compilers
    if other_compilers():
        raise RuntimeError("A Lean or Lake process is already running.")
    packages = cached_packages()
    # Exclusive creation preserves any pre-existing user configuration.
    with OVERRIDES.open("xb") as handle:
        handle.write(packages)
    try:
        runner = WORKSPACE / "scripts" / "bounded_lean.py"
        return subprocess.run([sys.executable, str(runner), *sys.argv[1:]], cwd=WORKSPACE).returncode
    finally:
        if OVERRIDES.read_bytes() != packages:
            raise RuntimeError("Local package selection changed during this trial; preserved it.")
        OVERRIDES.unlink()


if __name__ == "__main__":
    sys.exit(main())
