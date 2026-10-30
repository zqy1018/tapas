#!/usr/bin/env python3
"""Restore pinned upstream Lean sources and apply the recorded module-system patches."""

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from urllib.request import urlopen


UPSTREAM = Path(__file__).resolve().parent / "Upstream"
SOURCES = [("SOURCES.json", "PORT.patch"), ("SOURCES-addsub.json", "PORT-addsub.patch")]


def check_hash(data, expected, label):
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"SHA-256 mismatch: {label}")


def ensure_upstream():
    for manifest_name, patch_name in SOURCES:
        manifest = json.loads((UPSTREAM / manifest_name).read_text())
        files = [entry for entry in manifest["files"] if "local_file" in entry]
        missing = []
        # Check existing files before downloading; never overwrite local edits.
        for entry in files:
            target = UPSTREAM / entry["local_file"]
            if target.exists():
                check_hash(target.read_bytes(), entry["ported_sha256"], target)
            else:
                missing.append(entry)
        if not missing:
            continue

        # Stage the complete source batch because its patch covers all files together.
        with tempfile.TemporaryDirectory(prefix="tapas-upstream-") as temporary:
            staging = Path(temporary)
            for entry in files:
                url = f"https://raw.githubusercontent.com/leanprover/lean4/{manifest['commit']}/{entry['path']}"
                with urlopen(url, timeout=20) as response:
                    data = response.read()
                check_hash(data, entry["sha256"], url)
                (staging / entry["local_file"]).write_bytes(data)
            result = subprocess.run(
                ["patch", "--batch", "--fuzz=0", "-p0", "-i", str(UPSTREAM / patch_name)],
                cwd=staging, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(f"{patch_name} failed:\n{result.stdout}{result.stderr}")
            for entry in files:
                check_hash((staging / entry["local_file"]).read_bytes(),
                           entry["ported_sha256"], entry["local_file"])
            for entry in missing:
                # Exclusive creation also protects files created by another concurrent run.
                with (UPSTREAM / entry["local_file"]).open("xb") as target:
                    target.write((staging / entry["local_file"]).read_bytes())
        print(f"Restored {len(missing)} upstream Lean files from {manifest['commit']}.")


if __name__ == "__main__":
    ensure_upstream()
